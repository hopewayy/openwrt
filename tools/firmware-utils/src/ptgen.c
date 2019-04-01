/*
 * ptgen - partition table generator
 * Copyright (C) 2006 by Felix Fietkau <nbd@nbd.name>
 *
 * uses parts of afdisk
 * Copyright (C) 2002 by David Roetzel <david@roetzel.de>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 */

#include <sys/types.h>
#include <sys/stat.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <ctype.h>
#include <fcntl.h>
#include <stdint.h>
#include <linux/uuid.h>
#include "cyg_crc.h"

#if __BYTE_ORDER == __BIG_ENDIAN
#define cpu_to_le32(x) __bswap_32(x)
#define cpu_to_le64(x) __bswap_64(x)
#elif __BYTE_ORDER == __LITTLE_ENDIAN
#define cpu_to_le32(x) (x)
#define cpu_to_le64(x) (x)
#else
#error unknown endianness!
#endif

#ifndef GUID_INIT
typedef uuid_le guid_t;
#define GUID_INIT(a, b, c, d0, d1, d2, d3, d4, d5, d6, d7)      \
	UUID_LE(a, b, c, d0, d1, d2, d3, d4, d5, d6, d7)
#endif

#define GPT_SIGNATURE 0x5452415020494645ULL
#define GPT_REVISION 0x00010000

#define GPT_PARTITION_ESP \
	GUID_INIT( 0xC12A7328, 0xF81F, 0x11d2, \
			0xBA, 0x4B, 0x00, 0xA0, 0xC9, 0x3E, 0xC9, 0x3B)

#define GPT_PARTITION_DATA \
	GUID_INIT( 0xEBD0A0A2, 0xB9E5, 0x4433, \
			0x87, 0xC0, 0x68, 0xB6, 0xB7, 0x26, 0x99, 0xC7)

#define GPT_PARTITION_BIOS \
	GUID_INIT( 0x21686148, 0x6449, 0x6E6F, \
			0x74, 0x4E, 0x65, 0x65, 0x64, 0x45, 0x46, 0x49)

#define GPT_HEADER_SIZE         92
#define GPT_ENTRY_SIZE          128
#define GPT_ENTRY_NUM           128


/* Partition table entry */
struct pte {
	uint8_t active;
	uint8_t chs_start[3];
	uint8_t type;
	uint8_t chs_end[3];
	uint32_t start;
	uint32_t length;
};

struct partinfo {
	unsigned long size;
	int type;
};

/* GPT Partition table header */
struct gpth {
	uint64_t signature;
	uint32_t revision;
	uint32_t size;
	uint32_t crc32;
	uint32_t reserved;
	uint64_t self;
	uint64_t alternate;
	uint64_t first_usable;
	uint64_t last_usable;
	guid_t disk_guid;
	uint64_t first_entry;
	uint32_t entry_num;
	uint32_t entry_size;
	uint32_t entry_crc32;
} __attribute__((packed));

/* GPT Partition table entry */
struct gpte {
	guid_t type;
	guid_t guid;
	uint64_t start;
	uint64_t end;
	uint64_t attr;
	uint16_t name[72 / sizeof(uint16_t)];
} __attribute__((packed));


int verbose = 0;
int active = 1;
int heads = -1;
int sectors = -1;
int kb_align = 0;
bool ignore_null_sized_partition = false;
bool use_guid_partition_table = false;
struct partinfo parts[GPT_ENTRY_NUM];
char *filename = NULL;


/*
 * parse the size argument, which is either
 * a simple number (K assumed) or
 * K, M or G
 *
 * returns the size in KByte
 */
static long to_kbytes(const char *string)
{
	int exp = 0;
	long result;
	char *end;

	result = strtoul(string, &end, 0);
	switch (tolower(*end)) {
		case 'k' :
		case '\0' : exp = 0; break;
		case 'm' : exp = 1; break;
		case 'g' : exp = 2; break;
		default: return 0;
	}

	if (*end)
		end++;

	if (*end) {
		fprintf(stderr, "garbage after end of number\n");
		return 0;
	}

	/* result: number + 1024^(exp) */
	if (exp == 0)
		return result;
	return result * (2 << ((10 * exp) - 1));
}

/* convert the sector number into a CHS value for the partition table */
static void to_chs(long sect, unsigned char chs[3])
{
	int c,h,s;

	s = (sect % sectors) + 1;
	sect = sect / sectors;
	h = sect % heads;
	sect = sect / heads;
	c = sect;

	chs[0] = h;
	chs[1] = s | ((c >> 2) & 0xC0);
	chs[2] = c & 0xFF;

	return;
}

/* round the sector number up to the next cylinder */
static inline unsigned long round_to_cyl(long sect)
{
	int cyl_size = heads * sectors;

	return sect + cyl_size - (sect % cyl_size);
}

/* round the sector number up to the kb_align boundary */
static inline unsigned long round_to_kb(long sect) {
        return ((sect - 1) / kb_align + 1) * kb_align;
}

/* Compute a CRC for guid partition table */
static inline unsigned long gpt_crc32(void *buf, unsigned long len)
{
	return cyg_crc32_accumulate(~0L, buf, len) ^ ~0L;
}

/* Parse a guid string to guid_t struct */
static inline int guid_parse(char *buf, guid_t *guid)
{
	char b[4] = {0};
	char *p = buf;
	int i = 0;
	if (strnlen(buf, 36) != 36)
		return -1;
	for (i = 0; i < 16; i++) {
		if (*p == '-')
			p ++;
		if (*p == '\0')
			return -1;
		memcpy(b, p, 2);
		guid->b[i] = strtol(b, 0, 16);
		p += 2;
	}
	*((uint32_t *)guid->b) = __bswap_32(*((uint32_t *)guid->b));
	*((uint16_t *)(guid->b+4)) = __bswap_16(*((uint16_t *)(guid->b+4)));
	*((uint16_t *)(guid->b+6)) = __bswap_16(*((uint16_t *)(guid->b+6)));
	return 0;
}

/* print a guid_t struct  */
static inline void guid_print(guid_t *guid)
{
	printf("%02X%02X%02X%02X-%02X%02X-%02X%02X-%02X%02X-%02X%02X%02X%02X%02X%02X\n",
			guid->b[3],  guid->b[2],  guid->b[1],  guid->b[0],
			guid->b[5],  guid->b[4],  guid->b[7],  guid->b[6],
			guid->b[8],  guid->b[9],  guid->b[10], guid->b[11],
			guid->b[12], guid->b[13], guid->b[14], guid->b[15]
			);
}

/* check the partition sizes and write the partition table */
static int gen_ptable(uint32_t signature, int nr)
{
	struct pte pte[4];
	unsigned long sect = 0;
	int i, fd, ret = -1, start, len;

	memset(pte, 0, sizeof(struct pte) * 4);
	for (i = 0; i < nr; i++) {
		if (!parts[i].size) {
			if (ignore_null_sized_partition)
				continue;
			fprintf(stderr, "Invalid size in partition %d!\n", i);
			return -1;
		}

		pte[i].active = ((i + 1) == active) ? 0x80 : 0;
		pte[i].type = parts[i].type;

		start = sect + sectors;
		if (kb_align != 0)
			start = round_to_kb(start);
		pte[i].start = cpu_to_le32(start);

		sect = start + parts[i].size * 2;
		if (kb_align == 0)
			sect = round_to_cyl(sect);
		pte[i].length = cpu_to_le32(len = sect - start);

		to_chs(start, pte[i].chs_start);
		to_chs(start + len - 1, pte[i].chs_end);

		if (verbose)
			fprintf(stderr, "Partition %d: start=%ld, end=%ld, size=%ld\n", i, (long)start * 512, ((long)start + (long)len) * 512, (long)len * 512);
		printf("%ld\n", (long)start * 512);
		printf("%ld\n", (long)len * 512);
	}

	if ((fd = open(filename, O_WRONLY|O_CREAT|O_TRUNC, 0644)) < 0) {
		fprintf(stderr, "Can't open output file '%s'\n",filename);
		return -1;
	}

	lseek(fd, 440, SEEK_SET);
	if (write(fd, &signature, sizeof(signature)) != sizeof(signature)) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	lseek(fd, 446, SEEK_SET);
	if (write(fd, pte, sizeof(struct pte) * 4) != sizeof(struct pte) * 4) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}
	lseek(fd, 510, SEEK_SET);
	if (write(fd, "\x55\xaa", 2) != 2) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	ret = 0;
fail:
	close(fd);
	return ret;
}

/* check the partition sizes and write the guid partition table */
static int gen_gptable(uint32_t signature, guid_t guid, int nr)
{
	struct pte pte;
	struct gpth gpth = {
		.signature = GPT_SIGNATURE,
		.revision = GPT_REVISION,
		.size = cpu_to_le32(GPT_HEADER_SIZE),
		.self = cpu_to_le64(1),
		.first_usable = cpu_to_le64(GPT_ENTRY_SIZE * GPT_ENTRY_NUM / 512 + 2),
		.first_entry = cpu_to_le64(2),
		.disk_guid = guid,
		.entry_num = cpu_to_le32(GPT_ENTRY_NUM),
		.entry_size = cpu_to_le32(GPT_ENTRY_SIZE),
	};
	struct gpte  gpte[GPT_ENTRY_NUM];
	unsigned long long start, end, sect = 0;
	int i, fd, ret = -1;

	memset(gpte, 0, GPT_ENTRY_SIZE * GPT_ENTRY_NUM);
	for (i = 0; i < nr; i++) {
		if (!parts[i].size) {
			if (ignore_null_sized_partition)
				continue;
			fprintf(stderr, "Invalid size in partition %d!\n", i);
			return -1;
		}
		start = sect + sectors;
		if (kb_align != 0)
			start = round_to_kb(start);
		gpte[i].start = cpu_to_le64(start);

		sect = start + parts[i].size * 2;
		if (kb_align == 0)
			sect = round_to_cyl(sect);
		gpte[i].end = cpu_to_le64(sect -1);
		gpte[i].guid = guid;
		gpte[i].guid.b[15] += i + 1;
		if (parts[i].type == 0xEF || (i + 1) == active) {
			gpte[i].type = GPT_PARTITION_ESP;
		} else {
			gpte[i].type = GPT_PARTITION_DATA;
		}

		if (verbose)
			fprintf(stderr, "Partition %d: start=%lld, end=%lld, size=%lld\n", i, start * 512, sect * 512, (sect - start) * 512);
		printf("%lld\n", start * 512);
		printf("%lld\n", (sect - start) * 512);
	}

	gpte[GPT_ENTRY_NUM - 1].start = cpu_to_le64(GPT_ENTRY_SIZE * GPT_ENTRY_NUM / 512 + 2);
	gpte[GPT_ENTRY_NUM - 1].end = cpu_to_le64((kb_align ? round_to_kb(sectors) : sectors) - 1);
	gpte[GPT_ENTRY_NUM - 1].type = GPT_PARTITION_BIOS;
	gpte[GPT_ENTRY_NUM - 1].guid = guid;
	gpte[GPT_ENTRY_NUM - 1].guid.b[15] += GPT_ENTRY_NUM;

	end = sect + sectors - 1;

	pte.type = 0xEE;
	pte.start = cpu_to_le32(1);
	pte.length = cpu_to_le32(end);
	to_chs(1, pte.chs_start);
	to_chs(end, pte.chs_end);

	gpth.last_usable = cpu_to_le64(end - GPT_ENTRY_SIZE * GPT_ENTRY_NUM / 512 - 1);
	gpth.alternate = cpu_to_le64(end);
	gpth.entry_crc32 = gpt_crc32(gpte, GPT_ENTRY_SIZE * GPT_ENTRY_NUM);
	gpth.crc32 = gpt_crc32((char *)&gpth, GPT_HEADER_SIZE);

	if ((fd = open(filename, O_WRONLY|O_CREAT|O_TRUNC, 0644)) < 0) {
		fprintf(stderr, "Can't open output file '%s'\n",filename);
		return -1;
	}

	lseek(fd, 440, SEEK_SET);
	if (write(fd, &signature, sizeof(signature)) != sizeof(signature)) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	lseek(fd, 446, SEEK_SET);
	if (write(fd, &pte, sizeof(struct pte)) != sizeof(struct pte)) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	lseek(fd, 510, SEEK_SET);
	if (write(fd, "\x55\xaa", 2) != 2) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	lseek(fd, 512, SEEK_SET);
	if (write(fd, &gpth, GPT_HEADER_SIZE) != GPT_HEADER_SIZE) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	lseek(fd, 1024, SEEK_SET);
	if (write(fd, &gpte, GPT_ENTRY_SIZE * GPT_ENTRY_NUM) != GPT_ENTRY_SIZE * GPT_ENTRY_NUM) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	/* The second partition table */
	sect = gpth.self;
	gpth.self = gpth.alternate;
	gpth.alternate = sect;
	gpth.first_entry = cpu_to_le64(end - GPT_ENTRY_SIZE * GPT_ENTRY_NUM / 512),
	gpth.crc32 = 0;
	gpth.crc32 = gpt_crc32(&gpth, GPT_HEADER_SIZE);

	lseek(fd, end * 512 - GPT_ENTRY_SIZE * GPT_ENTRY_NUM, SEEK_SET);
	if (write(fd, &gpte, GPT_ENTRY_SIZE * GPT_ENTRY_NUM) != GPT_ENTRY_SIZE * GPT_ENTRY_NUM) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	lseek(fd, end * 512, SEEK_SET);
	if (write(fd, &gpth, GPT_HEADER_SIZE) != GPT_HEADER_SIZE) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	lseek(fd, end * 512 + 511, SEEK_SET);
	if (write(fd, "\x00", 1) != 1) {
		fprintf(stderr, "write failed.\n");
		goto fail;
	}

	ret = 0;
fail:
	close(fd);
	return ret;
}



static void usage(char *prog)
{
	fprintf(stderr, "Usage: %s [-v] [-n] [-g] -h <heads> -s <sectors> -o <outputfile> [-a 0..4] [-l <align kB>] [-G <guid>] [[-t <type>] -p <size>...] \n", prog);
	exit(EXIT_FAILURE);
}

int main (int argc, char **argv)
{
	unsigned char type = 0x83;
	int ch;
	int part = 0;
	uint32_t signature = 0x5452574F; /* 'OWRT' */
	guid_t guid = GUID_INIT( signature, 0x2211, 0x4433, \
			0x55, 0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0x00);

	while ((ch = getopt(argc, argv, "h:s:p:a:t:o:vngl:S:G:")) != -1) {
		switch (ch) {
		case 'o':
			filename = optarg;
			break;
		case 'v':
			verbose++;
			break;
		case 'n':
			ignore_null_sized_partition = true;
			break;
		case 'g':
			use_guid_partition_table = 1;
			break;
		case 'h':
			heads = (int)strtoul(optarg, NULL, 0);
			break;
		case 's':
			sectors = (int)strtoul(optarg, NULL, 0);
			break;
		case 'p':
			if (part > GPT_ENTRY_NUM - 1 || (use_guid_partition_table == false && part > 3)) {
				fprintf(stderr, "Too many partitions\n");
				exit(EXIT_FAILURE);
			}
			parts[part].size = to_kbytes(optarg);
			parts[part++].type = type;
			break;
		case 't':
			type = (char)strtoul(optarg, NULL, 16);
			break;
		case 'a':
			active = (int)strtoul(optarg, NULL, 0);
			if ((active < 0) || (active > 4))
				active = 0;
			break;
		case 'l':
			kb_align = (int)strtoul(optarg, NULL, 0) * 2;
			break;
		case 'S':
			signature = strtoul(optarg, NULL, 0);
			break;
		case 'G':
			if (guid_parse(optarg, &guid)) {
				fprintf(stderr, "Invalid guid string\n");
				exit(EXIT_FAILURE);
			}
			//guid_print(&guid);
			break;
		case '?':
		default:
			usage(argv[0]);
		}
	}
	argc -= optind;
	if (argc || (heads <= 0) || (sectors <= 0) || !filename)
		usage(argv[0]);

	if (use_guid_partition_table) {
		return gen_gptable(signature, guid, part) ? EXIT_FAILURE : EXIT_SUCCESS;
	} else {
		return gen_ptable(signature, part) ? EXIT_FAILURE : EXIT_SUCCESS;
	}
}
