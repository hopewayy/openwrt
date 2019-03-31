GRUB2_PLATFORM:=efi

include ../common.mk

define Host/Install
	$(call Host/Compile/Default,install-data)
endef

$(eval $(call HostBuild))
# make scan.mk happy
#$(eval $(call BuildPackage,grub2-efi))
