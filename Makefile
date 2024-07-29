BUILDDIR ?= _build
.PHONY: all clean install
$(BUILDDIR)/%: $(BUILDDIR)/%.o
	$(CC) -Wl,-z,relro,-z,now,-z,noexecstack -fPIC -o $@ $^ -pthread
$(BUILDDIR)/%.o: %.c Makefile | $(BUILDDIR)/
	$(CC) $(CFLAGS) -O2 -ggdb -MD -MP -MF $@.dep -pthread -c -o $@ $< \
		-Wp,-D_FORTIFY_SOURCE=2 \
		-Wp,-D_GNU_SOURCE \
		-fPIC \
		-fstack-protector-all \
		-fsanitize=undefined \
		-fsanitize-undefined-trap-on-error \
		-fvisibility=hidden \
		-fno-delete-null-pointer-checks \
		-fno-strict-aliasing \
		-Wall \
		-Wextra \
		-Werror=vla \
		-Werror=array-bounds \
		-Werror=format=2 \
		-Werror=empty-body \
		-Werror=misleading-indentation \
		-Werror=implicit-function-declaration \
		-Werror=int-conversion \
		-Werror=unused-label \
		-Wno-gnu-case-range \
		-Wno-declaration-after-statement
all: $(BUILDDIR)/qubes-gpg-signer
	for i in Clear Armor Binary; do ln -f -- $(BUILDDIR)/qubes-gpg-signer $(BUILDDIR)/"qubes.Gpg$${i}Sign"; done
$(BUILDDIR)/:
	mkdir -p -m 0700 -- $(BUILDDIR)
clean:
	rm -f -- $(BUILDDIR)/*.o $(BUILDDIR)/qubes-gpg-signer $(BUILDDIR)/*.dep
install:
	install -D -- $(BUILDDIR)/qubes.GpgBinarySign ${DESTDIR}/etc/qubes-rpc/qubes.GpgBinarySign
	for i in Clear Armor; do ln -sf -- qubes.GpgBinarySign ${DESTDIR}/"etc/qubes-rpc/qubes.Gpg$${i}Sign"; done
-include $(BUILDDIR)/*.o.dep
