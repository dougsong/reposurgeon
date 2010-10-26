#
# makefile for reposugeon
#
VERS=1.0

SOURCES = README COPYING reposurgeon reposurgeon.xml reposurgeon.6 Makefile reposurgeon.spec

all: reposurgeon.1

reposurgeon.1: reposurgeon.xml
	xmlto man reposurgeon.xml

reposurgeon.html: reposurgeon.xml
	xmlto html-nochunks reposurgeon.xml

clean:
	rm -f *~ *.1 *.html MANIFEST SHIPPER.*

reposurgeon-$(VERS).tar.gz: $(SOURCES)
	@ls $(SOURCES) | sed s:^:reposurgeon-$(VERS)/: >MANIFEST
	@(cd ..; ln -s reposurgeon reposurgeon-$(VERS))
	(cd ..; tar -czvf reposurgeon/reposurgeon-$(VERS).tar.gz `cat reposurgeon/MANIFEST`)
	@(cd ..; rm reposurgeon-$(VERS))

dist: reposurgeon-$(VERS).tar.gz

release: reposurgeon-$(VERS).tar.gz reposurgeon.html
	shipper -u -m -t; make clean
