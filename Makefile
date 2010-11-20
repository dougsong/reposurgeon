#
# makefile for reposurgeon
#
VERS=$(shell sed <reposurgeon -n -e '/version=\(.*\)/s//\1/p')

SOURCES = README NEWS COPYING reposurgeon reposurgeon.xml reposurgeon.1 Makefile
SOURCES += control .shipper reposturgeon.gif

all: reposurgeon.1

reposurgeon.1: reposurgeon.xml
	xmlto man reposurgeon.xml

reposurgeon.html: reposurgeon.xml
	xmlto html-nochunks reposurgeon.xml

clean:
	rm -f  *~ *.1 *.html *.tar.gz MANIFEST SHIPPER.*
	rm -fr .rs .rs* test/.rs test/.rs*
	rm -f typescript test/typescript

reposurgeon-$(VERS).tar.gz: $(SOURCES)
	@ls $(SOURCES) | sed s:^:reposurgeon-$(VERS)/: >MANIFEST
	@(cd ..; ln -s reposurgeon reposurgeon-$(VERS))
	(cd ..; tar -czvf reposurgeon/reposurgeon-$(VERS).tar.gz `cat reposurgeon/MANIFEST`)
	@(cd ..; rm reposurgeon-$(VERS))

version:
	@echo $(VERS)

pychecker:
	ln -f reposurgeon reposurgeon.py
	pychecker --only --limit 50 reposurgeon.py
	rm -f reposurgeon.py

check:
	cd test; make --quiet

dist: reposurgeon-$(VERS).tar.gz

release: reposurgeon-$(VERS).tar.gz reposurgeon.html
	shipper -u -m -t; make clean
