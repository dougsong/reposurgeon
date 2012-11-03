#
# makefile for reposurgeon
#
VERS=$(shell sed <reposurgeon -n -e '/version=\(.*\)/s//\1/p')

SOURCES = README NEWS COPYING TODO 
SOURCES += reposurgeon reposurgeon.xml conversion.mk svnpull svnpull.xml
SOURCES += Makefile control reposturgeon.png

all: reposurgeon.1

reposurgeon.1: reposurgeon.xml
	xmlto man reposurgeon.xml

reposurgeon.html: reposurgeon.xml
	xmlto html-nochunks reposurgeon.xml

svnpull.1: svnpull.xml
	xmlto man svnpull.xml

svnpull.html: svnpull.xml
	xmlto html-nochunks svnpull.xml

clean:
	rm -f  *~ *.1 *.html *.tar.gz MANIFEST SHIPPER.*
	rm -fr .rs .rs* test/.rs test/.rs*
	rm -f typescript test/typescript *.pyc

reposurgeon-$(VERS).tar.gz: $(SOURCES)
	@ls $(SOURCES) | sed s:^:reposurgeon-$(VERS)/: >MANIFEST
	@(cd ..; ln -s reposurgeon reposurgeon-$(VERS))
	(cd ..; tar -czf reposurgeon/reposurgeon-$(VERS).tar.gz `cat reposurgeon/MANIFEST`)
	@(cd ..; rm reposurgeon-$(VERS))

version:
	@echo $(VERS)

pychecker:
	@ln -f reposurgeon reposurgeon.py
	@-pychecker --only --limit 50 reposurgeon.py
	@rm -f reposurgeon.py

PYLINTOPTS = --rcfile=/dev/null --reports=n --include-ids=y --disable=C0103,C0111,C0301,C0302,C0322,C0324,C0321,C0323,R0201,R0902,R0903,R0904,R0911,R0912,R0913,R0914,R0915,W0108,W0141,W0142,W0212,W0233,W0603,W0511,W0611,E1101,E1103
pylint:
	@pylint --output-format=parseable $(PYLINTOPTS) reposurgeon

check: pylint
	cd test; make --quiet

dist: reposurgeon-$(VERS).tar.gz reposurgeon.1 svnpull.1

release: reposurgeon-$(VERS).tar.gz reposurgeon.html svnpull.html
	shipper -u -m -t; make clean
