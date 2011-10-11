#
# makefile for reposurgeon
#
VERS=$(shell sed <reposurgeon -n -e '/version=\(.*\)/s//\1/p')

SOURCES = README NEWS COPYING reposurgeon reposurgeon.xml reposurgeon.1 Makefile
SOURCES += control reposturgeon.png

all: reposurgeon.1

reposurgeon.1: reposurgeon.xml
	xmlto man reposurgeon.xml

reposurgeon.html: reposurgeon.xml
	xmlto html-nochunks reposurgeon.xml

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

PYLINTOPTS = --disable=C0103,C0111,C0301,C0302,C0322,C0324,C0323,R0201,R0902,R0903,R0904,R0911,R0912,R0913,R0914,R0915,W0141,W0603
pylint:
	pylint --output-format=parseable $(PYLINTOPTS) reposurgeon

check:
	cd test; make --quiet

dist: reposurgeon-$(VERS).tar.gz

release: reposurgeon-$(VERS).tar.gz reposurgeon.html
	shipper -u -m -t; make clean
