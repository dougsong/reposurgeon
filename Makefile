#
# makefile for reposurgeon
#
VERS=$(shell sed <reposurgeon -n -e '/version=\(.*\)/s//\1/p')

SOURCES = README NEWS COPYING TODO 
SOURCES += \
	reposurgeon reposurgeon.xml \
	repopuller repopuller.xml \
	repodiffer repodiffer.xml \
	conversion.mk features.asc \
	reposurgeon-mode.el
SOURCES += Makefile control reposturgeon.png

all: reposurgeon.1 repopuller.1 repodiffer.1

reposurgeon.1: reposurgeon.xml
	xmlto man reposurgeon.xml

reposurgeon.html: reposurgeon.xml
	xmlto html-nochunks reposurgeon.xml

repopuller.1: repopuller.xml
	xmlto man repopuller.xml

repopuller.html: repopuller.xml
	xmlto html-nochunks repopuller.xml

repodiffer.1: repodiffer.xml
	xmlto man repodiffer.xml

repodiffer.html: repodiffer.xml
	xmlto html-nochunks repodiffer.xml

features.html: features.asc
	asciidoc features.asc

clean:
	rm -fr  *~ *.1 *.html *.tar.gz MANIFEST SHIPPER.*
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

COMMON_PYLINT = --rcfile=/dev/null --reports=n --include-ids=y
PYLINTOPTS1 = $(COMMON_PYLINT) --disable=C0103,C0111,C0301,C0302,C0322,C0324,C0321,C0323,R0201,R0902,R0903,R0904,R0911,R0912,R0913,R0914,R0915,W0108,W0141,W0142,W0212,W0233,W0603,W0511,W0611,E1101,E1103
PYLINTOPTS2 = $(COMMON_PYLINT) --disable=C0103,C0111,C0301,W0603,W0621,E1101,E1103,R0902,R0903,R0912,R0914,R0915
pylint:
	@pylint --output-format=parseable $(PYLINTOPTS1) reposurgeon
	@pylint --output-format=parseable $(PYLINTOPTS2) repodiffer

check: pylint
	./reposurgeon "runtests"
	cd test; make --quiet

dist: reposurgeon-$(VERS).tar.gz reposurgeon.1 repopuller.1 repodiffer.1

release: reposurgeon-$(VERS).tar.gz reposurgeon.html repodiffer.html features.html
	shipper -u -m -t; make clean
