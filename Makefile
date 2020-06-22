#
# makefile for reposurgeon
#
INSTALL=install
prefix?=/usr/local
mandir?=share/man
target=$(DESTDIR)$(prefix)

VERS=$(shell sed <surgeon/version.go -n -e '/const *version *= *\"\(.*\)\"/s//\1/p')

META = README.adoc INSTALL.adoc NEWS.adoc COPYING
PAGES = reposurgeon.adoc repocutter.adoc repomapper.adoc repotool.adoc repobench.adoc
DOCS = $(PAGES) repository-editing.adoc oops.svg
SOURCES = $(shell ls */*.go) repobench reposurgeon-mode.el go.mod go.sum
SOURCES += Makefile control reposturgeon.png reposurgeon-git-aliases
SOURCES += Dockerfile ci/prepare.sh .gitlab-ci.yml
SOURCES += $(META) $(DOCS)

.PHONY: all build install install_bin install_man install_share clean		\
    uninstall version check release refresh docker-build docker-check	\
    docker-check-noscm get vet test fmt lint

BINARIES  = reposurgeon repotool repomapper repocutter repobench
MANPAGES  = $(PAGES:.adoc=.1)
HTMLFILES = $(DOCS:.adoc=.html)
SHARED    = $(META) reposurgeon-git-aliases $(HTMLFILES)

# The following would produce reproducible builds, but it breaks Gitlab CI.
#GOFLAGS=-gcflags 'all=-N -l -trimpath $(GOPATH)/src' -asmflags 'all=-trimpath $(GOPATH)/src'

GOFLAGS=-gcflags '-N -l'

# Must force options.adoc to be built earky so it will be available for inclusion. 
build: $(BINARIES) options.adoc $(MANPAGES) $(HTMLFILES)

# Imitate old behavior of rebuilding bins. They have no dependencies
# so *not* building them would be irritating if sources change.
.PHONY: repocutter reposurgeon repomapper repotool

repocutter:
	go build $(GOFLAGS) -o $(CURDIR)/repocutter ./cutter
reposurgeon:
	go build $(GOFLAGS) -o $(CURDIR)/reposurgeon ./surgeon
repomapper:
	go build $(GOFLAGS) -o $(CURDIR)/repomapper ./mapper
repotool:
	go build $(GOFLAGS) -o $(CURDIR)/repotool ./tool

# Generated documentation parts:

options.adoc: reposurgeon
	./reposurgeon "help options" | sed '/:/s//::/' >options.adoc

# Note: to suppress the footers with timestamps being generated in HTML,
# we use "-a nofooter".
# To debug asciidoc problems, you may need to run "xmllint --nonet --noout --valid"
# on the intermediate XML that throws an error.
.SUFFIXES: .html .adoc .1

.adoc.1:
	asciidoctor -D. -a nofooter -b manpage $<
.adoc.html:
	asciidoctor -D. -a webfonts! $<

#
# Auxillary Go tooling productions
#

get:
	go get -u ./...	# go get -u=patch for patch releases

test:
	go test $(TESTOPTS) ./surgeon
	go test $(TESTOPTS) ./cutter

lint:
	golint -set_exit_status ./...
	shellcheck -f gcc repobench test/fi-to-fi test/liftcheck test/singlelift test/svn-to-git test/svn-to-svn test/delver test/*.sh test/*test

fmt:
	gofmt -w .

#
# Installation
#

install_bin: $(BINARIES)
	$(INSTALL) -d "$(target)/bin"
	$(INSTALL) -m 755 $^ "$(target)/bin"

install_man: $(MANPAGES)
	$(INSTALL) -d "$(target)/$(mandir)/man1"
	$(INSTALL) -m 644 $^ "$(target)/$(mandir)/man1"

install_share: $(SHARED)
	$(INSTALL) -d "$(target)/share/doc/reposurgeon"
	$(INSTALL) -m 644 $^ "$(target)/share/doc/reposurgeon"

install: install_bin install_man install_share

clean:
	rm -fr reposurgeon repocutter repomapper repotool
	rm -f options.adoc
	rm -fr  *~ *.1 *.html *.tar.xz MANIFEST *.md5
	rm -fr .rs .rs* test/.rs test/.rs*
	rm -f typescript test/typescript

# Uninstallation
INSTALLED_BINARIES := $(BINARIES:%="$(target)/bin/%")
INSTALLED_SHARED   := $(SHARED:%="$(target)/share/doc/reposurgeon/%")
INSTALLED_MANPAGES := $(MANPAGES:%="$(target)/$(mandir)/man1/%")

uninstall:
	rm -f $(INSTALLED_BINARIES)
	rm -f $(INSTALLED_MANPAGES)
	rm -f $(INSTALLED_SHARED)
	rmdir "$(target)/share/doc/reposurgeon"

version:
	@echo $(VERS)

#
# Code validation
#

check: lint build test
	$(MAKE) -C test --quiet check BINDIR=$(realpath $(CURDIR))
#
# Continuous integration.  More specifics are in the ci/ directory
#

docker-build: $(SOURCES)
	docker build -t reposurgeon .

docker-check: docker-build
	docker run --rm -i -e "MAKEFLAGS=$(MAKEFLAGS)" -e "MAKEOVERRIDES=$(MAKEOVERRIDES)" reposurgeon make check

docker-check-only-%: docker-build
	docker run --rm -i -e "MAKEFLAGS=$(MAKEFLAGS)" -e "MAKEOVERRIDES=$(MAKEOVERRIDES)" reposurgeon bash -c "make -C ci install-only-$(*) && make check"

docker-check-no-%: docker-build
	docker run --rm -i -e "MAKEFLAGS=$(MAKEFLAGS)" -e "MAKEOVERRIDES=$(MAKEOVERRIDES)" reposurgeon bash -c "make -C ci install-no-$(*) && make check"

# Test that support for each VCS stands on its own and test without legacy
# VCS installed
docker-check-noscm: docker-check-only-bzr docker-check-only-cvs \
    docker-check-only-git docker-check-only-mercurial \
    docker-check-only-subversion docker-check-no-cvs 
# Due to many tests depending on git, docker-check-only-mercurial is a very poor
# test of Mercurial

#
# Release shipping.
#

reposurgeon-$(VERS).tar.xz: $(SOURCES) $(MANPAGES)
	tar --transform='s:^:reposurgeon-$(VERS)/:' --show-transformed-names -cJf reposurgeon-$(VERS).tar.xz $(SOURCES) $(MANPAGES) test

dist: reposurgeon-$(VERS).tar.xz

reposurgeon-$(VERS).md5: reposurgeon-$(VERS).tar.xz
	@md5sum reposurgeon-$(VERS).tar.xz >reposurgeon-$(VERS).md5

release: reposurgeon-$(VERS).tar.xz reposurgeon-$(VERS).md5 $(HTMLFILES)
	shipper version=$(VERS) | sh -e -x

refresh: $(HTMLFILES)
	shipper -N -w version=$(VERS) | sh -e -x
