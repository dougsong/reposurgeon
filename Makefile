#
# makefile for reposurgeon
#
INSTALL=install
prefix?=/usr/local
mandir?=share/man
target=$(DESTDIR)$(prefix)

META = README.adoc INSTALL.adoc NEWS.adoc COPYING
PAGES = reposurgeon.adoc repocutter.adoc repomapper.adoc repotool.adoc repobench.adoc
DOCS = $(PAGES) repository-editing.adoc oops.svg
SOURCES = $(shell ls */*.go) repobench reposurgeon-mode.el go.mod go.sum extractversion.sh
SOURCES += Makefile control reposturgeon.png reposurgeon-git-aliases
SOURCES += Dockerfile ci/prepare.sh .gitlab-ci.yml
SOURCES += $(META) $(DOCS)

.PHONY: all build install uninstall version check release refresh \
	docker-build docker-check docker-check-noscm get test fmt lint

BINARIES  = reposurgeon repotool repomapper repocutter repobench
MANPAGES  = $(PAGES:.adoc=.1)
HTMLFILES = $(DOCS:.adoc=.html)
SHARED    = $(META) reposurgeon-git-aliases $(HTMLFILES)

# Binaries need to be built before generated documentation parts can be made.
# Must force options.adoc to be built earky so it will be available for inclusion.
all: build options.adoc $(MANPAGES) $(HTMLFILES)

# The following would produce reproducible builds, but it breaks Gitlab CI.
#GOFLAGS=-gcflags 'all=-N -l -trimpath $(GOPATH)/src' -asmflags 'all=-trimpath $(GOPATH)/src'
GOFLAGS=-gcflags '-N -l'
build:
	sh extractversion.sh -g <NEWS.adoc >surgeon/version.go
	go build $(GOFLAGS) -o repocutter ./cutter
	go build $(GOFLAGS) -o repomapper ./mapper
	go build $(GOFLAGS) -o reposurgeon ./surgeon
	go build $(GOFLAGS) -o repotool ./tool

#
# Documentation
#

options.adoc: build
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
	shellcheck -f gcc extractversion.sh repobench test/fi-to-fi test/liftcheck test/singlelift test/svn-to-git test/svn-to-svn test/delver test/*.sh test/*test

fmt:
	gofmt -w .

#
# Cleaning
#
clean:
	rm -f $(BINARIES) options.adoc surgeon/version.go
	rm -fr  *~ *.1 *.html *.tar.xz MANIFEST *.md5
	rm -fr .rs .rs* test/.rs test/.rs*
	rm -f typescript test/typescript

#
# Installation
#
# Note that this does not run a build, so it will error out (harmlessly) if you 
# have not done "make all" or "make build" first.  There's a conflict between
# Go's preference for Rebuilding All The Things and the traditional makefile
# attempt to do as little build work as possible at any given time.
#
install:
	$(INSTALL) -d "$(target)/bin"
	$(INSTALL) -d "$(target)/share/doc/reposurgeon"
	$(INSTALL) -d "$(target)/$(mandir)/man1"
	$(INSTALL) -m 755 $(BINARIES) "$(target)/bin"
	$(INSTALL) -m 644 $(SHARED) "$(target)/share/doc/reposurgeon"
	$(INSTALL) -m 644 $(MANPAGES) "$(target)/$(mandir)/man1"

#
# Uninstallation
#

INSTALLED_BINARIES := $(BINARIES:%="$(target)/bin/%")
INSTALLED_SHARED   := $(SHARED:%="$(target)/share/doc/reposurgeon/%")
INSTALLED_MANPAGES := $(MANPAGES:%="$(target)/$(mandir)/man1/%")

uninstall:
	rm -f $(INSTALLED_BINARIES)
	rm -f $(INSTALLED_MANPAGES)
	rm -f $(INSTALLED_SHARED)
	rmdir "$(target)/share/doc/reposurgeon"

VERS=$(shell sh ./extractversion.sh <NEWS.adoc)

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

# Don't try using tar --transform, it tries to get too clever with symlinks 
SHIPPABLE = $(SOURCES) $(MANPAGES)
reposurgeon-$(VERS).tar.xz: $(SHIPPABLE)
	@ls $(SHIPPABLE) | sed s:^:reposurgeon-$(VERS)/: >MANIFEST
	@(cd ..; ln -s reposurgeon reposurgeon-$(VERS))
	@(cd ..; tar -cJf reposurgeon/reposurgeon-$(VERS).tar.xz `cat reposurgeon/MANIFEST`)
	@(cd ..; rm reposurgeon-$(VERS) reposurgeon/MANIFEST)

dist: reposurgeon-$(VERS).tar.xz

reposurgeon-$(VERS).md5: reposurgeon-$(VERS).tar.xz
	@md5sum reposurgeon-$(VERS).tar.xz >reposurgeon-$(VERS).md5

release: reposurgeon-$(VERS).tar.xz reposurgeon-$(VERS).md5 $(HTMLFILES)
	shipper version=$(VERS) | sh -e -x

refresh: $(HTMLFILES)
	shipper -N -w version=$(VERS) | sh -e -x

# end
