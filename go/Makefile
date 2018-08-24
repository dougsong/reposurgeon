# The layout of this Go workspace is a little nonstandard, due to the
# requirement that it play nice with Python and waf. This file attempts
# to paper over the cracks.

GOPATH=$(shell pwd)

default: build

build:
	GOPATH=$(GOPATH) go build repocutter
	GOPATH=$(GOPATH) go build repomapper

test:
	GOPATH=$(GOPATH) go test

format:
	gofmt -w src/repocutter/
	gofmt -w src/repomapper/

lint:
	@golint src/repocutter 2>&1
	@golint src/repomapper 2>&1

clean:
	rm -fr repocutter repomapper
