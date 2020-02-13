#!/bin/bash

apt-get update -qy && apt-get install -qy --no-install-recommends \
    asciidoctor \
    cvs \
    cvs-fast-export \
    golint \
    mercurial \
    python2.7 \
    python3 \
    subversion \
    time \
 && apt-get clean \
 && rm -rf /var/lib/apt/lists/*
type go
go version

echo
echo ============= Dependency install complete ============= 
echo
