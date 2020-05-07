#!/bin/bash

apt-get update -qy && apt-get install -qy --no-install-recommends \
    asciidoctor \
    cvs \
    cvs-fast-export \
    golang \
    golint \
    mercurial \
    pylint \
    python3 \
    rsync \
    shellcheck \
    subversion \
    time \
 && apt-get clean \
 && rm -rf /var/lib/apt/lists/*
type go
go version

echo
echo ============= Dependency install complete =============
echo USER=$USER PWD=$PWD
echo
