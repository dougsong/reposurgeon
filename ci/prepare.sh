#!/bin/bash

apt-get update -qy && apt-get install -qy \
    asciidoctor \
    cvs \
    cvs-fast-export \
    golang-1.13-go \
    golint \
    make \
    mercurial \
    python2.7 \
    pylint \
    python3 \
    shellcheck \
    subversion \
    time \
 && apt-get clean \
 && rm -rf /var/lib/apt/lists/*

echo
echo ============= Dependency install complete ============= 
echo
