#!/bin/bash

apt-get update -qy && apt-get install -qy --no-install-recommends \
    asciidoc \
    asciidoctor \
    cvs \
    cvs-fast-export \
    golang \
    mercurial \
    parallel \
    python2.7 \
    python3 \
    subversion \
    time \
 && apt-get clean \
 && rm -rf /var/lib/apt/lists/*

echo
echo ============= Dependency install complete ============= 
echo
