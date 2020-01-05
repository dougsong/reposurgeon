#!/bin/bash

# Install dependencies that aren't included in buildpack-deps:jessie

REPOSURGEON_DIR=$(pwd)

apt-get update -qy && apt-get install -qy --no-install-recommends \
    asciidoc \
    asciidoctor \
    bison \
    cvs \
    flex \
    golang \
    libpcre3-dev \
    mercurial \
    parallel \
    pypy \
    python2.7 \
    python3 \
    subversion \
    time \
    xmlto \
 && apt-get clean \
 && rm -rf /var/lib/apt/lists/*

# Install cvs-fast-export - this is the only reason bison and flex are installed
mkdir -p /usr/local/src/
cd /usr/local/src/
git clone https://gitlab.com/esr/cvs-fast-export.git && \
    cd cvs-fast-export/ && \
    make install

cd $REPOSURGEON_DIR

echo
echo ============= Dependency install complete ============= 
echo
