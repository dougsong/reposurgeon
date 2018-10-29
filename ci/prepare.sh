#!/bin/bash

# Install dependencies that aren't included in buildpack-deps:jessie

REPOSURGEON_DIR=$(pwd)

apt-get update -qy && apt-get install -qy --no-install-recommends \
    asciidoc \
    bison \
    cvs \
    flex \
    golang \
    libpcre3-dev \
    pypy \
    python2.7 \
    python3 \
    python-pip \
    subversion \
    time \
    xmlto \
 && apt-get clean \
 && rm -rf /var/lib/apt/lists/*

# Get required Go packages
go version
make gosetup

# Install cvs-fast-export - this is the only reason bison and flex are installed
mkdir -p /usr/local/src/
cd /usr/local/src/
git clone https://gitlab.com/esr/cvs-fast-export.git && \
    cd cvs-fast-export/ && \
    make install

cd $REPOSURGEON_DIR

pip install -r ci/requirements.txt

echo
echo ============= Dependency install complete ============= 
echo
