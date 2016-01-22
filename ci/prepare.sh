#!/bin/bash

# Install dependencies that aren't included in buildpack-deps:jessie

REPOSURGEON_DIR=$(pwd)

apt-get update -qy && apt-get install -qy --no-install-recommends \
    asciidoc \
    bison \
    cvs \
    flex \
    python2.7 \
    python-pip \
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

pip install -r requirements.txt

echo
echo ============= Dependency install complete ============= 
echo
