#!/bin/bash

# tzdata needs to be installed first and expicitly
# to avoid CI trying interactive configuration on it.
export DEBIAN_FRONTEND=noninteractive
apt-get update -qy && apt-get install -qy \
    tzdata \
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
