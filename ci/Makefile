#
# makefile for reposurgeon continuous integration
#
# This has targets for switching to special sets of package installs
# for testing purposes. You probably only want to run it inside
# temporary Docker containers or VMs.

VERS=$(shell sed <reposurgeon -n -e '/version=\(.*\)/s//\1/p')

# Combine SCM packages installed by ci/prepare.sh and installed by 
# https://github.com/docker-library/buildpack-deps/blob/master/jessie/scm/Dockerfile
DOCKER-SCM=bzr \
    cvs \
    git \
    mercurial \
    openssh-client \
    subversion

.PHONY: 

install-only-%:
	apt-get -qy autoremove $(DOCKER-SCM) $(*)+

install-no-%:
	apt-get -qy autoremove $*

install-hglib:
	pip install 'python-hglib>=1.9'
