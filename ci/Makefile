#
# makefile for reposurgeon continuous integration
#

VERS=$(shell sed <reposurgeon -n -e '/version=\(.*\)/s//\1/p')

.PHONY: 

install-hglib:
	pip install 'python-hglib>=1.9'
