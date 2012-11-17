# Generic makefile for DVCS conversions using reposurgeon
#
# Steps to using this:
# 0. Copy this into a scratch directory as Makefile
# 1. Make sure rsync, reposurgeon and svnpull are on your $PATH.
# 2. Set PROJECT to the name of your project
# 3. Set SOURCE_VCS to svn or cvs
# 4. Set TARGET_VCS to git, hg, or bzr
# 5. For svn, set SVN_URL to point at the remote repository you want to convert.
# 6. For cvs, set CVS_HOST to the repository hostname
# 6. Create a $(PROJECT).lift script for your custom commands, initially empty.
# 7. (Optional) Set EXTRAS to name extra metadata such as a comments mailbox.
# 8. Invoke make on this file.

PROJECT = foo
SOURCE_VCS = svn
TARGET_VCS = git
EXTRAS = 
SVN_URL = svn://svn.debian.org/$(PROJECT)
CVS_HOST = $(PROJECT).cvs.sourceforge.net

# Configuration ends here

.PHONY: local-clobber remote-clobber gitk gc compare clean dist

default: $(PROJECT)-$(TARGET_VCS)

ifeq ($(SOURCE_VCS),svn)

# Build the repo from the fast-import stream
$(PROJECT)-$(TARGET_VCS): $(PROJECT).fi
	rm -fr $(PROJECT)-$(TARGET_VCS); reposurgeon "read $(PROJECT).fi" "prefer $(TARGET_VCS)" "rebuild $(PROJECT)-$(TARGET_VCS)"

# Build the fast-import stream from the Subversion stream dump
$(PROJECT).fi: $(PROJECT).svn $(PROJECT).lift $(EXTRAS)
	reposurgeon "verbose 1" "read $(PROJECT).svn" "script $(PROJECT).lift" "write $(PROJECT).fi"

# Build the Subversion stream dump from the local mirror
$(PROJECT).svn: $(PROJECT)-mirror
	svnpull $(PROJECT)-mirror
	svnadmin dump $(PROJECT)-mirror/ >$(PROJECT).svn

# Build a local mirror of the remote Subversion repo
$(PROJECT)-mirror:
	svnpull $(SVN_URL)

# Force rebuild of the fast-import stream from the local mirror on the next make
local-clobber: clean
	rm -fr $(PROJECT).fi $(PROJECT)-$(TARGET_VCS) *~ .rs* $(PROJECT)-conversion.tar.gz 

# Force full rebuild from the remote repo on the next make.
remote-clobber: local-clobber
	rm -fr $(PROJECT).svn $(PROJECT)-mirror svn-checkout

# Make a local checkout of the Subversion mirror for inspection
svn-checkout: $(PROJECT)-mirror
	svn co file://${PWD}/$(PROJECT)-mirror svn-checkout

# Get the Subversion state of the author mapping
$(PROJECT).map: $(PROJECT).svn
	reposurgeon "read $(PROJECT).svn" "authors write $(PROJECT).map"

endif

ifeq ($(SOURCE_VCS),cvs)

#
# The following productions are CVS-specific
#

# Mirror a CVS repo (from a site with a SourceForge-like CVS layout).
# You may need to modify this.
$(PROJECT)-mirror:
	rsync -av $(CVSHOST)::cvsroot/$(PROJECT)/* $(PROJECT)-mirror

# Build a git repo in project-cvs-git from a CVS repo in project-mirror
# You must have created an author mapping in $(PROJECT).map.
CVSIMPORT_OPTS = -s '~' -m -u -k -R -z 90 -v
$(PROJECT)-git: $(PROJECT)-mirror $(PROJECT).map
	cd $(PROJECT)-mirror
	cvs update
	git cvsimport -C ../$(PROJECT)-git $(CVSIMPORT_OPTS) -A ../$(PROJECT).map $(PROJECT)-mirror

endif

ifeq ($(TARGET_VCS),git)

#
# The following productions are git-specific
#

# Browse the generated git repository
gitk: $(PROJECT)-git
	cd $(PROJECT)-git; gitk --all

# Run a garbage-collect on the generated git repository.  Import doesn't.
gc: $(PROJECT)-git
	cd $(PROJECT)-git; git repack; git gc --aggressive

# Make a conversion using a competing tool
$(PROJECT)-git-svn:
	git svn --stdlayout clone file://${PWD}/$(PROJECT)-mirror $(PROJECT)-git-svn

# Compare the results
compare: $(PROJECT)-git-svn $(PROJECT)-git
	@rm -f GITSVN.MANIFEST PROJECTGIT.MANIFEST
	@(cd $(PROJECT)-git-svn >/dev/null; find . -type f | sort | fgrep -v '.git') >GITSVN.MANIFEST
	@(cd $(PROJECT)-git >/dev/null; find . -type f | sort | fgrep -v '.git') >PROJECTGIT.MANIFEST
	@diff -u GITSVN.MANIFEST PROJECTGIT.MANIFEST
	@echo "No diff output is good news"

endif

# General cleanup and utility
clean:
	rm -fr *~ .rs* $(PROJECT)-conversion.tar.gz 

# Bundle up the conversion metadata for shipping
SOURCES = Makefile $(PROJECT).lift $(PROJECT).map $(EXTRAS)
$(PROJECT)-conversion.tar.gz: $(SOURCES)
	tar --dereference --transform 's:^:$(PROJECT)-conversion/:' -czvf $(PROJECT)-conversion.tar.gz $(SOURCES)

dist: $(PROJECT)-conversion.tar.gz

