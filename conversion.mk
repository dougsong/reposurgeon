# Generic makefile for Subversion-to-DVCS conversions using reposurgeon
#
# Steps to using this:
# 1. Make sure reposurgeon and svnpull are on your $PATH.
# 2. Set SVN_URL to point at the remote repository you want to convert.
# 3. Set DVCS to git, hg, or bzr
# 4. Create a project.lift script for your custom commands, initially empty.
# 5. (Optional) Set EXTRAS to name extra metadata such as a comments mailbox.
# 6. (Optional) Replace 'project' with a short name for your project.
# 7. Invoke make on this file.

SVN_URL = svn://random-host.net/project
DVCS = git
EXTRAS =

.PHONY: clean dist compare clobber

# Build the repo from the fast-import stream
project-$(DVCS): project.fi
	rm -fr project-$(DVCS); reposurgeon "read project.fi" "prefer $(DVCS)" "rebuild project-$(DVCS)"

# Build the fast-import stream from the stream dump
project.fi: project.svn project.lift reposurgeon $(EXTRAS)
	reposurgeon "verbose 1" "read project.svn" "script project.lift" "write project.fi"

# Get the stream dump from the local mirror
project.svn: project-mirror
	svnpull project-mirror
	svnadmin dump project-mirror/ >project.svn

# Make local mirror of the PROJECT Subversion repo
project-mirror:
	svnpull $(SVN_URL)

# Force rebuild of the fast-import stream from the local mirror on the next make
clean:
	rm -fr project.fi project-$(DVCS) *~ .rs* project-conversion.tar.gz 

# Force full rebuild from the remote repo on the next make.
clobber: clean
	rm -fr project.svn project-mirror svn-checkout

# Make a local checkout of the Subversion project for 
svn-checkout: project-mirror
	svn co file://${PWD}/project-mirror svn-checkout

#
# The following productions are git-specific
#

# Browse the generated git repository
gitk: project-git
	cd project-git; gitk --all

# Run a garbage-collect on the generated git repository.  Import doesn't.
gc: project-git
	cd project-git; git gc --aggressive

# Make a conversion using a competing tool
git-svn:
	git svn --stdlayout clone file://${PWD}/project-mirror git-svn

# Compare the results
compare: git-svn project-git
	rm -f GITSVN.MANIFEST PROJECTGIT.MANIFEST
	(cd git-svn; find . -type f | sort | fgrep -v '.git') >GITSVN.MANIFEST
	(cd project-git; find . -type f | sort | fgrep -v '.git') >PROJECTGIT.MANIFEST
	diff -u GITSVN.MANIFEST PROJECTGIT.MANIFEST

SOURCES = Makefile project.lift $(EXTRAS)
project-conversion.tar.gz: $(SOURCES)
	tar --dereference --transform 's:^:project-conversion/:' -czvf project-conversion.tar.gz $(SOURCES)

dist: project-conversion.tar.gz
