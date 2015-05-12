# Generic makefile for DVCS conversions using reposurgeon
#
# Steps to using this:
# 0. Copy this into a scratch directory as Makefile.
# 1. Make sure reposurgeon, repostreamer, and repopuller are on your $PATH.
# 2. Set PROJECT to the name of your project.
# 3. Set SOURCE_VCS to svn or cvs.
# 4. Set TARGET_VCS to git, hg, or bzr.
# 5. For svn, set REMOTE_URL to point at the remote repository
#    you want to convert.
# 6. For cvs, set CVS_HOST to the repo hostname and CVS_MODULE to the module,
#    then uncomment the line that builds REMOTE_URL 
#    Note: for CVS hosts other than Sourceforge or Savannah you will need to 
#    include the path to the CVS modules directory after the hostname.
# 7. Create a $(PROJECT).lift script for your custom commands, initially empty.
# 8. Run 'make stubmap' to create a stub author map.
# 9. (Optional) set REPOSURGEON to point at a faster cython build of the tool.
# 10. Run 'make' to build a converted repository.
#
# The reason both first- and second-stage stream files are generated is that,
# especially with Subversion, making the first-stage stream file is often
# painfully slow. By splitting the process, we lower the overhead of
# experiments with the lift script.
#
# For a production-quality conversion you will need to edit the map
# file and the lift script.  During the process you can set EXTRAS to
# name extra metadata such as a comments mailbox.
#
# After the conversion, you may be able to perform a sanity check with
# 'make diff' (supported for CVS and svn).  You can check
# individual tags or branches with 'make diff-tag'
#
# Note that CVS-checkout directories not matched in a conversion may be
# historical relics containing only CVSROOT directories.

PROJECT = foo
SOURCE_VCS = svn
TARGET_VCS = git
EXTRAS = 
REMOTE_URL = svn://svn.debian.org/$(PROJECT)
CVS_HOST = cvs.sourceforge.net
#CVS_HOST = cvs.savannah.gnu.org
CVS_MODULE = $(PROJECT)
#REMOTE_URL = cvs://$(CVS_HOST)/$(PROJECT)#$(CVS_MODULE)
VERBOSITY = "verbose 1"
REPOSURGEON = reposurgeon

# Configuration ends here

.PHONY: local-clobber remote-clobber gitk gc compare clean dist stubmap diff
# Tell make not to auto-remove tag directories, because it only tries rm and hence fails
.PRECIOUS: $(PROJECT)-%-checkout $(PROJECT)-%-$(TARGET_VCS)

default: $(PROJECT)-$(TARGET_VCS)

# Build the converted repo from the second-stage fast-import stream
$(PROJECT)-$(TARGET_VCS): $(PROJECT).fi
	rm -fr $(PROJECT)-$(TARGET_VCS); $(REPOSURGEON) "read <$(PROJECT).fi" "prefer $(TARGET_VCS)" "rebuild $(PROJECT)-$(TARGET_VCS)"

# Build the second-stage fast-import stream from the first-stage stream dump
$(PROJECT).fi: $(PROJECT).$(SOURCE_VCS) $(PROJECT).lift $(PROJECT).map $(EXTRAS)
	$(REPOSURGEON) $(VERBOSITY) "read <$(PROJECT).$(SOURCE_VCS)" "authors read <$(PROJECT).map" "prefer git" "script $(PROJECT).lift" "fossils write >$(PROJECT).fo" "write >$(PROJECT).fi"

# Build the first-stage stream dump from the local mirror
$(PROJECT).$(SOURCE_VCS): $(PROJECT)-mirror
	repotool mirror $(PROJECT)-mirror
	(cd $(PROJECT)-mirror/ >/dev/null; repotool export) >$(PROJECT).$(SOURCE_VCS)

# Build a local mirror of the remote repository
$(PROJECT)-mirror:
	repotool mirror $(REMOTE_URL)

# Force rebuild of first-stage stream from the local mirror on the next make
local-clobber: clean
	rm -fr $(PROJECT).fi $(PROJECT)-$(TARGET_VCS) *~ .rs* $(PROJECT)-conversion.tar.gz $(PROJECT)-*-$(TARGET_VCS)

# Force full rebuild from the remote repo on the next make.
remote-clobber: local-clobber
	rm -fr $(PROJECT).$(SOURCE_VCS) $(PROJECT)-mirror $(PROJECT)-checkout $(PROJECT)-*-checkout

# Get the (empty) state of the author mapping from the first-stage stream
stubmap: $(PROJECT).$(SOURCE_VCS)
	$(REPOSURGEON) "read <$(PROJECT).$(SOURCE_VCS)" "authors write >$(PROJECT).map"

# Compare the head revisions of the unconverted and converted repositories
EXCLUDE = -x CVS -x .$(SOURCE_VCS) -x .$(TARGET_VCS)
EXCLUDE += -x .$(SOURCE_VCS)ignore -x .$(TARGET_VCS)ignore
diff: $(PROJECT)-checkout $(PROJECT)-$(TARGET_VCS)
	diff $(EXCLUDE) -r -u $(PROJECT)-checkout $(PROJECT)-$(TARGET_VCS)

# Compare specific tags of the unconverted and converted repositories
diff-%: $(PROJECT)-%-checkout $(PROJECT)-%-$(TARGET_VCS)
	diff $(EXCLUDE) -r -u $(PROJECT)-$*-checkout $(PROJECT)-$*-$(TARGET_VCS)

# Compare all tags
diff-all-tags: $(PROJECT)-tags.txt
	make $(shell sed -e 's/^/diff-/' $(PROJECT)-tags.txt)

# Source-VCS-specific productions to build the first-stage stream dump

ifeq ($(SOURCE_VCS),svn)

# Make a local checkout of the Subversion mirror for inspection
$(PROJECT)-checkout: $(PROJECT)-mirror
	svn co file://${PWD}/$(PROJECT)-mirror $(PROJECT)-checkout

# Make a local checkout of the Subversion mirror for inspection at a specific tag
$(PROJECT)-%-checkout: $(PROJECT)-mirror
	svn co -r $* file://${PWD}/$(PROJECT)-mirror $(PROJECT)-$*-checkout

endif

ifeq ($(SOURCE_VCS),cvs)

# Make a local checkout of the CVS mirror for inspection
# Note: if your project contains binary files, change -kk to -kb.
$(PROJECT)-checkout: $(PROJECT)-mirror
	cvs -Q -d:local:${PWD}/$(PROJECT)-mirror co -P -d $(PROJECT)-checkout -kk $(CVS_MODULE)

# Make a local checkout of the CVS mirror for inspection at a specific tag
# Note: if your project contains binary files, change -kk to -kb.
$(PROJECT)-%-checkout: $(PROJECT)-mirror
	cvs -Q -d:local:${PWD}/$(PROJECT)-mirror co -P -r $* -d $(PROJECT)-$*-checkout -kk $(CVS_MODULE)

#  Get a list of tags from the CVS repository
$(PROJECT)-tags.txt: $(PROJECT)-mirror
	cvs -Q -d:local:${PWD}/$(PROJECT)-mirror rlog -h $(CVS_MODULE) 2>&1 \
	| awk -F"[.:]" '/^\t/{print $$1}' \
	| awk '{print $$1}' \
	| sort -u \
	> $(PROJECT)-tags.txt

endif

ifeq ($(TARGET_VCS),hg)

# Check out specific tags or branches from the converted repo
$(PROJECT)-%-hg: $(PROJECT)-hg
	hg clone -u $* $(PROJECT)-hg $@

endif

ifeq ($(TARGET_VCS),git)

# Check out specific tags or branches from the converted repo
$(PROJECT)-%-git: $(PROJECT)-git
	mkdir $@ && git -C $@ --git-dir ../$(PROJECT)-$(TARGET_VCS)/.git checkout -f $*

#
# The following productions are git-specific
#

# Browse the generated git repository
gitk: $(PROJECT)-git
	cd $(PROJECT)-git; gitk --all

# Run a garbage-collect on the generated git repository.  Import doesn't.
# This repack call is the active part of gc --aggressive.  This call is
# tuned for very large repositories.
gc: $(PROJECT)-git
	cd $(PROJECT)-git; time git -c pack.threads=1 repack -AdF --window=1250 --depth=250

# Make a conversion using a competing tool
$(PROJECT)-git-svn:
	git svn --stdlayout --no-metadata --authors-file=$(PROJECT).map clone file://${PWD}/$(PROJECT)-mirror $(PROJECT)-git-svn

# Compare file manifests on the master branch
compare: $(PROJECT)-git-svn $(PROJECT)-git
	@echo; echo "Comparing the directory manifests..."
	@rm -f GITSVN.MANIFEST PROJECTGIT.MANIFEST
	@(cd $(PROJECT)-git-svn >/dev/null; find . -type f | sort | fgrep -v '.git') >GITSVN.MANIFEST
	@(cd $(PROJECT)-git >/dev/null; find . -type f | sort | fgrep -v '.git') >PROJECTGIT.MANIFEST
	@echo "Comparing file manifests..."
	@diff -u GITSVN.MANIFEST PROJECTGIT.MANIFEST
	@echo "No diff output is good news"
	@echo; echo "Comparing file contents..."
	@set -e; for file in `cd $(PROJECT)-git-svn >/dev/null; git ls-files`; do cmp $(PROJECT)-git-svn/$$file $(PROJECT)-git/$$file; done
	@echo "No cmp output is good news"

# Compare all files in all revisions.  Ignore .gitignores, as reposurgeon
# makes them  but git-svn does not.
repodiffer: $(PROJECT)-git-svn $(PROJECT)-git
	repodiffer --ignore="gitignore,comment" --fossil-map=$(PROJECT).fo $(PROJECT)-git $(PROJECT)-git-svn | tee REPODIFFER.LOG

endif

# General cleanup and utility
clean:
	rm -fr *~ .rs* $(PROJECT)-conversion.tar.gz REPODIFFER.LOG *.$(SOURCE_VCS) *.fi *.fo

# Bundle up the conversion metadata for shipping
SOURCES = Makefile $(PROJECT).lift $(PROJECT).map $(EXTRAS)
$(PROJECT)-conversion.tar.gz: $(SOURCES)
	tar --dereference --transform 's:^:$(PROJECT)-conversion/:' -czvf $(PROJECT)-conversion.tar.gz $(SOURCES)

dist: $(PROJECT)-conversion.tar.gz

