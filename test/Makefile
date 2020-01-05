# Test-suite makefile for reposurgeon

# By setting the REPOSURGEON environment variable and using -e
# a different implementation can be plugged in to the tests.

# Use absolute path so tests that change working directory still use 
# scripts from parent directory.  Note that using $PWD seems to fail
# here under Gitlab's CI environment.
PATH := $(realpath ..):$(realpath .):${PATH}
REPOSURGEON := reposurgeon 
REPOCUTTER := repocutter 
REPOTOOL := repotool EPOMAPPER := repomapper

# Setting this to 0 allows tests to continue on error.
STOPOUT=1

# Setting this to 1 suppresses diffs in favor of a FAIL tag
QUIET=0

# Force pure serial execution when rebuilding check files.  Slower,
# but makes them deterministic and may help smoke out bugs in
# concurrent code.
BUILDOPT="'set serial'"

# Defeat annoying behavior under Mac OS X - builtin echo doesn't do -n
ECHO := /bin/echo

# Without this, under CentOS Python may emit invisible ANSI strings
# that confuse diff.  Leave this in while pyreposurgeon still exists.
TERM := dumb

default: fastcheck

# Define test groups
BASIC = listcheck roundtrip roundtrip-compress messagebox fi-regress coalesce
SUBVERSION = svnload-regress liftcheck-regress legacy-regress svncheck-regress
FULLSUBVERSION = $(SUBVERSION) liftcheck-fullregress
GIT_EXTRACTOR = git-regress git-regress-branches git-regress-merges git-regress-tags
HG_EXTRACTOR = hg-regress hg-regress-branches hg-regress-merges hg-regress-tags \
	hg-regress-patho
AUXTOOLS = repocutter-regress repomapper-regress repotool-regress

# If we have GNU parallel available, the tests can exploit multiple processors
RUNNER = $(shell if type parallel >/dev/null 2>&1; then echo "parallel"; else echo "xargs"; fi)

# This series can change depending on the current development focus
fastcheck: clean $(BASIC) $(SUBVERSION)
	@echo "=== No diff output is good news ==="

# This should always be a full test
fullcheck: clean $(BASIC) $(SUBVERSION) $(GIT_EXTRACTOR) $(HG_EXTRACTOR) $(AUXTOOLS)
	@echo "=== No diff output is good news ==="

# FIXME: is log -all really correct when regeneting the map checks?

.SUFFIXES: .svn .chk .fi .map

.svn.chk:
	$(REPOSURGEON) "read <$<" "prefer git" "write -" >$@ 2>&1
.svn.fi:
	$(REPOSURGEON) "read <$<" "prefer git" "write -" >$@
.svn.map:
	$(REPOSURGEON) "log -all" "read <$<" "legacy write -" >$@

buildregress: fi-buildregress svnload-buildregress legacy-buildregress \
	repomapper-buildregress repotool-buildregress hg-buildregress-branches \
	svncheck-buildregress repocutter-buildregress repomapper-buildregress \
	repotool-buildregress buildcoalesce

clean:
	rm -fr .rs* test-repo test-checkout git-repo left-repo right-repo *~

options:
	@echo "REPOSURGEOM is $(REPOSURGEOM)"
	@echo "TESTOPT is $(TESTOPT)"

runner:
	@echo $(RUNNER)

# Show summary lines for all tests.
testlist:
	@grep --text '^##' *.tst
	@grep --text '^ ##' *.svn
listcheck:
	@for f in *.tst *.svn; do \
	    if ( head -3 $$f | grep --text -q '^ *##' ); then :; else echo "$$f needs a description" >&2; exit $(STOPOUT); fi;  \
	done

# Test that all stream files round-trip properly
roundtrip:
	@echo "=== Testing stream-file round-tripping:" 
	@for file in *.fi; do \
	    echo "  $${file}"; \
	    $(REPOSURGEON) "$(TESTOPT)" "read -;write -" <$$file >/tmp/rs$$$$ || exit $(STOPOUT); \
	    [ -s /tmp/rs$$$$ ] && diff --text -u $${file} /tmp/rs$$$$ \
		|| exit $(STOPOUT); \
	    rm -f /tmp/rs$$$$ || exit $(STOPOUT); \
	done

# Test that all stream files round-trip properly with compression
roundtrip-compress:
	@echo "=== Testing stream-file round-tripping with compression:" 
	@for file in *.fi; do \
	    echo "  $${file}"; \
	    $(REPOSURGEON) "$(TESTOPT)" "set compressblobs" "read -;write -" \
		<$$file >/tmp/rs$$$$ || exit $(STOPOUT); \
	    [ -s /tmp/rs$$$$ ] && diff --text -u $${file} /tmp/rs$$$$ \
		|| exit $(STOPOUT); \
	    rm -f /tmp/rs$$$$ || exit $(STOPOUT); \
	done

# Test that dumping metadata to msgbox form and updating from the message-box
# is idempotent if you make no changes to the message-box.
messagebox:
	@echo "=== Testing msgout/msgin roundtripping:"
	@for file in *.fi; do \
	    echo "  $${file}";\
	    $(REPOSURGEON) "$(TESTOPT)" "read <$${file}" "edit echo>/dev/null" "write -" \
		>/tmp/regress$$$$ || exit $(STOPOUT); \
	    [ -s /tmp/regress$$$$ ] && diff --text -u $${file} /tmp/regress$$$$ \
		|| exit $(STOPOUT); \
	done
	@rm -f /tmp/regress$$$$

# General regression testing of commands and output; look at the *.tst and
# corresponding *.chk files to see which tests this runs.
TESTLOADS := $(shell ls -1 *.tst | sed '/.tst/s///')
fi-buildregress:
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    $(REPOSURGEON) "$(BUILDOPT)" "$(TESTOPT)" "script $${file}.tst testing123" >$${file}.chk \
		2>&1 || exit $(STOPOUT); \
	done
fi-regress:
	@echo "=== Running general tests:"
	@for file in $(TESTLOADS); do \
	    $(ECHO) -n "  $${file} "; grep --text '##' $${file}.tst  || echo ' ## (no description)'; \
	    $(REPOSURGEON) "$(TESTOPT)" "script $${file}.tst testing123" >/tmp/regress$$$$ 2>&1 \
		|| (echo "*** Nonzero return status on $${file}!"; exit $(STOPOUT) ); \
	    diff --text -u $${file}.chk /tmp/regress$$$$ >/tmp/diff$$$$; \
	    case $$? in \
	    0) ;; \
	    1) if [ $(QUIET) = 1 ]; then echo FAILED; else cat /tmp/diff$$$$; fi; if [ $(STOPOUT) = 1 ]; then exit 1; fi;; \
	    *) echo "*** diff had trouble, status $$?"; exit $(STOPOUT);; \
	    esac \
	done
	@rm -f /tmp/regress$$$$ /tmp/diff$$$$

# Test coalescence operation.
COALESCE=uncoalesced
buildcoalesce:
	@for file in $(COALESCE); do \
	    echo "Rebuilding coalescence regression test using $${file}.fi"; \
	    $(REPOSURGEON) "$(BUILDOPT)" "$(TESTOPT)" "read <$${file}.fi; coalesce; write -" \
		>$${file}.chk || exit $(STOPOUT); \
	done
	@rm -f /tmp/regress$$$$
coalesce:
	@echo "=== Coalescence regression test:"
	@for file in $(COALESCE); do \
	    echo "  $${file}.fi"; \
	    $(REPOSURGEON) "$(TESTOPT)" "read <$${file}.fi; coalesce; write -" >/tmp/regress$$$$ 2>&1  \
		|| (echo "*** Nonzero return status on $${file}!"; exit $(STOPOUT) ); \
	    diff --text -u $${file}.chk /tmp/regress$$$$ >/tmp/diff$$$$; \
	    case $$? in \
	    0) ;; \
	    1) if [ $(QUIET) = 1 ]; then echo FAILED; else cat /tmp/diff$$$$; fi; if [ $(STOPOUT) = 1 ]; then exit 1; fi;; \
	    *) echo "*** diff had trouble, status $$?"; exit $(STOPOUT);; \
	    esac \
	done
	@rm -f /tmp/regress$$$$ /tmp/diff$$$$

# Test the git extractor
GITLOADS = bs
git-regress:
	@echo "=== Testing git-extractor:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(GITLOADS); do \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the git extractor with multiple git branches
GITBRANCHES = be bb
git-regress-branches:
	@echo "=== Testing git-extractor with multiple git branches:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(GITBRANCHES); do \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the git extractor with merges
GITMERGES = be2 be3 be4 be5 be6
git-regress-merges:
	@echo "=== Testing git-extractor with merges:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(GITMERGES); do \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the git extractor with tags
GITTAGS = bt bt2
git-regress-tags:
	@echo "=== Testing git-extractor with tags:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(GITTAGS); do \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor
HGLOADS = testrepo2
hg-regress:
	@echo "=== Testing hg-extractor:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 && command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(HGLOADS); do \
		if (echo "  $${test}.fi" >&2; \
		./hg-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg or git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with multiple hg branches
# NOTE: the bb-alt test demonstrates an hg repo with coloring that git cannot reproduce
HGBRANCHES = be be2 be3 bb-alt be-bookmarks
hg-buildregress-branches:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT; BUILDOPT="$(BUILDOPT)"; export BUILDOPT;\
	for file in $(HGBRANCHES); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit $(STOPOUT); \
	done
hg-regress-branches:
	@echo "=== Testing hg-extractor with multiple hg branches:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGBRANCHES); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with merges
HGMERGES = be2 be3 be4 be5 be6
hg-buildregress-merges:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for file in $(HGMERGES); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit $(STOPOUT); \
	done
hg-regress-merges:
	@echo "=== Testing hg-extractor with merges:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGMERGES); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with tags
HGTAGS = bt bt2
hg-buildregress-tags:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT; BUILDOPT="$(BUILDOPT)"; export BUILDOPT;\
	for file in $(HGTAGS); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit $(STOPOUT); \
	done
hg-regress-tags:
	@echo "=== Testing hg-extractor with tags:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGTAGS); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with pathological loads
HGPATHO = be-subrepo be-subrepo2
hg-buildregress-patho:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT; BUILDOPT="$(BUILDOPT)"; export BUILDOPT;\
	for file in $(HGPATHO); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test 2>/dev/null | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit $(STOPOUT); \
	done
hg-regress-patho:
	@echo "=== Testing hg-extractor with pathological loads:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGPATHO); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test 2>/dev/null) | sed -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test loading from Subversion
SVNLOADS := $(shell ls *.svn | sed '/.svn$$/s///')
svnload-buildregress:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for test in $(SVNLOADS); do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		    echo "Remaking $${test}.chk"; \
		    rm -f $${test}.chk && make --quiet $${test}.chk \
			|| exit $(STOPOUT); \
	    fi \
	done
svnload-regress:
	@echo "== Testing loading of Subversion streams:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT; BUILDOPT="$(BUILDOPT)"; export BUILDOPT;\
	for test in $(SVNLOADS); \
	do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		{ $(ECHO) -n "  $${test}.svn"; grep --text '^ ##' $${test}.svn || echo ' ## (no description)'; } >&2; \
		$(REPOSURGEON) "$(TESTOPT)" "$(TESTOPT)" "read <$${test}.svn" "prefer git" "write -" >/tmp/regress$$$$ 2>&1 \
		    || (echo "*** Nonzero return status on $${file}!"; exit $(STOPOUT) ); \
		diff --text -u $${test}.chk /tmp/regress$$$$ >/tmp/diff$$$$; \
		case $$? in \
		0) ;; \
		1) if [ $(QUIET) = 1 ]; then echo FAILED; else cat /tmp/diff$$$$; fi; if [ $(STOPOUT) = 1 ]; then exit 1; fi;; \
		*) echo "*** diff had trouble, status $$?"; exit $(STOPOUT);; \
		esac; \
		if command -v git >/dev/null 2>&1 ; \
		then \
		    mkdir /tmp/reposurgeon$$$$ || exit $(STOPOUT); \
		    (cd /tmp/reposurgeon$$$$ || exit $(STOPOUT); \
			git init --quiet || exit $(STOPOUT); \
			grep --text -v 'reposurgeon:' /tmp/regress$$$$ | git fast-import --quiet) \
			    || exit $(STOPOUT); \
		    rm -fr /tmp/reposurgeon$$$$\
		else \
		    echo "    Skipped, git missing."; \
		fi \
	    fi \
	done
	@rm -f /tmp/regress$$$$

# Perform full regression on SVN streams that have clean conversions -
# that is, no messages due to branch surgery or whatever.
# Empty-commit tags generated in gitspace corresponding to branch
# copies are ignored.
SVNCLEAN := \
	agito.svn \
	attrws.svn \
	authortz.svn \
	bad-author.svn \
	badattrib.svn \
	badattrib2.svn \
	binary.svn \
	blob-id.svn \
	branchreplace.svn \
	branch-drop-add.svn \
	cherry-pick.svn \
	cvstag.svn \
	debranch.svn \
	deepdirs.svn \
	delete-rename.svn \
	deletion.svn \
	delignore.svn \
	delref.svn \
	dircopyprop.svn \
	emptycommit-merge.svn \
	emptyfrom.svn \
	executable.svn \
	expunge-copyfrom.svn \
	expunge.svn \
	filecopy.svn \
	fleetwood.svn \
	format7.svn \
	gitify.svn \
	gitignore.svn \
	ignore-blank.svn \
	lint.svn \
	mergeinfo-combine.svn \
	mergeinfo-grandparent.svn \
	mergeinfo-trunkstomp.svn \
	mergeinfo-with-split.svn \
	mergeinfo.svn \
	mixedbranch.svn \
	mkignore.svn \
	myers1.svn \
	node-kind-first.svn \
	no-forward-merge.svn \
	no-merge.svn \
	nontipcopy.svn \
	nullignores.svn \
	pangram.svn \
	permcopy1.svn \
	permcopy2.svn \
	permcopy3.svn \
	permcopy4.svn \
	references.svn \
	replace-dir.svn \
	rootfirst.svn \
	samplebranch.svn \
	simpletag.svn \
	smallref.svn \
	snarl.svn \
	split-dir.svn \
	squash-id.svn \
	subclipse.svn \
	subdir.svn \
	svnignores.svn \
	symlink.svn \
	tagpollute.svn \
	tagsimple.svn \
	tagsimpledelete.svn \
	treecontents.svn \
	trunkstomp.svn \
	vanilla.svn \
	wrong-mergeinfo.svn \

liftcheck-regress:
	@echo "== Testing conversion correctness of Subversion streams at head revision:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if  command -v git >/dev/null 2>&1 &&  command -v svn >/dev/null 2>&1; \
	then \
		for test in $(SVNCLEAN); \
		do \
		    liftcheck -e emptycommit $${test} >/tmp/diff$$$$; \
		    case $$? in \
		    0) ;; \
		    1) if [ $(QUIET) = 1 ]; then echo FAILED; else cat /tmp/diff$$$$; fi; if [ $(STOPOUT) = 1 ]; then exit 1; fi;; \
		    *) echo "*** liftcheck had trouble, status $$?"; exit $(STOPOUT);; \
		    esac \
		done \
	else \
		echo "     Skipped, either git or svn is missing"; \
	fi; \
	rm -f /tmp/diff$$$

# This is not part of the normal test sequence becausr the reposurgeon tools are very slow.
liftcheck-fullregress:
	@echo "== Testing conversion correctness of all SVN revisions:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if  command -v git >/dev/null 2>&1 &&  command -v svn >/dev/null 2>&1; \
	then \
		for test in *.svn; \
		do \
		    liftcheck -q -r all $${test} || { echo "*** Failed on $${test}!"; exit $(STOPOUT); } \
		done \
	else \
		echo "     Skipped, either git or svn is missing"; \
	fi


# List Subversion streams that don't convert clean without -q -r all
liftcheck-dirty:
	@for x in $(SVNCLEAN); do echo $${x} >>goodlist$$; done
	@sort -o goodlist$$ goodlist$$
	@ls *.svn | comm -23 - goodlist$$
	@rm goodlist$$

REFLOADS=references mergeinfo-with-split
legacy-buildregress:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for test in $(REFLOADS); \
	do \
	    echo "Remaking $${test}.map"; \
	    rm -f $${test}.map && make --quiet $${test}.map 2>/dev/null \
		|| exit $(STOPOUT); \
	done
legacy-regress:
	@echo "=== Testing legacy-map generation:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for test in $(REFLOADS); \
	do \
	    if echo "  $${test}.svn" >&2; \
	    $(REPOSURGEON) "$(TESTOPT)" "read <$${test}.svn" "legacy write -" | grep -v '^reposurgeon:' >/tmp/regress$$$$ 2>/dev/null; \
	    then diff --text -u $${test}.map /tmp/regress$$$$ || exit $(STOPOUT); \
	    else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi; \
	done
	@rm -f /tmp/regress$$$$

# Regression-testing of repomapper; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
MAPPERTESTS := $(shell ls -1 repomapper*.sh | sed '/.sh/s///')
repomapper-buildregress:
	@REPOMAPPER=$$REPOMAPPER; export REPOMAPPER; \
	for file in $(MAPPERTESTS); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk || exit $(STOPOUT); \
	done
repomapper-regress:
	@echo "=== Running repomapper tests:"
	@REPOMAPPER=$$REPOMAPPER; export REPOMAPPER; \
	status=0; \
	for file in $(MAPPERTESTS); do \
	    $(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh | diff --text -u $${file}.chk - || status=1; \
	done; \
	exit $${status}
	@rm -f /tmp/regress$$$$

# Regression-testing of repotool; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
TOOLTESTS := $(shell ls -1 repotool*.sh | sed '/.sh/s///')
repotool-buildregress:
	@REPOTOOL=$$REPOTOOL; export REPOTOOL; \
	for file in $(TOOLTESTS); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh --rebuild $${file} || exit $(STOPOUT); \
	done
repotool-regress:
	@echo "=== Running repotool tests:"
	@REPOTOOL=$$REPOTOOL; export REPOTOOL; \
	status=0; \
	for file in $(TOOLTESTS); do \
	    $(ECHO) -n "  $${file} "; grep '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh --regress $${file} || status=1; \
	done; \
	exit $${status}


# Regression-testing of repocutter; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
CUTTERTESTS := $(shell ls -1 repocutter*.sh | sed '/.sh/s///')
repocutter-buildregress:
	@REPOMAPPER=$$REPOMAPPER; export REPOMAPPER; \
	for file in $(CUTTERTESTS); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk || exit $(STOPOUT); \
	done
repocutter-regress:
	@echo "=== Running repocutter tests:"
	@REPOCUTTER=$$REPOCUTTER; export REPOCUTTER; \
	status=0; \
	for file in $(CUTTERTESTS); do \
	    $(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh | diff --text -u $${file}.chk - || status=1; \
	done; \
	exit $${status}
	@rm -f /tmp/regress$$$$

# Regression-testing of Subversion permission-bit cases; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
SVNCHECK := $(shell ls -1 svncheck*.sh | sed '/.sh/s///')
svncheck-buildregress:
	@for file in $(SVNCHECK); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh -d | $(REPOSURGEON) "$(TESTOPT)" "set testmode" 'read -' 'prefer git' 'write -' >$${file}.chk || exit $(STOPOUT); \
	done
svncheck-regress:
	@echo "=== Running svncheck tests:"
	@status=0; \
	if command -v svn >/dev/null 2>&1 ; \
	then \
	    for file in $(SVNCHECK); do \
		$(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)'; \
		$(SHELL) $${file}.sh -d | $(REPOSURGEON) "$(TESTOPT)" "set testmode" 'read -' 'prefer git' 'write -' | diff --text -u $${file}.chk - || status=1; \
	    done; \
	else echo "    Skipped, svn missing."; exit 0; \
	fi; \
	exit $${status}
	@rm -f /tmp/regress$$$$

# Test productions end here.

# The result from this is checked in because, as it turns out, the order
# in which the components are archived can vary randomly based on the
# state of the filesystem when it is built.
make-tarball:
	mkdir -p /tmp/tarball
	echo "first sample small file" >/tmp/tarball/snip
	echo "second sample small file" >/tmp/tarball/snap
	chmod a+x /tmp/tarball/snap
	here=`pwd`
	(cd /tmp; tar cf sample.tar tarball)
	mv /tmp/sample.tar .

# Make a new repo and checkout directory to create a Subversion test load.
# Reminder - a branch copy looks like this:
# svn copy file://$PWD/test-repo/trunk file://$PWD/test-repo/branches/foo
# or, within test-checkout, svn copy ^/trunk ^/branches/foo
svn-flat: clean
	svnadmin create test-repo
	svn co file://${PWD}/test-repo test-checkout
svn-branchy: svn-flat
	@cd test-checkout || exit $(STOPOUT); set -x; \
		svn mkdir trunk || exit $(STOPOUT); \
		svn mkdir tags || exit $(STOPOUT); \
		svn mkdir branches || exit $(STOPOUT); \
		echo "Directory layout." | svn commit -F - || exit $(STOPOUT); \
		echo "This is a test Subversion repository" >trunk/README; \
		svn add trunk/README || exit $(STOPOUT); \
		echo "Initial README content." | svn commit -F - || exit $(STOPOUT)
svn-dump:
	@svnadmin dump test-repo 

# end
