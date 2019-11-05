# Test-suite makefile for reposurgeon

# By setting the REPOSURGEON environment variable and using -e
# a different implementation can be plugged in to the tests.

# Use absolute path so tests that change working directory still use 
# scripts from parent directory.  Note that using $PWD seems to fail
# here under Gitlab's CI environment.
PATH := $(realpath ..):$(realpath .):${PATH}
REPOSURGEON := reposurgeon 
REPOCUTTER := repocutter 
REPOTOOL := repotool 
REPOMAPPER := repomapper

# Setting this to 0 allows tests to continue on error.
STOPOUT=1

# Force pure serial execution when rebuilding check files.  Slower,
# but makes them deterministic and may help smoke out bugs in
# concurrent code.
BUILDOPT="'set serial'"

# Defeat annoying behavior under Mac OS X - builtin echo doesn't do -n
ECHO := /bin/echo

# Without this, under CentOS Python may emit invisible ANSI strings
# that confuse diff.  Leave this in while pyreposurgeon still exists.
TERM := dumb

default: check

# Define test groups
BASIC = listcheck roundtrip roundtrip-compress messagebox fi-regress coalesce
SUBVERSION = svnload-regress liftcheck-regress legacy-regress svncheck-regress
GIT_EXTRACTOR = git-regress git-regress-branches git-regress-merges git-regress-tags
HG_EXTRACTOR = hg-regress hg-regress-branches hg-regress-merges hg-regress-tags
AUXTOOLS = repocutter-regress repomapper-regress repotool-regress

check: clean $(BASIC) $(SUBVERSION) $(GIT_EXTRACTOR) $(HG_EXTRACTOR) $(AUXVERSION)
	@echo "=== No diff output is good news ==="

# hg-regress-patho is not part of the normal test sequence.

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
	repotool-buildregress

clean:
	rm -fr .rs* test-repo test-checkout git-repo left-repo right-repo *~

options:
	@echo "REPOSURGEOM is $(REPOSURGEOM)"
	@echo "TESTOPT is $(TESTOPT)"

# Show summary lines for all tests.
testlist:
	@grep --text '^##' *.tst
	@grep --text '^ ##' *.svn
listcheck:
	@for f in *.tst *.svn; do \
	    if ( head -3 $$f | grep --text -q '^ *##' ); then :; else echo "$$f needs a description"; fi; \
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
	    if $(REPOSURGEON) "$(TESTOPT)" "script $${file}.tst testing123" >/tmp/regress$$$$ 2>&1; \
	    then diff --text -u $${file}.chk /tmp/regress$$$$ || exit $(STOPOUT); \
	    else echo "*** Nonzero return status on $${file}!"; exit $(STOPOUT); fi \
	done
	@rm -f /tmp/regress$$$$
fi-regress-tighten:
	@echo "=== Running general tests with tighten option:"
	@for file in $(TESTLOADS); do \
	    $(ECHO) -n "  $${file} "; grep --text '##' $${file}.tst  || echo ' ## (no description)'; \
	    if $(REPOSURGEON) "$(TESTOPT)" "set tighten" "script $${file}.tst testing123" >/tmp/regress$$$$ 2>&1; \
	    then diff --text -u $${file}.chk /tmp/regress$$$$ || exit $(STOPOUT); \
	    else echo "*** Nonzero return status on $${file}!"; exit $(STOPOUT); fi \
	done
	@rm -f /tmp/regress$$$$

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
	    $(REPOSURGEON) "$(TESTOPT)" "read <$${file}.fi; coalesce; write -" \
		>/tmp//regress$$$$ || exit $(STOPOUT); \
	    [ -s /tmp/regress$$$$ ] && diff --text -u $${file}.chk /tmp/regress$$$$ \
		|| exit $(STOPOUT); \
	done
	@rm -f /tmp/regress$$$$

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
		(if { $(ECHO) -n "  $${test}.svn"; grep --text '^ ##' $${test}.svn || echo ' ## (no description)'; } >&2; \
		$(REPOSURGEON) "$(TESTOPT)" "$(TESTOPT)" "read <$${test}.svn" "prefer git" "write -" >/tmp/regress$$$$ 2>&1; \
		then diff --text -u $${test}.chk /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi; \
		if command -v git >/dev/null 2>&1 ; \
		then \
		    mkdir /tmp/reposurgeon$$$$ || exit $(STOPOUT); \
		    (cd /tmp/reposurgeon$$$$ || exit $(STOPOUT); \
			git init --quiet || exit $(STOPOUT); \
			grep --text -v 'reposurgeon:' /tmp/regress$$$$ | git fast-import --quiet) \
			    || exit $(STOPOUT); \
		    rm -fr /tmp/reposurgeon$$$$\
		else echo "    Skipped, git missing."; \
		fi \
		) || exit $(STOPOUT); \
	    fi \
	done
	@rm -f /tmp/regress$$$$

# Perform full regression on SVN streams that have clean conversions -
# that is, no messages due to branch surgery or whatever.
# Empty-commit tags generated in gitspace corresponding to branch
# copies are ignored.
# FIXME: We should report error and stop if the outout is nonempty.
SVNCLEAN := bad-author.svn binary.svn blob-id.svn debranch.svn deletion.svn \
	deepdirs.svn emptybranch.svn executable.svn expunge.svn filecopy.svn \
	format7.svn gitify.svn ignore-blank.svn mergeinfo.svn mergeinfo-with-split.svn \
	mixedbranch.svn mkignore.svn nullignores.svn nontipcopy.svn \
	pangram.svn permcopy.svn replace-dir.svn simpletag.svn smallref.svn \
	snarl.svn squash-id.svn subdir.svn subclipse.svn svnignores.svn
liftcheck-regress:
	@echo "== Testing conversion correctness of Subversion streams:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if  command -v git >/dev/null 2>&1 &&  command -v svn >/dev/null 2>&1; \
	then \
		for test in $(SVNCLEAN); \
		do \
		    { $(ECHO) -n "  $${test}"; grep --text '^ ##' $${test} || echo ' ## (no description)'; } >&2; \
		    liftcheck -e emptycommit $${test} || { echo "*** Failed on $${test}!"; exit $(STOPOUT); } \
		done \
	else \
		echo "     Skipped, either git or svn is missing"; \
	fi

# List Subversion streams that don't convert clean 
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

# Check idempotency of read/dump/read on Subversion repos
# This can only succeed for linear repos.  At the moment it fails on
# all repos.
SVNCHECK=pangram
svncheck:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for test in $(SVNCHECK); \
	do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		svn-to-svn -s <$${test}.svn >/tmp/checkstripped$$$$ 2>&1 \
		    || exit $(STOPOUT); \
		if echo "  $${test}.svn" >&2; \
		$(REPOSURGEON) "$(TESTOPT)" "set svn_no_autoignores" "read $${test}.svn" "prefer svn" "write -"  | svn-to-svn -s >/tmp/stripped$$$$ 2>&1; \
		then diff --text -u /tmp/checkstripped$$$$ /tmp/stripped$$$$ \
		    || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi;\
	    fi \
	done
	@make --quiet clean
	@rm -f /tmp/prestripped$$$$ /tmp/stripped$$$$ /tmp/checkstripped$$$$

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
