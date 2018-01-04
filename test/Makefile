# Test-suite makefile for reposurgeon

# By setting the REPOSURGEON environment variable and using -e
# a different implementation can be plugged in to the tests.

# Use absolute path so tests that change working directory still use 
# scripts from parent directory.  Note that using $PWD seems to fail
# here under Gitlab's CI environment.
PATH := $(realpath ..):$(realpath .):${PATH}
REPOSURGEON := reposurgeon 

# Defeat annoying behavior under Mac OS X - builtin echo doesn't do -n
ECHO := /bin/echo

# Without this, under CentOS Python may emit invisible ANSI strings
# that confuse diff
TERM := dumb

default: check

# Speed check - test under the default in the hashbang line
check:
	@if command -v pylint >/dev/null 2>&1; then echo "=== Running pylint" && (cd ..; make -e --quiet pylint); else echo "pylint missing; skipping tests"; fi
	@echo "=== Running built-in tests"
	@$(REPOSURGEON) "runtests"
	@if ./setpypy pypy; then time make -e --quiet all; else echo "pypy missing; skipping tests"; fi

# Portability check - tests all dialects
portcheck: check
	@if ./setpypy python2; then time make -e --quiet all; else echo "python2 missing; skipping tests"; fi
	@if ./setpypy python3; then time make -e --quiet all; else echo "python3 missing; skipping tests"; fi
	@./setpypy pypy

all: listcheck roundtrip roundtrip-compress mailboxing fi-regress coalesce \
		git-regress git-regress-branches git-regress-merges git-regress-tags \
		hg-extractor svnload-regress legacy-regress svndump-regress \
		repodiffer-regress repomapper-regress \
		repotool-regress repocutter-regress svncheck-regress
	@echo "=== No diff output is good news."

hg-extractor: hg-regress hg-regress-branches hg-regress-merges \
		hg-regress-tags hg-regress-patho

.SUFFIXES: .svn .chk .fi .map

.svn.chk:
	$(REPOSURGEON) "read <$<" "prefer git" "write -" >$@ 2>&1
.svn.fi:
	$(REPOSURGEON) "read <$<" "prefer git" "write -" >$@
.svn.map:
	$(REPOSURGEON) "read <$<" "legacy write -" >$@

buildregress: fi-buildregress svnload-buildregress legacy-buildregress \
	svndump-buildregress repodiffer-buildregress repomapper-buildregress \
	repotool-buildregress repocutter-buildregress hg-buildregress-branches \
	hg-buildregress-patho svncheck-buildregress

clean:
	rm -fr .rs* test-repo test-checkout git-repo left-repo right-repo *~

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
	    $(REPOSURGEON) "read -;write -" <$$file >/tmp/rs$$$$ || exit 1; \
	    [ -s /tmp/rs$$$$ ] && diff --text -u $${file} /tmp/rs$$$$ \
		|| exit 1; \
	    rm -f /tmp/rs$$$$ || exit 1; \
	done

# Test that all stream files round-trip properly with compression
roundtrip-compress:
	@echo "=== Testing stream-file round-tripping with compression:" 
	@for file in *.fi; do \
	    echo "  $${file}"; \
	    $(REPOSURGEON) "set compressblobs" "read -;write -" \
		<$$file >/tmp/rs$$$$ || exit 1; \
	    [ -s /tmp/rs$$$$ ] && diff --text -u $${file} /tmp/rs$$$$ \
		|| exit 1; \
	    rm -f /tmp/rs$$$$ || exit 1; \
	done

# Test that dumping metadata to mailbox form and updating from the mailbox
# is idempotent if you make no changes to the mailbox.
mailboxing:
	@echo "=== Testing mailbox-out/mailbox-in roundtripping:"
	@for file in *.fi; do \
	    echo "  $${file}";\
	    $(REPOSURGEON) "read <$${file}" "edit echo>/dev/null" "write -" \
		>/tmp/regress$$$$ || exit 1; \
	    [ -s /tmp/regress$$$$ ] && diff --text -u $${file} /tmp/regress$$$$ \
		|| exit 1; \
	done
	@rm -f /tmp/regress$$$$

# General regression testing of commands and output; look at the *.tst and
# corresponding *.chk files to see which tests this runs.
TESTLOADS := $(shell ls -1 *.tst | sed '/.tst/s///')
fi-buildregress:
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    $(REPOSURGEON) "script $${file}.tst testing123" >$${file}.chk \
		2>&1 || exit 1; \
	done
fi-regress:
	@echo "=== Running general tests:"
	@for file in $(TESTLOADS); do \
	    $(ECHO) -n "  $${file} "; grep --text '##' $${file}.tst  || echo ' ## (no description)'; \
	    if $(REPOSURGEON) "script $${file}.tst testing123" >/tmp/regress$$$$ 2>&1; \
	    then diff --text -u $${file}.chk /tmp/regress$$$$ || exit 1; \
	    else echo "*** Nonzero return status on $${file}!"; exit 1; fi \
	done
	@rm -f /tmp/regress$$$$

# Test coalescence operation.
COALESCE=uncoalesced
buildcoalesce:
	@for file in $(COALESCE); do \
	    echo "Rebuilding coalescence regression test using $${file}.fi"; \
	    $(REPOSURGEON) "read <$${file}.fi; coalesce; write -" \
		>$${file}.chk || exit 1; \
	done
	@rm -f /tmp/regress$$$$
coalesce:
	@echo "=== Coalescence regression test:"
	@for file in $(COALESCE); do \
	    echo "  $${file}.fi"; \
	    $(REPOSURGEON) "read <$${file}.fi; coalesce; write -" \
		>/tmp/regress$$$$ || exit 1; \
	    [ -s /tmp/regress$$$$ ] && diff --text -u $${file}.chk /tmp/regress$$$$ \
		|| exit 1; \
	done
	@rm -f /tmp/regress$$$$

# Test the git extractor
GITLOADS = bs
git-regress:
	@echo "=== Testing git-extractor:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(GITLOADS); do \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the git extractor with multiple git branches
GITBRANCHES = be bb
git-regress-branches:
	@echo "=== Testing git-extractor with multiple git branches:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(GITBRANCHES); do \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the git extractor with merges
GITMERGES = be2 be3 be4 be5 be6
git-regress-merges:
	@echo "=== Testing git-extractor with merges:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(GITMERGES); do \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the git extractor with tags
GITTAGS = bt bt2
git-regress-tags:
	@echo "=== Testing git-extractor with tags:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(GITTAGS); do \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor
HGLOADS = testrepo2
hg-regress:
	@echo "=== Testing hg-extractor:"
	@if command -v hg >/dev/null 2>&1 && command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(HGLOADS); do \
		if (echo "  $${test}.fi" >&2; \
		./hg-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, hg or git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with multiple hg branches
# NOTE: the bb-alt test demonstrates an hg repo with coloring that git cannot reproduce
HGBRANCHES = be be2 be3 bb-alt be-bookmarks
hg-buildregress-branches:
	@for file in $(HGBRANCHES); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit 1; \
	done
hg-regress-branches:
	@echo "=== Testing hg-extractor with multiple hg branches:"
	@if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGBRANCHES); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with merges
HGMERGES = be2 be3 be4 be5 be6
hg-buildregress-merges:
	@for file in $(HGMERGES); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit 1; \
	done
hg-regress-merges:
	@echo "=== Testing hg-extractor with merges:"
	@if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGMERGES); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with tags
HGTAGS = bt bt2
hg-buildregress-tags:
	@for file in $(HGTAGS); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit 1; \
	done
hg-regress-tags:
	@echo "=== Testing hg-extractor with tags:"
	@if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGTAGS); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with pathological loads
HGPATHO = be-subrepo be-subrepo2
hg-buildregress-patho:
	@for file in $(HGPATHO); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test 2>/dev/null | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit 1; \
	done
hg-regress-patho:
	@echo "=== Testing hg-extractor with pathological loads:"
	@if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGPATHO); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test 2>/dev/null) | sed -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test loading from Subversion
SVNLOADS := $(shell ls *.svn | sed '/.svn/s///')
svnload-buildregress:
	@for test in $(SVNLOADS); do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		    echo "Remaking $${test}.chk"; \
		    rm -f $${test}.chk && make --quiet $${test}.chk \
			|| exit 1; \
	    fi \
	done
svnload-regress:
	@echo "== Testing loading of Subversion streams:"
	@for test in $(SVNLOADS); \
	do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		(if { $(ECHO) -n "  $${test}.svn"; grep --text '^ ##' $${test}.svn || echo ' ## (no description)'; } >&2; \
		$(REPOSURGEON) "read <$${test}.svn" "prefer git" "write -" >/tmp/regress$$$$ 2>&1; \
		then diff --text -u $${test}.chk /tmp/regress$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi; \
		if command -v git >/dev/null 2>&1 ; \
		then \
		    mkdir /tmp/reposurgeon$$$$ || exit 1; \
		    (cd /tmp/reposurgeon$$$$ || exit 1; \
			git init --quiet || exit 1; \
			grep --text -v 'reposurgeon:' /tmp/regress$$$$ | git fast-import --quiet) \
			    || exit 1; \
		    rm -fr /tmp/reposurgeon$$$$\
		else echo "    Skipped, git missing."; \
		fi \
		) || exit 1; \
	    fi \
	done
	@rm -f /tmp/regress$$$$

REFLOADS=references mergeinfo-with-split
legacy-buildregress:
	@for test in $(REFLOADS); \
	do \
	    echo "Remaking $${test}.map"; \
	    rm -f $${test}.map && make --quiet $${test}.map 2>/dev/null \
		|| exit 1; \
	done
legacy-regress:
	@echo "=== Testing legacy-map generation:"
	@for test in $(REFLOADS); \
	do \
	    if echo "  $${test}.svn" >&2; \
	    $(REPOSURGEON) "read <$${test}.svn" "legacy write -" >/tmp/regress$$$$ 2>/dev/null; \
	    then diff --text -u $${test}.map /tmp/regress$$$$ || exit 1; \
	    else echo "*** Nonzero return status on $${test}!"; exit 1; fi; \
	done
	@rm -f /tmp/regress$$$$

# Test dumping to Subversion
DUMPLOADS=bs svnfodder
svndump-buildregress:
	@for f in $(DUMPLOADS); \
	do \
	    echo "Remaking $${f}.chk"; \
	    $(REPOSURGEON) "read <$${f}.fi" "prefer svn" "write -" | svn-to-svn -s >$${f}.chk \
		|| exit 1; \
	done
	@make --quiet clean
svndump-regress:
	@echo "=== Test dumping of Subversion streams:"
	@for test in $(DUMPLOADS); \
	do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		if echo "  $${test}.fi" >&2; \
		$(REPOSURGEON) "read <$${test}.fi" "prefer svn" "write -" | tee /tmp/prestripped$$$$ | svn-to-svn -s >/tmp/stripped$$$$ 2>&1; \
		then diff --text -u $${test}.chk /tmp/stripped$$$$ || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi;\
	    fi \
	done
	@make --quiet clean
	@rm -f /tmp/prestripped$$$$ /tmp/stripped$$$$

# Check idempotency of read/dump/read on Subversion repos
# This can only succeed for linear repos.  At the moment it fails on
# all repos.
SVNCHECK=pangram
svncheck:
	@for test in $(SVNCHECK); \
	do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		svn-to-svn -s <$${test}.svn >/tmp/checkstripped$$$$ 2>&1 \
		    || exit 1; \
		if echo "  $${test}.svn" >&2; \
		$(REPOSURGEON) "set svn_no_autoignores" "read $${test}.svn" "prefer svn" "write -"  | svn-to-svn -s >/tmp/stripped$$$$ 2>&1; \
		then diff --text -u /tmp/checkstripped$$$$ /tmp/stripped$$$$ \
		    || exit 1; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi;\
	    fi \
	done
	@make --quiet clean
	@rm -f /tmp/prestripped$$$$ /tmp/stripped$$$$ /tmp/checkstripped$$$$

# Regression-testing of repodiffer; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
REPODIFFER := $(shell ls -1 repodiffer*.sh | sed '/.sh/s///')
repodiffer-buildregress:
	@for file in $(REPODIFFER); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk || exit 1; \
	done
repodiffer-regress:
	@echo "=== Running repodiffer tests:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
	    for file in $(REPODIFFER); do \
		$(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)'; \
		$(SHELL) $${file}.sh | diff --text -u $${file}.chk - || exit 1; \
	    done; \
	else echo "    Skipped, git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Regression-testing of repomapper; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
REPOMAPPER := $(shell ls -1 repomapper*.sh | sed '/.sh/s///')
repomapper-buildregress:
	@for file in $(REPOMAPPER); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk || exit 1; \
	done
repomapper-regress:
	@echo "=== Running repomapper tests:"
	@for file in $(REPOMAPPER); do \
	    $(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh | diff --text -u $${file}.chk - || exit 1; \
	done
	@rm -f /tmp/regress$$$$

# Regression-testing of repotool; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
REPOTOOL := $(shell ls -1 repotool*.sh | sed '/.sh/s///')
repotool-buildregress:
	@for file in $(REPOTOOL); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh --rebuild $${file} || exit 1; \
	done
repotool-regress:
	@echo "=== Running repotool tests:"
	@for file in $(REPOTOOL); do \
	    $(ECHO) -n "  $${file} "; grep '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh --regress $${file} || exit 1; \
	done

# Regression-testing of repocutter; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
REPOCUTTER := $(shell ls -1 repocutter*.sh | sed '/.sh/s///')
repocutter-buildregress:
	@for file in $(REPOCUTTER); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk || exit 1; \
	done
repocutter-regress:
	@echo "=== Running repocutter tests:"
	@for file in $(REPOCUTTER); do \
	    $(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh | diff --text -u $${file}.chk - || exit 1; \
	done
	@rm -f /tmp/regress$$$$

# Regression-testing of Subversion permission-bit cases; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
SVNCHECK := $(shell ls -1 svncheck*.sh | sed '/.sh/s///')
svncheck-buildregress:
	@for file in $(SVNCHECK); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh -d | $(REPOSURGEON) "set testmode" 'read -' 'prefer git' 'write -' >$${file}.chk || exit 1; \
	done
svncheck-regress:
	@echo "=== Running svncheck tests:"
	@for file in $(SVNCHECK); do \
	    $(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh -d | $(REPOSURGEON) "set testmode" 'read -' 'prefer git' 'write -' | diff --text -u $${file}.chk - || exit 1; \
	done
	@rm -f /tmp/regress$$$$

# Test productions end here.

# The result from this is checked in because, as it turns out, the order
# in which the components are archived cab vary randomly based on the
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
	@cd test-checkout || exit 1; set -x; \
		svn mkdir trunk || exit 1; \
		svn mkdir tags || exit 1; \
		svn mkdir branches || exit 1; \
		echo "Directory layout." | svn commit -F - || exit 1; \
		echo "This is a test Subversion repository" >trunk/README; \
		svn add trunk/README || exit 1; \
		echo "Initial README content." | svn commit -F - || exit 1
svn-dump:
	@svnadmin dump test-repo 

# end
