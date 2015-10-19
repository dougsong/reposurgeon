# Test-suite makefile for reposurgeon

# By setting the REPOSURGEON environment variable and using -e
# a different implementation can be plugged in to the tests.

PATH := ..:.:${PATH}
REPOSURGEON = reposurgeon 

# Defeat annoying behavior under Mac OS X - builtin echo doesn't do -n
ECHO=/bin/echo

# Without this, under CentOS Python may emit invisible ANSI strings
# that confuse diff
TERM := dumb

default:
	@(cd ..; make -e --quiet pylint)
	@$(REPOSURGEON) "runtests"
	@make -e --quiet all

all: listcheck roundtrip mailboxing fi-regress coalesce \
		git-regress hg-regress svnload-regress legacy-regress \
		svndump-regress \
		repodiffer-regress repomapper-regress
	@echo "=== No diff output is good news."

.SUFFIXES: .svn .chk .fi .map

.svn.chk:
	$(REPOSURGEON) "read <$<" "prefer git" "write -" >$@ 2>&1
.svn.fi:
	$(REPOSURGEON) "read <$<" "prefer git" "write -" >$@
.svn.map:
	$(REPOSURGEON) "read <$<" "legacy write -" >$@

buildregress: fi-buildregress svnload-buildregress legacy-buildregress \
	svndump-buildregress repodiffer-buildregress repomapper-buildregress

clean:
	rm -fr .rs* test-repo test-checkout git-repo left-repo right-repo *~

# Show summary lines for all tests.
testlist:
	@grep '^##' *.tst
	@grep '^ ##' *.svn
listcheck:
	@for f in *.tst *.svn; do \
	    if ( head -3 $$f | grep -q '^ *##' ); then :; else echo "$$f needs a description"; fi; \
	done

# Test that all stream files round-trip properly
roundtrip:
	@echo "=== Testing stream-file round-tripping:" 
	@for file in *.fi; do \
	    echo "  $${file}"; \
	    $(REPOSURGEON) "read -;write -" <$$file >/tmp/rs$$$$; \
	    [ -s /tmp/r$$$$ ] && diff --text -u $${file} /tmp/rs$$$$; \
	    rm -f /tmp/rs$$$$; \
	done
	@echo "=== Testing stream-file round-tripping with compression:" 
	@for file in *.fi; do \
	    echo "  $${file}"; \
	    $(REPOSURGEON) "set compressblobs" "read -;write -" <$$file >/tmp/rs$$$$; \
	    [ -s /tmp/rs$$$$ ] && diff --text -u $${file} /tmp/rs$$$$; \
	    rm -f /tmp/rs$$$$; \
	done

# Test that dumping metadata to mailbox form and updating from the mailbox
# is idempotent if you make no changes to the mailbox.
mailboxing:
	@echo "=== Testing mailbox-out/mailbox-in roundtripping:"
	@for file in *.fi; do \
	    echo "  $${file}";\
	    $(REPOSURGEON) "read <$${file}" "edit echo>/dev/null" "write -" >/tmp/regress; \
	    [ -s /tmp/regress ] && diff --text -u $${file} /tmp/regress; \
	done
	@rm -f /tmp/regress

# General regression testing of commands and output; look at the *.tst and
# corresponding *.chk files to see which tests this runs.
TESTLOADS := $(shell ls -1 *.tst | sed '/.tst/s///')
fi-buildregress:
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    $(REPOSURGEON) "script $${file}.tst testing123" >$${file}.chk 2>&1; \
	done
fi-regress:
	@echo "=== Running general tests:"
	@for file in $(TESTLOADS); do \
	    $(ECHO) -n "  $${file} "; grep '##' $${file}.tst  || echo ' ## (no description)'; \
	    if $(REPOSURGEON) "script $${file}.tst testing123" >/tmp/regress 2>&1; \
	    then diff --text -u $${file}.chk /tmp/regress; \
	    else echo "*** Nonzero return status on $${file}!"; exit 1; fi \
	done
	@rm -f /tmp/regress

# Test coalescence operation.
COALESCE=uncoalesced
buildcoalesce:
	@for file in $(COALESCE); do \
	    echo "Rebuilding coalescence regression test using $${file}.fi"; \
	    $(REPOSURGEON) "read <$${file}.fi; coalesce; write -" > $${file}.chk; \
	done
	@rm -f /tmp/regress
coalesce:
	@echo "=== Coalescence regression test:"
	@for file in $(COALESCE); do \
	    echo "  $${file}.fi"; \
	    $(REPOSURGEON) "read <$${file}.fi; coalesce; write -" >/tmp/regress; \
	    [ -s /tmp/regress ] && diff --text -u $${file}.chk /tmp/regress; \
	done
	@rm -f /tmp/regress

# Test the git extractor
GITLOADS = bs
git-regress:
	@echo "=== Testing git-extractor:"
	@for test in $(GITLOADS); do \
	    if (echo "  $${test}.fi" >&2; \
	    ./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress; \
	    then diff --text -u $${test}.fi /tmp/regress; \
	    else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	done
	@rm -f /tmp/regress

# Test the hg extractor
HGLOADS = testrepo2
hg-regress:
	@echo "=== Testing hg-extractor:"
	@for test in $(HGLOADS); do \
	    if (echo "  $${test}.fi" >&2; \
	    ./hg-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress; \
	    then diff --text -u $${test}.fi /tmp/regress; \
	    else echo "*** Nonzero return status on $${test}!"; exit 1; fi \
	done
	@rm -f /tmp/regress

# Make a new repo and checkout directory to create a Subversion test load.
# Reminder - a branch copy looks like this:
# svn copy file://$PWD/test-repo/trunk file://$PWD/test-repo/branches/foo
svn-flat: clean
	svnadmin create test-repo
	svn co file://${PWD}/test-repo test-checkout
svn-branchy: svn-flat
	@cd test-checkout; set -x; \
		svn mkdir trunk; svn mkdir tags; svn mkdir branches; \
		echo "Directory layout." | svn commit -F -; \
		echo "This is a test Subversion repository" >trunk/README; \
		svn add trunk/README; \
		echo "Initial README content." | svn commit -F -
svn-dump:
	@svnadmin dump test-repo 

# Test loading from Subversion
SVNLOADS := $(shell ls *.svn | sed '/.svn/s///')
svnload-buildregress:
	@for test in $(SVNLOADS); do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		    echo "Remaking $${test}.chk"; \
		    rm -f $${test}.chk && make --quiet $${test}.chk; \
	    fi \
	done
svnload-regress:
	@echo "== Testing loading of Subversion streams:"
	@for test in $(SVNLOADS); \
	do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		(if $(ECHO) -n "  $${test}.svn" >&2; grep '^ ##' $${test}.svn ||  echo ' ## (no description)'; >&2\
		$(REPOSURGEON) "read <$${test}.svn" "prefer git" "write -" >/tmp/regress 2>&1; \
		then diff --text -u $${test}.chk /tmp/regress; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi; \
		mkdir /tmp/reposurgeon$$$$ ; \
		(cd /tmp/reposurgeon$$$$; \
		    git init --quiet; \
		    grep -v 'reposurgeon:' /tmp/regress | git fast-import --quiet); \
		rm -fr /tmp/reposurgeon$$$$) \
	    fi \
	done
	@rm -f /tmp/regress

REFLOADS=references mergeinfo-with-split
legacy-buildregress:
	@for test in $(REFLOADS); \
	do \
	    echo "Remaking $${test}.map"; \
	    rm -f $${test}.map && make --quiet $${test}.map 2>/dev/null; \
	done
legacy-regress:
	@echo "=== Testing legacy-map generation:"
	@for test in $(REFLOADS); \
	do \
	    if echo "  $${test}.svn" >&2; \
	    $(REPOSURGEON) "read <$${test}.svn" "legacy write -" >/tmp/regress 2>/dev/null; \
	    then diff --text -u $${test}.map /tmp/regress; \
	    else echo "*** Nonzero return status on $${test}!"; exit 1; fi; \
	done
	@rm -f /tmp/regress

# Test dumping to Subversion
DUMPLOADS=bs svnfodder
svndump-buildregress:
	@for f in $(DUMPLOADS); \
	do \
	    echo "Remaking $${f}.chk"; \
	    $(REPOSURGEON) "read <$${f}.fi" "prefer svn" "write -" | svn-to-svn -s >$${f}.chk; \
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
		then diff --text -u $${test}.chk /tmp/stripped$$$$; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi;\
		svn-to-svn -n -q </tmp/prestripped$$$$; \
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
		svn-to-svn -s <$${test}.svn >/tmp/checkstripped$$$$ 2>&1; \
		if echo "  $${test}.svn" >&2; \
		$(REPOSURGEON) "set svn_no_autoignores" "read $${test}.svn" "prefer svn" "write -"  | svn-to-svn -s >/tmp/stripped$$$$ 2>&1; \
		then diff --text -u /tmp/checkstripped$$$$ /tmp/stripped$$$$; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi;\
	    fi \
	done
	@make --quiet clean
	@rm -f /tmp/prestripped$$$$ /tmp/stripped$$$$ /tmp/checkstripped$$$$

# Regression-testing of repodiffer; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
REPODIFFER := $(shell ls -1 repodiffer*.sh | sed '/.sh/s///')
repodiffer-buildregress:
	@-for file in $(REPODIFFER); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk; \
	done
repodiffer-regress:
	@echo "=== Running repodiffer tests:"
	@-for file in $(REPODIFFER); do \
	    $(ECHO) -n "  $${file} "; grep '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh | diff --text -u $${file}.chk -; \
	done
	@rm -f /tmp/regress

# Regression-testing of repomapper; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
REPOMAPPER := $(shell ls -1 repomapper*.sh | sed '/.sh/s///')
repomapper-buildregress:
	@-for file in $(REPOMAPPER); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk; \
	done
repomapper-regress:
	@echo "=== Running repomapper tests:"
	@-for file in $(REPOMAPPER); do \
	    $(ECHO) -n "  $${file} "; grep '##' $${file}.sh  || echo ' ## (no description)'; \
	    $(SHELL) $${file}.sh | diff --text -u $${file}.chk -; \
	done
	@rm -f /tmp/regress

# end
