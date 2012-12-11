# Test-suite makefile for reposurgeon

PATH := ${PATH}:..

all: listcheck roundtrip mailboxing fi-regress coalesce \
		git-regress svnload-regress fossil-regress svndump-regress \
		repodiffer-regress
	@echo "=== No diff output is good news."

.SUFFIXES: .svn .chk .fi .map

# The 'prefer git' suppresses writing out properties.
.svn.chk:
	reposurgeon "read $<" "prefer git" "write" >$@ 2>&1
.svn.fi:
	reposurgeon "read $<" "prefer git" "write" >$@
.svn.map:
	reposurgeon "read $<" "prefer git" "fossils write" >$@

buildregress: fi-buildregress svnload-buildregress fossil-buildregress \
	svndump-buildregress repodiffer-buildregress

clean:
	rm -fr .rs* test-repo test-checkout git-repo *~

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
	    reposurgeon "read -;write -" <$$file >/tmp/rs$$$$; \
	    diff -u $${file} /tmp/rs$$$$; \
	    rm -f /tmp/rs$$$$; \
	done

# Test that dumping metadata to mailbox form and updating from the mailbox
# is idempotent if you make no changes to the mailbox.
mailboxing:
	@echo "=== Testing mailbox-out/mailbox-in roundtripping:"
	@for file in *.fi; do \
	    echo "  $${file}";\
	    reposurgeon "read $${file}" "edit echo>/dev/null" "write" >/tmp/regress; \
	    diff -u $${file} /tmp/regress; \
	done
	@rm -f /tmp/regress

# General regression testing of commands and output; look at the *.tst and
# corresponding *.chk files to see which tests this runs.
TESTLOADS := $(shell ls -1 *.tst | sed '/.tst/s///')
fi-buildregress:
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    reposurgeon "script $${file}.tst testing123" >$${file}.chk 2>&1; \
	done
fi-regress:
	@echo "=== Running general tests:"
	@for file in $(TESTLOADS); do \
	    echo -n "  $${file} "; grep '##' $${file}.tst  || echo ' ## (no description)'; \
	    if reposurgeon "script $${file}.tst testing123" >/tmp/regress 2>&1; \
	    then diff -u $${file}.chk /tmp/regress; \
	    else echo "*** Nonzero return status on $${file}!"; exit 1; fi \
	done
	@rm -f /tmp/regress

# Test coalescence operation.
COALESCE=uncoalesced
buildcoalesce:
	@for file in $(COALESCE); do \
	    echo "Rebuilding coalescence regression test using $${file}.fi"; \
	    reposurgeon "read $${file}.fi; coalesce; write -" > $${file}.chk; \
	done
	@rm -f /tmp/regress
coalesce:
	@echo "=== Coalescence regression test:"
	@for file in $(COALESCE); do \
	    echo "  $${file}.fi"; \
	    reposurgeon "read $${file}.fi; coalesce; write -" >/tmp/regress; \
	    diff -u $${file}.chk /tmp/regress; \
	done
	@rm -f /tmp/regress

# Test the git extractor
GITLOADS = bs
git-regress:
	@echo "=== Testing git-extractor:"
	@for test in $(GITLOADS); do \
	    if (echo "  $${test}.fi" >&2; \
	    ./fi-to-fi) <$${test}.fi | sed '/# Fossil-ID:/d' >/tmp/regress; \
	    then diff -u $${test}.fi /tmp/regress; \
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
		(if echo -n "  $${test}.svn" >&2; grep '^ ##' $${test}.svn ||  echo ' ## (no description)'; >&2\
		reposurgeon "read $${test}.svn" "prefer git" "write" >/tmp/regress 2>&1; \
		then diff -u $${test}.chk /tmp/regress; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi; \
		mkdir /tmp/reposurgeon$$$$ ; \
		(cd /tmp/reposurgeon$$$$; \
		    git init --quiet; \
		    grep -v '^reposurgeon:' /tmp/regress | git fast-import --quiet); \
		rm -fr /tmp/reposurgeon$$$$) \
	    fi \
	done
	@rm -f /tmp/regress

REFLOADS=references mergeinfo-with-split
fossil-buildregress:
	@for test in $(REFLOADS); \
	do \
	    echo "Remaking $${test}.map"; \
	    rm -f $${test}.map && make --quiet $${test}.map 2>/dev/null; \
	done
fossil-regress:
	@echo "=== Testing fossil-map generation:"
	@for test in $(REFLOADS); \
	do \
	    if echo "  $${test}.svn" >&2; \
	    reposurgeon "read $${test}.svn" "fossils write" >/tmp/regress 2>/dev/null; \
	    then diff -u $${test}.map /tmp/regress; \
	    else echo "*** Nonzero return status on $${test}!"; exit 1; fi; \
	done
	@rm -f /tmp/regress

# Test dumping to Subversion
DUMPLOADS=bs svnfodder
svndump-buildregress:
	@for f in $(DUMPLOADS); \
	do \
	    echo "Remaking $${f}.chk"; \
	    reposurgeon "read $${f}.fi" "prefer svn" "write" | svn-to-svn -s >$${f}.chk; \
	done
	@make --quiet clean
svndump-regress:
	@echo "=== Test dumping of Subversion streams:"
	@for test in $(DUMPLOADS); \
	do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		if echo "  $${test}.fi" >&2; \
		reposurgeon "read $${test}.fi" "prefer svn" "write" | tee /tmp/prestripped$$$$ | svn-to-svn -s >/tmp/stripped$$$$ 2>&1; \
		then diff -u $${test}.chk /tmp/stripped$$$$; \
		else echo "*** Nonzero return status on $${test}!"; exit 1; fi;\
		svn-to-svn -n -q </tmp/prestripped$$$$; \
	    fi \
	done
	@make --quiet clean
	@rm -f /tmp/prestripped$$$$ /tmp/stripped$$$$

# Regression-testing of repodiffer; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
REPODIFFER := $(shell ls -1 repodiffer*.sh | sed '/.sh/s///')
repodiffer-buildregress:
	@-for file in $(REPODIFFER); do \
	    echo "Remaking $${file}.chk"; \
	    sh $${file}.sh >$${file}.chk; \
	done
repodiffer-regress:
	@echo "=== Running repodiffer tests:"
	@-for file in $(REPODIFFER); do \
	    echo -n "  $${file} "; grep '##' $${file}.sh  || echo ' ## (no description)'; \
	    sh $${file}.sh | diff -u $${file}.chk -; \
	done
	@rm -f /tmp/regress

# end
