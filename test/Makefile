# Test-suite makefile for reposurgeon

all: listcheck roundtrip mailboxing fi-regress coalesce \
		git-regress svn-regress fossil-regress
	@echo "No diff output is good news."

.SUFFIXES: .svn .chk .fi

# The 'prefer git' suppresses writing out properties.
.svn.chk:
	../reposurgeon "read $<" "prefer git" "write" >$@ 2>&1
.svn.fi:
	../reposurgeon "read $<" "prefer git" "write $@"

buildregress: fi-buildregress svn-buildregress fossil-buildregress

clean:
	rm -fr .rs* test-repo test-checkout *~

# Show summary lines for all tests.
testlist:
	@grep '^##' *.tst
	@grep '^ ##' *.svn
listcheck:
	@for f in *.tst *.svn; do \
	    if ( head -3 $$f | grep -q '^ *##' ); then :; else echo "$$f needs a description"; fi; \
	done

# Test that all dumpfiles round-trip properly
roundtrip:
	@for file in *.fi; do \
	    echo "Testing round-tripping of $${file}"; \
	    ../reposurgeon "read -;write -" <$$file >/tmp/rs$$$$; \
	    diff -u $${file} /tmp/rs$$$$; \
	    rm -f /tmp/rs$$$$; \
	done

# Test that dumping metadata to mailbox form and updating from the mailbox
# is idempotent if you make no changes to the mailbox.
mailboxing:
	@for file in *.fi; do \
	    echo "Testing mailbox-out/mailbox-in roundtripping using $${file}";\
	    ../reposurgeon "read $${file}" "edit echo>/dev/null" "write" >/tmp/regress; \
	    diff -u $${file} /tmp/regress; \
	done
	@rm -f /tmp/regress

# General regression testing of commands and output; look at the *.tst and
# corresponding *.chk files to see which tests this runs.
TESTLOADS := $(shell ls -1 *.tst | sed '/.tst/s///')
fi-buildregress:
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    ../reposurgeon "script $${file}.tst testing123" >$${file}.chk 2>&1; \
	done
fi-regress:
	@for file in $(TESTLOADS); do \
	    echo -n $${file} " "; grep '##' $${file}.tst  || echo ' ## (no description)'; \
	    if ../reposurgeon "script $${file}.tst testing123" >/tmp/regress 2>&1; \
	    then diff -u $${file}.chk /tmp/regress; \
	    else echo "*** Nonzero return status on $${file}!"; exit 1; fi \
	done
	@rm -f /tmp/regress

# Test coalescence operation.
COALESCE=uncoalesced
buildcoalesce:
	@for file in $(COALESCE); do \
	    echo "Rebuilding coalescence regression test using $${file}.fi"; \
	    ../reposurgeon "read $${file}.fi; coalesce; write -" > $${file}.chk; \
	done
	@rm -f /tmp/regress
coalesce:
	@for file in $(COALESCE); do \
	    echo "Coalescence regression test using $${file}.fi"; \
	    ../reposurgeon "read $${file}.fi; coalesce; write -" >/tmp/regress; \
	    diff -u $${file}.chk /tmp/regress; \
	done
	@rm -f /tmp/regress

GITLOADS = bs
git-regress:
	@for test in $(GITLOADS); do \
	    if (echo "Testing git-extractor on $${test}" >&2; \
	    ./fi-to-fi) <$${test}.fi >/tmp/regress; \
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

SVNLOADS := $(shell ls *.svn | sed '/.svn/s///')
svn-buildregress:
	@for test in $(SVNLOADS); do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		    echo "Remaking $${test}.chk"; \
		    rm -f $${test}.chk && make --quiet $${test}.chk; \
	    fi \
	done
svn-regress:
	@for test in $(SVNLOADS); \
	do \
	    if [ ! -f $${test}.tst ] ; \
	    then \
		(if echo -n "Testing $${test}" >&2; grep '^ ##' $${test}.svn ||  echo ' ## (no description)'; >&2\
		../reposurgeon "read $${test}.svn" "prefer git" "write" >/tmp/regress 2>&1; \
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
	    ../reposurgeon "read $${test}.svn" "fossils write " >$${test}.map 2>&1; \
	done
fossil-regress:
	@for test in $(REFLOADS); \
	do \
	    if echo "Checking $${test} map" >&2; \
	    ../reposurgeon "read $${test}.svn" "fossils write" >/tmp/regress 2>&1; \
	    then diff -u $${test}.map /tmp/regress; \
	    else echo "*** Nonzero return status on $${test}!"; exit 1; fi; \
	done
	@rm -f /tmp/regress

# end
