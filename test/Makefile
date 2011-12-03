# Test-suite makefile for reposurgeon

all: clean roundtrip mailboxing fi-regress coalesce svn-regress
	@echo "No diff output is good news."

buildregress: fi-regress svn-regress

clean:
	rm -fr .rs* test-repo test-checkout

# Test that all dumpfiles round-trip properly
roundtrip:
	@for file in *.fi; do \
	    echo "Testing round-tripping of $${file}.tst."; \
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
TESTLOADS = simple roundup gsoc cut testrepo testmerge graft references
fi-buildregress:
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    ../reposurgeon "script $${file}.tst" >$${file}.chk 2>&1; \
	done
fi-regress:
	@for file in $(TESTLOADS); do \
	    echo -n $${file} " "; grep '##' $${file}.tst; \
	    if ../reposurgeon "script $${file}.tst" >/tmp/regress 2>&1; \
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

# Make a new repo and checkout directory to create a Subversion test load.
svn-flat: clean
	svnadmin create test-repo
	svn co file://${PWD}/test-repo test-checkout
svn-branchy: svn-flat
	@cd test-checkout; set -x; \
		svn mkdir trunk; svn mkdir tags; svn mkdir branches; \
		svn commit -m "Directory layout"; \
		echo "This is a test Subversion repository" >trunk/README; \
		svn add trunk/README; \
		svn commit -m "Initial README content.\n"

SVNLOADS = vanilla simpletag #samplebranch ignores nontipcopy
svn-buildregress:
	@for test in $(SVNLOADS); do \
	    echo "Remaking $${test}.chk"; \
	    sd-to-fi <$${test}.sd >$${test}.chk; \
	done
svn-regress:
	@for test in $(SVNLOADS); do \
	    if (echo "Testing $${test}" >&2; \
	    sd-to-fi) <$${test}.sd >/tmp/regress; \
	    then diff -u $${test}.chk /tmp/regress; \
	    else echo "*** Nonzero return status on $${test}!"; exit 1; fi; \
	    mkdir /tmp/reposteamer$$$$ ; \
	    (cd /tmp/reposteamer$$$$; git init --quiet; git fast-import --quiet) </tmp/regress; \
	    rm -fr /tmp/reposteamer$$$$ ; \
	done
	@rm -f /tmp/regress
