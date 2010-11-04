# Test-suite makefile for reposurgeon

all: clean roundtrip mailboxing regress coalesce
	@echo "No diff output is good news."

clean:
	rm -fr .rs*

# Test that all dumpfiles round-trip properly
roundtrip:
	@for file in *.dump; do \
	    echo "Testing round-tripping of $${file}.tst."; \
	    ../reposurgeon "read -;write -" <$$file >/tmp/rs$$$$; \
	    diff -u $${file} /tmp/rs$$$$; \
	    rm -f /tmp/rs$$$$; \
	done

# Test that dumping metadata to mailbox form and updating from the mailbox
# is idempotent if you make no changes to the mailbox.
mailboxing:
	@for file in *.dump; do \
	    echo "Testing mailbox-out/mailbox-in roundtripping using $${file}";\
	    ../reposurgeon "read $${file}" "edit echo>/dev/null" "write" >/tmp/regress; \
	    diff -u $${file} /tmp/regress; \
	done
	@rm -f /tmp/regress

# General regression testing of commands and output; look at the *.tst and
# corresponding *.chk files to see which tests this runs.
TESTLOADS = simple-dump
makeregress:
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    ../reposurgeon "script $${file}.tst" >$${file}.chk 2>&1; \
	done
regress:
	@for file in $(TESTLOADS); do \
	    echo "Regression test using $${file}.tst"; \
	    ../reposurgeon "script $${file}.tst" >/tmp/regress 2>&1; \
	    diff -u $${file}.chk /tmp/regress; \
	done
	@rm -f /tmp/regress

# Test coalescence operation.
COALESCE=uncoalesced
makecoalesce:
	@for file in $(COALESCE); do \
	    echo "Rebuliding coalescence regression test using $${file}.dump"; \
	    ../reposurgeon "read $${file}.dump; coalesce; write -" > $${file}.chk; \
	done
	@rm -f /tmp/regress
coalesce:
	@for file in $(COALESCE); do \
	    echo "Coalescence regression test using $${file}.dump"; \
	    ../reposurgeon "read $${file}.dump; coalesce; write -" >/tmp/regress; \
	    diff -u $${file}.chk /tmp/regress; \
	done
	@rm -f /tmp/regress

