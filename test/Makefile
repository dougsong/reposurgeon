# Test-suite makefile for reposurgeon

all: clean roundtrip regress
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

TESTLOADS = simple-dump
makeregress:
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    ../reposurgeon "script $${file}.tst" >$${file}.chk; \
	done
regress:
	@for file in $(TESTLOADS); do \
	    echo "Regression test using $${file}.tst"; \
	    ../reposurgeon "script $${file}.tst" >/tmp/regress; \
	    diff -u $${file}.chk /tmp/regress; \
	done
	@rm -f /tmp/regress

