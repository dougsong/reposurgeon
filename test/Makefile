# Test-suite makefile for reposurgeon

all: roundtrip selectregress
	@echo "No diff output is good news."

# Test that all dumpfiles round-trip properly
roundtrip:
	@echo "Testing round-tripping of dump file."
	@for file in *.dump; do \
	    ../reposurgeon "read -;write -" <$$file >/tmp/rs$$$$; \
	    diff -u $${file} /tmp/rs$$$$; \
	    rm -f /tmp/rs$$$$; \
	done

make_selectregress:
	../reposurgeon "script simple-dump.tst" >simple-dump.chk
selectregress:
	@echo "Regression-testing the selection language."
	@../reposurgeon "script simple-dump.tst" >/tmp/regress
	@diff -u simple-dump.chk /tmp/regress
	@rm -f /tmp/regress

# Alas, we can't regression-test email_out without giving up generating 
# a now timestamp into the header
