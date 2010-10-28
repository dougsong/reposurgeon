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

# Test that the selection language gives consistent results.
# Pile up test cases in SELECT_TEST.  The checkfile contains an 
# index listing that you can use to sanity-check the resolve
# results by eyeball.
SELECT_TEST = resolve 15; \
	resolve =TR; \
	resolve 24..97; \
	resolve 24..97&=C; \
	resolve 3,:15; \
	resolve /regression/
select_test:
	cat simple.dump | ../reposurgeon "read -" "echo 1" "index; $(SELECT_TEST)"
make_selectregress:
	make --quiet select_test >select_test.chk
selectregress:
	@echo "Regression-testing the selection language."
	@make --quiet select_test >/tmp/regress
	@diff -u select_test.chk /tmp/regress
	@rm -f /tmp/regress

# Alas, we can't regression-test email_out without giving up generating 
# a now timestamp into the header
