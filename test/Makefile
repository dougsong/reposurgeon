# Test-suite makefile for rs

all: roundtrip

# Test that all dumpfiles round-trip properly
# Test suceeds if there is no output.
roundtrip:
	echo "Testing round-tripping of dump file. No diff output is good news."
	for file in *.dump; do \
	    ../rs "read -;write -" <$$file >/tmp/rs$$$$; \
	    diff -u $${file} /tmp/rs$$$$; \
	    rm -f /tmp/rs$$$$; \
	done
