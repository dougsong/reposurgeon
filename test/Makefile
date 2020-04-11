# Test-suite makefile for reposurgeon

# By setting the REPOSURGEON environment variable and using -e
# a different implementation can be plugged in to the tests.

# Use absolute path so tests that change working directory still use 
# scripts from parent directory.  Note that using $PWD seems to fail
# here under Gitlab's CI environment.
PATH := $(realpath ..):$(realpath .):${PATH}
REPOSURGEON := reposurgeon 
REPOCUTTER := repocutter 
REPOTOOL := repotool
REPOMAPPER := repomapper

# Force the timezone in case CI has a different idea
export TZ=UTC

# Setting this to 0 allows tests to continue on error.
STOPOUT=1

# Setting this to 1 suppresses diffs in favor of a FAIL tag
QUIET=0

# Force pure serial execution when rebuilding check files.  Slower,
# but makes them deterministic and may help smoke out bugs in
# concurrent code.
BUILDOPT="set serial"

# Defeat annoying behavior under Mac OS X - builtin echo doesn't do -n
ECHO := /bin/echo

# Define test groups
BASIC = listcheck roundtrip roundtrip-compress messagebox fi-regress
SUBVERSION = svnload-regress liftcheck-regress legacy-regress svncheck-regress
FULLSUBVERSION = $(SUBVERSION) liftcheck-fullregress
GIT_EXTRACTOR = git-regress git-regress-branches git-regress-merges git-regress-tags
HG_EXTRACTOR = hg-regress hg-regress-branches hg-regress-merges hg-regress-tags \
	hg-regress-patho
AUXTOOLS = repocutter-regress repomapper-regress repotool-regress

# See https://stackoverflow.com/questions/6481005/how-to-obtain-the-number-of-cpus-cores-in-linux-from-the-command-line
CONCURRENT_JOBS=$(shell getconf _NPROCESSORS_ONLN || getconf NPROCESSORS_ONLN || echo 4)

# Exploit make parallelism
PARALLEL_MAKE=make --output-sync --no-print-directory -j $(CONCURRENT_JOBS)

# This should always be a full test
check: clean disclose $(BASIC) $(FULLSUBVERSION) $(GIT_EXTRACTOR) $(HG_EXTRACTOR) $(AUXTOOLS)
	@echo "=== Sporadic tests:"
	sh hashcheck.sh
	@echo "=== No diff output is good news ==="

disclose:
	@echo "Running with $(CONCURRENT_JOBS) threads."

# FIXME: is log -all really correct when regenerating the map checks?

.SUFFIXES: .svn .chk .fi .map

.svn.chk:
	$(REPOSURGEON) "read <$<" "prefer git" "write -" >$@ 2>&1
.svn.fi:
	$(REPOSURGEON) "read <$<" "prefer git" "write -" >$@
.svn.map:
	$(REPOSURGEON) "log -all" "read <$<" "legacy write -" >$@

buildregress: fi-buildregress svnload-buildregress legacy-buildregress \
	repomapper-buildregress repotool-buildregress hg-buildregress-branches \
	svncheck-buildregress repocutter-buildregress repomapper-buildregress \
	repotool-buildregress

clean:
	rm -fr .rs* test-repo test-checkout git-repo left-repo right-repo *~

options:
	@echo "REPOSURGEON is '$(REPOSURGEON)'"
	@echo "TESTOPT is '$(TESTOPT)'"

# Show summary lines for all tests.
testlist:
	@grep --text '^##' *.tst *.sh
	@grep --text '^ ##' *.svn
listcheck:
	@for f in *.tst *.svn; do \
	    if ( head -3 $$f | grep --text -q '^ *##' ); then :; else echo "$$f needs a description" >&2; exit $(STOPOUT); fi;  \
	done

# Test that all stream files round-trip properly
RULES_ROUNDTRIP=$(patsubst %,roundtrip-%,$(wildcard *.fi))
roundtrip:
	@echo "=== Testing stream-file round-tripping:"
	@$(PARALLEL_MAKE) $(RULES_ROUNDTRIP)

$(RULES_ROUNDTRIP): roundtrip-%: %
	@echo "  $<"; \
	$(REPOSURGEON) "$(TESTOPT)" "read -;write -" <$< >/tmp/rs$$$$ || exit $(STOPOUT); \
	[ -s /tmp/rs$$$$ ] && diff --text -u $< /tmp/rs$$$$ \
		|| exit $(STOPOUT); \
	rm -f /tmp/rs$$$$ || exit $(STOPOUT)

# Test that all stream files round-trip properly with compression
RULES_ROUNDTRIP_COMPRESS=$(patsubst %,roundtrip-compress-%,$(wildcard *.fi))
roundtrip-compress:
	@echo "=== Testing stream-file round-tripping with compression:" 
	@$(PARALLEL_MAKE) $(RULES_ROUNDTRIP_COMPRESS)

$(RULES_ROUNDTRIP_COMPRESS): roundtrip-compress-%: %
	@echo "  $<"; \
	$(REPOSURGEON) "$(TESTOPT)" "set compressblobs" "read -;write -" \
		<$< >/tmp/rs$$$$ || exit $(STOPOUT); \
	[ -s /tmp/rs$$$$ ] && diff --text -u $< /tmp/rs$$$$ \
		|| exit $(STOPOUT); \
	rm -f /tmp/rs$$$$ || exit $(STOPOUT)

# Test that dumping metadata to msgbox form and updating from the message-box
# is idempotent if you make no changes to the message-box.
RULES_MESSAGE_BOX=$(patsubst %,messagebox-%,$(wildcard *.fi))
messagebox:
	@echo "=== Testing msgout/msgin roundtripping:"
	@$(PARALLEL_MAKE) $(RULES_ROUNDTRIP_COMPRESS)

$(RULES_MESSAGE_BOX): messagebox-%: %
	@echo "  $${file}";\
	$(REPOSURGEON) "$(TESTOPT)" "read <$<" "edit echo>/dev/null" "write -" \
	>/tmp/regress$$$$ || exit $(STOPOUT); \
	[ -s /tmp/regress$$$$ ] && diff --text -u $< /tmp/regress$$$$ \
	|| exit $(STOPOUT); \
	rm -f /tmp/regress$$$$

# General regression testing of commands and output; look at the *.tst and
# corresponding *.chk files to see which tests this runs.
TESTLOADS := $(shell ls -1 *.tst | sed '/.tst/s///')
fi-buildregress: multigen.svn
	@for file in $(TESTLOADS); do \
	    echo "Remaking $${file}.chk"; \
	    $(REPOSURGEON) $(BUILDOPT) "$(TESTOPT)" "script $${file}.tst testing123" >$${file}.chk \
		2>&1 || exit $(STOPOUT); \
	done

fi-regress: multigen.svn
	@echo "=== Running general tests:"
	@$(PARALLEL_MAKE) $(TESTLOADS:%=fi-regress-%)

# A generated test load
multigen.svn: multigen.sh
	sh multigen.sh -d >multigen.svn
	sh singlelift -b multigen

$(TESTLOADS:%=fi-regress-%): fi-regress-%: %.tst
	@file=$(<:.tst=); \
	( $(ECHO) -n "  $${file} "; grep --text '##' $${file}.tst  || echo ' ## (no description)' ) | sed -e '/ ##/s//:/' ; \
	    $(REPOSURGEON) "$(TESTOPT)" "script $${file}.tst testing123" >/tmp/regress$$$$ 2>&1 \
		|| (echo "*** Nonzero return status on $${file}!"; exit $(STOPOUT) ); \
	    diff --text -u $${file}.chk /tmp/regress$$$$ >/tmp/diff$$$$; \
	    case $$? in \
	    0) ;; \
	    1) if [ $(QUIET) = 1 ]; then echo FAILED; else cat /tmp/diff$$$$; fi; if [ $(STOPOUT) = 1 ]; then exit 1; fi;; \
	    *) echo "*** diff had trouble, status $$?"; exit $(STOPOUT);; \
	    esac ; \
	rm -f /tmp/regress$$$$ /tmp/diff$$$$

# Test the git extractor
GITLOADS = bs
git-regress:
	@echo "=== Testing git-extractor:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
		$(PARALLEL_MAKE) $(GITLOADS:%=git-regress-test-%); \
	else echo "    Skipped, git missing."; exit 0; \
	fi

# Test the git extractor with multiple git branches
GITBRANCHES = be bb
git-regress-branches:
	@echo "=== Testing git-extractor with multiple git branches:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
		$(PARALLEL_MAKE) $(GITBRANCHES:%=git-regress-test-%); \
	else echo "    Skipped, git missing."; exit 0; \
	fi

# Test the git extractor with merges
GITMERGES = be2 be3 be4 be5 be6
git-regress-merges:
	@echo "=== Testing git-extractor with merges:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
		$(PARALLEL_MAKE) $(GITMERGES:%=git-regress-test-%); \
	else echo "    Skipped, git missing."; exit 0; \
	fi

# Test the git extractor with tags
GITTAGS = bt bt2
git-regress-tags:
	@echo "=== Testing git-extractor with tags:"
	@if command -v git >/dev/null 2>&1 ; \
	then \
		$(PARALLEL_MAKE) $(GITTAGS:%=git-regress-test-%); \
	else echo "    Skipped, git missing."; exit 0; \
	fi

RULES_GIT_REGRESS=$(patsubst %,git-regress-test-%, \
			$(GITLOADS) $(GITBRANCHES) $(GITTAGS) $(GITMERGES))

$(RULES_GIT_REGRESS): git-regress-test-%: %.fi
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	test=$(<:.fi=); \
		if (echo "  $${test}.fi" >&2; \
		./fi-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi; \
	rm -f /tmp/regress$$$$


# Test the hg extractor
HGLOADS = testrepo2
hg-regress:
	@echo "=== Testing hg-extractor:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 && command -v git >/dev/null 2>&1 ; \
	then \
	    for test in $(HGLOADS); do \
		if (echo "  $${test}.fi" >&2; \
		./hg-to-fi) <$${test}.fi | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg or git missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with multiple hg branches
# NOTE: the bb-alt test demonstrates an hg repo with coloring that git cannot reproduce
HGBRANCHES = be be2 be3 bb-alt be-bookmarks
hg-buildregress-branches:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT; BUILDOPT=$(BUILDOPT); export BUILDOPT;\
	for file in $(HGBRANCHES); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit $(STOPOUT); \
	done
hg-regress-branches:
	@echo "=== Testing hg-extractor with multiple hg branches:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGBRANCHES); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with merges
HGMERGES = be2 be3 be4 be5 be6
hg-buildregress-merges:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for file in $(HGMERGES); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit $(STOPOUT); \
	done
hg-regress-merges:
	@echo "=== Testing hg-extractor with merges:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGMERGES); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with tags
HGTAGS = bt bt2
hg-buildregress-tags:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT; BUILDOPT=$(BUILDOPT); export BUILDOPT;\
	for file in $(HGTAGS); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit $(STOPOUT); \
	done
hg-regress-tags:
	@echo "=== Testing hg-extractor with tags:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGTAGS); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test) | sed -e 1d -e '/^#legacy-id/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test the hg extractor with pathological loads
HGPATHO = be-subrepo be-subrepo2
hg-buildregress-patho:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT; BUILDOPT=$(BUILDOPT); export BUILDOPT;\
	for file in $(HGPATHO); do \
	    echo "Remaking $${file}.fi"; \
	    ./hg-$${file}-test 2>/dev/null | sed -e 1d -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >$${file}.fi \
		2>&1 || exit $(STOPOUT); \
	done
hg-regress-patho:
	@echo "=== Testing hg-extractor with pathological loads:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	if command -v hg >/dev/null 2>&1 ; \
	then \
	    for test in $(HGPATHO); do \
		if (echo "  $${test}" >&2; \
		./hg-$${test}-test 2>/dev/null) | sed -e '/^#legacy-id/d' | sed -e '/^#reposurgeon sourcetype/d' >/tmp/regress$$$$; \
		then diff --text -u $${test}.fi /tmp/regress$$$$ || exit $(STOPOUT); \
		else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi \
	    done; \
	else echo "    Skipped, hg missing."; exit 0; \
	fi
	@rm -f /tmp/regress$$$$

# Test loading from Subversion
SVN_AND_TST_FILES := $(sort $(wildcard *.svn *.tst))
SVNLOADS := $(shell echo $(SVN_AND_TST_FILES) | sed 's/\([^ ]*\)\.svn \1.tst//g; s/[^ ]*\.tst//g; s/\.svn//g')
svnload-buildregress:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for test in $(SVNLOADS); do \
	    if [ -f $${test}.tst ] ; \
	    then \
		    echo "BUG: $${test} should have been skipped: $${test}.tst exists"; \
		    exit 1; \
		fi; \
		echo "Remaking $${test}.chk"; \
		rm -f $${test}.chk && make --quiet $${test}.chk \
			|| exit $(STOPOUT); \
	done

svnload-regress:
	@echo "== Testing loading of Subversion streams:"
	@$(PARALLEL_MAKE) $(SVNLOADS:%=svnload-regress-%)

$(SVNLOADS:%=svnload-regress-%): svnload-regress-%: %.svn
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT; BUILDOPT=$(BUILDOPT); export BUILDOPT;\
	test=$(<:.svn=); \
		{ $(ECHO) -n "  $${test}.svn"; grep --text '^ ##' $${test}.svn || echo ' ## (no description)'; } | sed -e '/ ##/s//:/' >&2; \
		$(REPOSURGEON) "$(TESTOPT)" "$(TESTOPT)" "read <$${test}.svn" "prefer git" "write -" >/tmp/regress$$$$ 2>&1 \
		    || (echo "*** Nonzero return status on $${file}!"; exit $(STOPOUT) ); \
		diff --text -u $${test}.chk /tmp/regress$$$$ >/tmp/diff$$$$; \
		case $$? in \
		0) ;; \
		1) if [ $(QUIET) = 1 ]; then echo FAILED; else cat /tmp/diff$$$$; fi; if [ $(STOPOUT) = 1 ]; then exit 1; fi;; \
		*) echo "*** diff had trouble, status $$?"; exit $(STOPOUT);; \
		esac; \
		if command -v git >/dev/null 2>&1 ; \
		then \
		    mkdir /tmp/reposurgeon$$$$ || exit $(STOPOUT); \
		    (cd /tmp/reposurgeon$$$$ || exit $(STOPOUT); \
			git init --quiet || exit $(STOPOUT); \
			grep --text -v 'reposurgeon:' /tmp/regress$$$$ | git fast-import --quiet) \
			    || exit $(STOPOUT); \
		    rm -fr /tmp/reposurgeon$$$$\
		else \
		    echo "    Skipped, git missing."; \
	    fi; \
	rm -f /tmp/regress$$$$ /tmp/diff$$$$

# Perform full regression on SVN streams that have clean conversions -
# that is, no messages due to branch surgery or whatever.
# Empty-commit tags generated in gitspace corresponding to branch
# copies are ignored.
SVNCLEAN := \
	nut.svn \
	agito.svn \
	attrws.svn \
	authortz.svn \
	bad-author.svn \
	badattrib.svn \
	badattrib2.svn \
	binary.svn \
	blob-id.svn \
	branchreplace.svn \
	branch-drop-add.svn \
	cherry-pick.svn \
	cvstag.svn \
	debranch.svn \
	deepdirs.svn \
	delete-rename.svn \
	deletion.svn \
	delignore.svn \
	delref.svn \
	dircopyprop.svn \
	emptycommit-merge.svn \
	emptyfrom.svn \
	executable.svn \
	expunge.svn \
	filecopy.svn \
	fleetwood.svn \
	format7.svn \
	gitify.svn \
	gitignore.svn \
	ignore-blank.svn \
	lint.svn \
	mergeinfo-combine.svn \
	mergeinfo-grandparent.svn \
	mergeinfo-trunkstomp.svn \
	mergeinfo-with-split.svn \
	mergeinfo.svn \
	mixedbranch.svn \
	mkignore.svn \
	myers1.svn \
	node-kind-first.svn \
	no-forward-merge.svn \
	no-merge.svn \
	nontipcopy.svn \
	nullignores.svn \
	pangram.svn \
	permcopy1.svn \
	permcopy2.svn \
	permcopy3.svn \
	permcopy4.svn \
	replace-dir.svn \
	rootfirst.svn \
	samplebranch.svn \
	simpletag.svn \
	smallref.svn \
	snarl.svn \
	split-dir.svn \
	squash-id.svn \
	subclipse.svn \
	subdir.svn \
	svnignores.svn \
	symlink.svn \
	tagpollute.svn \
	tagsimple.svn \
	tagsimpledelete.svn \
	treecontents.svn \
	trunkstomp.svn \
	vanilla.svn \
	wrong-mergeinfo.svn \

liftcheck-regress:
	@echo "== Testing conversion correctness of Subversion streams at head revision:"
	@if  command -v git >/dev/null 2>&1 &&  command -v svn >/dev/null 2>&1; \
	then \
		$(PARALLEL_MAKE) $(SVNCLEAN:%=liftcheck-regress-%); \
	else \
		echo "     Skipped, either git or svn is missing"; \
	fi

$(patsubst %,liftcheck-regress-%,$(wildcard *.svn)): liftcheck-regress-%: %
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	liftcheck -e emptycommit -e -root $< >/tmp/diff$$$$; \
	case $$? in \
	    0) ;; \
	    1) if [ $(QUIET) = 1 ]; then echo FAILED; else cat /tmp/diff$$$$; fi; if [ $(STOPOUT) = 1 ]; then exit 1; fi;; \
	    *) echo "*** liftcheck had trouble, status $$?"; exit $(STOPOUT);; \
	esac; \
	rm -f /tmp/diff$$$

# This is not part of the normal test sequence becausr the reposurgeon tools are very slow.
# Put references.svn first because it is the longest one to run.
LOADS_LIFTCHECK_FULLREGRESS = nut.svn $(filter-out nut.svn,$(wildcard *.svn))
RULE_LIFTCHECK_FULLREGRESS = $(LOADS_LIFTCHECK_FULLREGRESS:%=liftcheck-regress-full-%)
liftcheck-fullregress:
	@echo "== Testing conversion correctness of all SVN revisions:"
	@if  command -v git >/dev/null 2>&1 &&  command -v svn >/dev/null 2>&1; \
	then \
		$(PARALLEL_MAKE) $(RULE_LIFTCHECK_FULLREGRESS); \
	else \
		echo "     Skipped, either git or svn is missing"; \
	fi

$(RULE_LIFTCHECK_FULLREGRESS): liftcheck-regress-full-%: %
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	liftcheck -q -r all $< || { echo "*** Failed on $< !"; exit $(STOPOUT); } \

# List Subversion streams that don't convert clean without -q -r all
liftcheck-dirty:
	@for x in $(SVNCLEAN); do echo $${x} >>goodlist$$$$; done; \
	sort -o goodlist$$$$ goodlist$$$$; \
	ls *.svn | comm -23 - goodlist$$$$; \
	rm goodlist$$$$

REFLOADS=nut mergeinfo-with-split
legacy-buildregress:
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for test in $(REFLOADS); \
	do \
	    echo "Remaking $${test}.map"; \
	    rm -f $${test}.map && make --quiet $${test}.map 2>/dev/null \
		|| exit $(STOPOUT); \
	done
legacy-regress:
	@echo "=== Testing legacy-map generation:"
	@REPOSURGEON=$(REPOSURGEON); export REPOSURGEON; TESTOPT="$(TESTOPT)"; export TESTOPT;\
	for test in $(REFLOADS); \
	do \
	    if echo "  $${test}.svn" >&2; \
	    $(REPOSURGEON) "$(TESTOPT)" "read <$${test}.svn" "legacy write -" | grep -v '^reposurgeon:' >/tmp/regress$$$$ 2>/dev/null; \
	    then diff --text -u $${test}.map /tmp/regress$$$$ || exit $(STOPOUT); \
	    else echo "*** Nonzero return status on $${test}!"; exit $(STOPOUT); fi; \
	done
	@rm -f /tmp/regress$$$$

# Regression-testing of repomapper; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
MAPPERTESTS := $(shell ls -1 repomapper*.sh | sed '/.sh/s///')
repomapper-buildregress:
	@REPOMAPPER=$$REPOMAPPER; export REPOMAPPER; \
	for file in $(MAPPERTESTS); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk || exit $(STOPOUT); \
	done
repomapper-regress:
	@echo "=== Running repomapper tests:"
	@REPOMAPPER=$$REPOMAPPER; export REPOMAPPER; \
	status=0; \
	for file in $(MAPPERTESTS); do \
	    ( $(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)') | sed -e '/ ##/s//:/'; \
	    $(SHELL) $${file}.sh | diff --text -u $${file}.chk - || status=1; \
	done; \
	exit $${status}
	@rm -f /tmp/regress$$$$

# Regression-testing of repotool; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
TOOLTESTS := $(shell ls -1 repotool*.sh | sed '/.sh/s///')
repotool-buildregress:
	@REPOTOOL=$$REPOTOOL; export REPOTOOL; \
	for file in $(TOOLTESTS); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh --rebuild || exit $(STOPOUT); \
	done
repotool-regress:
	@echo "=== Running repotool tests:"
	@REPOTOOL=$$REPOTOOL; export REPOTOOL; \
	status=0; \
	for file in $(TOOLTESTS); do \
	    ( $(ECHO) -n "  $${file} "; grep '##' $${file}.sh  || echo ' ## (no description)') | sed -e '/ ##/s//:/'; \
	    $(SHELL) $${file}.sh --regress || status=1; \
	done; \
	exit $${status}


# Regression-testing of repocutter; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
CUTTERTESTS := $(shell ls -1 repocutter*.sh | sed '/.sh/s///')
repocutter-buildregress:
	@REPOMAPPER=$$REPOMAPPER; export REPOMAPPER; \
	for file in $(CUTTERTESTS); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh >$${file}.chk || exit $(STOPOUT); \
	done
repocutter-regress:
	@echo "=== Running repocutter tests:"
	@REPOCUTTER=$$REPOCUTTER; export REPOCUTTER; \
	status=0; \
	for file in $(CUTTERTESTS); do \
	    ( $(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)') | sed -e '/ ##/s//:/'; \
	    $(SHELL) $${file}.sh | diff --text -u $${file}.chk - || status=1; \
	done; \
	exit $${status}
	@rm -f /tmp/regress$$$$

# Regression-testing of Subversion permission-bit and other exceptional cases; look at the *.sh and
# corresponding *.chk files to see which tests this runs.
SVNCHECK := $(shell ls -1 svncheck*.sh | sed '/.sh/s///')
svncheck-buildregress:
	@for file in $(SVNCHECK); do \
	    echo "Remaking $${file}.chk"; \
	    $(SHELL) $${file}.sh -d | $(REPOSURGEON) "$(TESTOPT)" "set testmode" 'read -' 'prefer git' 'write -' >$${file}.chk || exit $(STOPOUT); \
	done
svncheck-regress:
	@echo "=== Running svncheck tests:"
	@status=0; \
	if command -v svn >/dev/null 2>&1 ; \
	then \
	    for file in $(SVNCHECK); do \
		( $(ECHO) -n "  $${file} "; grep --text '##' $${file}.sh  || echo ' ## (no description)' ) | sed -e '/ ##/s//:/'; \
		$(SHELL) $${file}.sh -d | $(REPOSURGEON) "$(TESTOPT)" "set testmode" 'read -' 'prefer git' 'write -' | diff --text -u $${file}.chk - || status=1; \
	    done; \
	else echo "    Skipped, svn missing."; exit 0; \
	fi; \
	exit $${status}
	@rm -f /tmp/regress$$$$

# Test productions end here.

# The result from this is checked in because, as it turns out, the order
# in which the components are archived can vary randomly based on the
# state of the filesystem when it is built.
make-tarball:
	mkdir -p /tmp/tarball
	echo "first sample small file" >/tmp/tarball/snip
	echo "second sample small file" >/tmp/tarball/snap
	chmod a+x /tmp/tarball/snap
	here=`pwd`
	(cd /tmp; tar cf sample.tar tarball)
	mv /tmp/sample.tar .
make-tarball2:
	mkdir -p /tmp/tarball
	echo "first sample2 small file" >/tmp/tarball/bim
	echo "second sample2 small file" >/tmp/tarball/bam
	here=`pwd`
	(cd /tmp; tar cf sample2.tar tarball)
	mv /tmp/sample2.tar .

# Make a new repo and checkout directory to create a Subversion test load.
# Reminder - a branch copy looks like this:
# svn copy file://$PWD/test-repo/trunk file://$PWD/test-repo/branches/foo
# or, within test-checkout, svn copy ^/trunk ^/branches/foo
svn-flat: clean
	svnadmin create test-repo
	svn co file://${PWD}/test-repo test-checkout
svn-branchy: svn-flat
	@cd test-checkout || exit $(STOPOUT); set -x; \
		svn mkdir trunk || exit $(STOPOUT); \
		svn mkdir tags || exit $(STOPOUT); \
		svn mkdir branches || exit $(STOPOUT); \
		echo "Directory layout." | svn commit -F - || exit $(STOPOUT); \
		echo "This is a test Subversion repository" >trunk/README; \
		svn add trunk/README || exit $(STOPOUT); \
		echo "Initial README content." | svn commit -F - || exit $(STOPOUT)
svn-dump:
	@svnadmin dump test-repo 

# end
