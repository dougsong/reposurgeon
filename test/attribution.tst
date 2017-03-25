## Test attribution manipulation
echo 1

# error: no repo
attribution

read <multitag.fi

# error: shlex.parse failure
attribution missing "quotation mark

# error: no event selection
attribution delete

# error: no commits or tags selected
=R | =B attribution

# error: unrecognized action
1..$ attribution bogus

:2..:4 attribution 2 resolve
:2..:4 attribution $ resolve
:2..:4 attribution 1..$ resolve
:2..:4 attribution 1,$ resolve
:2..:4 attribution 1 | 2 resolve
:2..:4 attribution 1 & (2) resolve
:2..:4 attribution ~2 resolve
:2..:4 attribution @min(1..$) resolve
:2..:4 attribution @max(1..$) resolve
:2..:4 attribution @amp(1) resolve
:2..:4 attribution @pre(2) resolve
:2..:4 attribution @suc(1) resolve
:2..:4 attribution @srt(2,1) resolve
1..$ attribution @amp(~1) resolve label

# error: bogus selection (tag has only "tagger" attribution at index 1)
10 attribution 2 resolve

1..$ attribution =C resolve committer only
1..$ attribution =A resolve author only
1..$ attribution =T resolve tagger only
1..$ attribution =CAT resolve all

# error: bogus visibility flag
1..$ attribution =X resolve

@min(=C) attribution /Julien/ resolve match any
@min(=C) attribution /Julien/n resolve match name
@min(=C) attribution /frnchfrgg/e resolve match email
@min(=C) attribution /Julien/e resolve name not match email
@min(=C) attribution /frnchfrgg/n resolve email not match name
@min(=C) attribution /nomatch/ resolve no match

# error bogus regex match flag
@min(=C) attribution /Julien/x resolve

attribution
attribution show
1..$ attribution show
=C attribution 2 show
=T attribution 1 show
@max(=C) attribution =A show
# empty attribution selection
@max(=T) attribution =A show

#error: incorrect number of arguments
attribution show bogus

:2 attribution show
:2 attribution =C set 2017-03-21T01:23:45Z
:2 attribution show
:2 attribution =C set sunshine@sunshineco.com
:2 attribution show
:2 attribution =C set "Eric Sunshine"
:2 attribution show
:2 attribution @min(=A) set "1234567890 +0500" sunshine@sunshineco.com "Eric Sunshine"
:2 attribution show
:2 attribution =A set "Eric S. Raymond" esr@thyrsus.com
:2 attribution show
:2 attribution =A set sunshine@sunshineco.com 2017-03-21T01:23:45Z
:2 attribution show

# error: incorrect number of arguments or repeated arguments
1..$ attribution set
1..$ attribution set Name email@example.com "1234567890 +0500" junk
1..$ attribution set Name1 email@example.com Name2
1..$ attribution set email1@example.com Name email2@example.com
1..$ attribution set "1234567890 +0500" Name 2017-03-21T01:23:45Z

:5 attribution show
:5 attribution =A delete
:5 attribution show
# no attribution selection: delete all authors
:4 attribution show
:4 attribution delete
:4 attribution show
# multiple events
1..$ attribution show
1..$ attribution =A delete
1..$ attribution show

# error: incorrect number of arguments
1..$ attribution delete bogus
# error: no event selection
attribution =A delete
# error: cannot delete mandatory committer or tagger
@max(=C) attribution =C delete
@max(=T) attribution =T delete

:2 attribution show
:2 attribution append "Eric S. Raymond" esr@thyrsus.com "1234567890 +0500"
:2 attribution show
:2 attribution append "Eric Sunshine" sunshine@sunshineco.com 2017-03-21T01:23:45Z
:2 attribution show
:2 attribution /sunshine/ & =A prepend "Micky Mouse" toon@disney.com 1979-04-01T12:12:12Z
:2 attribution show
:2 attribution /esr/e prepend Example example@example.com "1234567890 +0500"
:2 attribution show

# error: incorrect number of arguments
1..$ attribution prepend
1..$ attribution append Name email@example.com "1234567890 +0500" junk
# error: no event selection
attribution =A prepend
# error: cannot add committer or tagger (only 1 allowed)
@max(=C) attribution =C prepend "Eric Sunshine" sunshine@sunshineco.com 2017-03-21T01:23:45Z
@max(=T) attribution =T append "Eric Sunshine" sunshine@sunshineco.com 2017-03-21T01:23:45Z
# error: cannot add author to tag
@max(=T) attribution append "Eric Sunshine" sunshine@sunshineco.com 2017-03-21T01:23:45Z

:2 attribution show
:2 attribution =A prepend "Eric Sunshine"
:2 attribution show
:2 attribution =A append esr@thyrsus.com
:2 attribution show
:2 attribution /disney/e append Pluto othertoon@disney.com
:2 attribution show

# infer author name and date from committer
:4 attribution show
:4 attribution append frnchfrgg@free.fr
:4 attribution show

# error: unable to infer name, email
:4 attribution append 2017-03-21T01:23:45Z
:4 attribution prepend Nobody
:4 attribution append nobody@nowhere.com
