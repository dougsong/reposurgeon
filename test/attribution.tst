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
