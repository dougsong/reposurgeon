## Tests of selection-set syntax and parser features
echo 1
read <simple.fi
=H resolve Special set resolution
15 resolve Event number resolution
=TR resolve Special combination
@min(=TR) resolve min operator
@max(=TR) resolve max operator
24..97 resolve Range
24..97&=C resolve Range and conjunction
24..97? resolve Neighborhood extension
(24..97?) & 20..40 resolve Conjunct
@min(=C)&@max(=C) resolve Conjunct non-overlapping relative position
(24..97?) & (20..40?) resolve Conjunct with grouping
24..97 | 20..40 resolve Disjunct
@max(=C)|@max(=C) resolve Disjunct overlapping relative position
(24..97 | 20..40) & =C resolve Commit selection
24..97 & =C | 20..40 & =C resolve Disjunct and conjunct
24..97 & (=C | 20..40) resolve Parenthesis grouping
3|5 resolve Disjunct
3|5|7 resolve Disjunct chain
3..7&5 resolve Conjunct
3..7&3..5&5 resolve Conjunct chain
7? resolve Neighborhood
7?? resolve Neighborhood chain
3,:15 resolve Comma syntax selecting doubleton
/master/b resolve Branch
/operating theater/B resolve Blobs
<lightweight-sample> resolve Branch tip
/annotated-sample/b resolve Tag
<annotated-sample> resolve Tag location
/regression/ resolve Text search
/Raymond/ resolve Commit comment search
[Makefile] resolve Path search
~[Makefile] resolve Negated path search 
=B & [Makefile] resolve Blob path search
=C & [Makefile] resolve Commit path search
[/Ma.*le/] resolve Regexp commit search
=B & [/Ma.*le/] resolve Regexp patch search for blobs
=C & [/Ma.*le/] resolve Regexp patch search for commits
[/^Ma.*le$/] resolve Anchored regexp commit search
=B & [/^Ma.*le$/] resolve Anchored regexp patch search for blobs
=C & [/^Ma.*le$/] resolve Anchored regexp patch search for commits
[/D.ME.\.txt/] resolve Regexp escape
[/Makefile/a] resolve Author match
[/^Make/a] resolve Anchored author match
[/^test/] resolve Text search
[/^test/c] resolve Comment search
[/^r/ca] resolve Commit and author search
[/r/ca] resolve Commit and author search
<2010-10-27T18:43:32Z> resolve Date resolution
<2010-10-27T12:07:32Z!esr@thyrsus.com> resolve Action stamp resolution
<2010-10-27> resolve Partial-date resolution
@max(~$)|$ resolve function argument parsing
@amp(1) resolve resolve amplified nonempty set
@amp(/mytzlpyk/) resolve amplified empty set
@suc(<2010-10-27T17:25:36Z>) resolve successor function call 
@pre(<2010-10-27T17:25:36Z>) resolve predecessor function call 
# Test here-doc syntax
echo 0
authors read <<EOF
esr = Eric Raymond <esr@thyrsus.com>
EOF
echo 1
write -
# Test multiline commands
resolve \
<annotated-sample>
resolve \
24..97\
&\
=C
