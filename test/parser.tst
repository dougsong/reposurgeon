## Tests of selection-set syntax and parser features
echo 1
read simple.fi
resolve =H
resolve 15
resolve =TR
resolve 24..97
resolve 24..97&=C
resolve 24..97 ?
resolve {24..97 ?} & 20..40
resolve {24..97 ?} & {20..40 ?}
resolve 24..97 | 20..40
resolve {24..97 | 20..40} & =C
resolve 24..97 & =C | 20..40 & =C
resolve 24..97 & {=C | 20..40}
resolve 3,:15
resolve (master)
resolve <lightweight-sample>
resolve (annotated-sample)
resolve <annotated-sample>
resolve /regression/
resolve /Raymond/
resolve [Makefile]
resolve [/Ma.*le/]
resolve [/^Ma.*le$/]
resolve [/D.ME.\.txt/]
resolve ["READ[ME].txt"]
resolve ['READ[ME].txt']
resolve [*"Makefile"]
resolve [*/^Make/]
resolve [/^test/]
resolve [@/^test/]
resolve [@*/^r/]
resolve [@*/r/]
resolve <2010-10-27T18:43:32Z>
resolve <2010-10-27T12:07:32Z!esr@thyrsus.com>
# Test here-doc syntax
echo 0
authors read <<EOF
esr = Eric Raymond <esr@thyrsus.com>
EOF
echo 1
write
# Test multiline commands
resolve \
<annotated-sample>
resolve \
24..97\
&\
=C
