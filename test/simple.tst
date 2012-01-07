## Tests of selection-set syntax, tags, history, and expunge
echo 1
read simple.fi
index
resolve =H
resolve 15
resolve =TR
resolve 24..97
resolve 24..97&=C
resolve 3,:15
resolve (master)
resolve <lightweight-sample>
resolve (annotated-sample)
resolve <annotated-sample>
resolve /regression/
resolve /Raymond/
resolve [Makefile]
resolve <2010-10-27T18:43:32Z>
resolve <2010-10-27T12:07:32Z!esr@thyrsus.com>
tags
history
verbose 1
paths
expunge 1..$ theory.txt
paths
verbose 0
checkout 116 foobar
!ls foobar
!rm -fr foobar
diff 101,103
choose simple-expunges
paths sub foo
paths sup
write

