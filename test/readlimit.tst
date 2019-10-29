## Test readlimit
set echo
readlimit 3
read <simpletag.svn
prefer git
write -
# This should yield an EOF message.
read <binary.svn
prefer git
write -
# This should not
read <bs.fi
prefer git
write -
# This should
read <utf8.fi
prefer git
write -
