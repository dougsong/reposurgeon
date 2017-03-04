## Test mailbox_in adding author to commit

# Export to mailbox format, add Author: and Author-Date: headers, and
# re-import.
#
# Note: mailbox_out/mailbox_in does not round-trip cleanly: an extra newline
# is added at the end of the commit message. The extra ${/^$/d;} sed
# expression makes this test robust against that bug someday being fixed (and
# can be removed at that time).
read <min.fi
@min(=C) mailbox_out >/tmp/rsmailboxout$$$$
shell sed \
  '/^Committer:/{p;s/.*/Author: Eric Sunshine <sunshine@sunshineco.com>/;};\
  /^Committer-Date:/{p;s/Committer/Author/;};\
  ${/^$/d;}'\
  </tmp/rsmailboxout$$$$ >/tmp/rsmailboxin$$$$
mailbox_in </tmp/rsmailboxin$$$$
shell rm /tmp/rsmailboxout$$$$ /tmp/rsmailboxin$$$$
write -
