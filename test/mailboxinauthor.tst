## Test mailbox_in adding author to commit

# Export to mailbox format, add Author: and Author-Date: headers, and
# re-import.
read <min.fi
@min(=C) mailbox_out >/tmp/rsmailboxout$$$$
shell sed \
  '/^Committer:/{p;s/.*/Author: Eric Sunshine <sunshine@sunshineco.com>/;};\
  /^Committer-Date:/{p;s/Committer/Author/;}'\
  </tmp/rsmailboxout$$$$ >/tmp/rsmailboxin$$$$
mailbox_in </tmp/rsmailboxin$$$$
shell rm /tmp/rsmailboxout$$$$ /tmp/rsmailboxin$$$$
write -
