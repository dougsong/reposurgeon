## Test msgin adding author to commit

# Export to msgbox format, add Author: and Author-Date: headers, and
# re-import.
read <min.fi
@min(=C) msgout >/tmp/rsmsgboxout$$$$
shell sed \
  '/^Committer:/{p;s/.*/Author: Eric Sunshine <sunshine@sunshineco.com>/;};\
  /^Committer-Date:/{p;s/Committer/Author/;}'\
  </tmp/rsmsgboxout$$$$ >/tmp/rsmsgboxin$$$$
print Modification input begins
shell cat /tmp/rsmsgboxin$$$$
print Modification input ends
msgin </tmp/rsmsgboxin$$$$
shell rm /tmp/rsmsgboxout$$$$ /tmp/rsmsgboxin$$$$
write -
