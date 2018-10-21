## Test Check-Text match and mismatch
read <min.fi
msgin <<EOF
------------------------------------------------------------------------------
Committer: Ralf Schlatterbeck <rsc@runtux.com>
Committer-Date: Thu 01 Jan 1970 00:00:00 +0000
Check-Text: First commit.

Alter first commit, check text is correct.
EOF
msgin <<EOF
------------------------------------------------------------------------------
Committer: Ralf Schlatterbeck <rsc@runtux.com>
Committer-Date: Thu 01 Jan 1970 00:00:00 +0000
Check-Text: Second commit.

This alteration should fail, check text is not correct.
EOF
write -
