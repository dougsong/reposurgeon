## Test --empty modifier on mailbox_in
read <min.fi
# Expecting failure on this command
mailbox_in --empty <<EOF
------------------------------------------------------------------------------
Committer: Ralf Schlatterbeck <rsc@runtux.com>
Committer-Date: Thu 01 Jan 1970 00:00:00 +0000

Wearing stompy boots.
------------------------------------------------------------------------------
EOF
