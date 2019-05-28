## Test commit creation

read <min.fi
msgin --create <<EOF
Branch: refs/heads/master
Committer: Eric S. Raymond <esr@thyrsus.com>
Committer-Date: Sat 04 Mar 2006 17:44:41 +0000

This is an example commit.
EOF
$|@max(=C&~$) reparent --rebase
write
