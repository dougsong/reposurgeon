## Test --empty modifier on msgin
set relax
read <min.fi
# Expecting failure on this command
msgin --empty-only <<EOF
------------------------------------------------------------------------------
Author: Ralf Schlatterbeck <rsc@runtux.com>
Author-Date: Thu 01 Jan 1970 00:00:00 +0000

Wearing stompy boots.
------------------------------------------------------------------------------
EOF
# And a warning on this command
:2 squash --empty-only
