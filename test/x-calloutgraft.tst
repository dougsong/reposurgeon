## Test graft using a root callout and no selection set
read <debranch3.fi
/alternate/b delete
# Relies on the fact that callout.chk was created from the branch just deleted
read <callout.chk
choose debranch3
graft callout.chk
# The result should be topologically equivalent to the original debranch3.fi
write -
