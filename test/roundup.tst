## Test squash --pushback
set echo
read <roundup.fi
set interactive
:1? resolve
:39,:42 inspect
:42 squash --pushback
:39 inspect
