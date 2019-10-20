## Test squash --pushback
echo 1
read <roundup.fi
set interactive
:1? resolve
:39,:42 inspect
:42 squash --pushback
:39 inspect
