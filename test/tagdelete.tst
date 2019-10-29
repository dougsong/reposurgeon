## Test of tag deletion by regexp
set echo
read <tagify.fi
tagify
<emptycommit-mark5> inspect
tag /emptycommit/ delete
write -

