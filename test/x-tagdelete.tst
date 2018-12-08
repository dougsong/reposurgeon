## Test of tag deletion by regexp
echo 1
read <tagify.fi
tagify
<emptycommit-mark5> inspect
tag /emptycommit/ delete
write -

