## Test of tag deletion by regexp
set echo
read <snarl.svn
tagify
<emptycommit-6> inspect
tag /INITIAL_IMPORT/ delete
write -
