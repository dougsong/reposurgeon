## Test the split command
set echo
set interactive
set quiet
set relax
read <mergeinfo.svn
:6 split at 2
prefer git
inspect
print "Avoid having a last command that fails"
