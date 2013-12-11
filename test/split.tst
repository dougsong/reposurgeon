## Test the split command
echo 1
verbose 1
quiet on
read <mergeinfo.svn
:19 split at 1
:19 split at 3
:19 split at 2
:24 split at 1
:25 split at 2
prefer git
inspect
