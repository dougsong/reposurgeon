## Test the split command
echo 1
verbose 1
quiet on
read <mergeinfo.svn
split :19 at 1
split :19 at 3
split :19 at 2
split :24 at 1
split :25 at 2
prefer git
inspect
