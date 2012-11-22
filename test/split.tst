## test the split command
verbose 1
read mergeinfo.svn
split :19 at 1
split :19 at 3
split :19 at 2
split :24 at 1
split :25 at 2
write
