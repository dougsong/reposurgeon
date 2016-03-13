## Test unite of multiple copies of a repo mapped to branches
read <bzr.fi
path ^(.*) rename foo/\1
rename foo
read <bzr.fi
path ^(.*) rename bar/\1
rename bar
unite foo bar
write -
