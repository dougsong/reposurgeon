## Test of canonicalization-after-commit cases
!echo This exercises many combine cases in the test repo
echo 1
read <testrepo.fi
coverage
squash :7,:8
coverage       # Expect this to show case 1 covered.
squash :10,:11
coverage       # Expect this to show case 3 covered.
squash :17,:18
coverage       # Expect this to show case 2 covered.
squash :25,:26
coverage       # Expect this to show case 4 covered.
squash :29,:30
coverage       # Expect this to show case 6 covered.
resolve 1..$
delete :34	# Test the code that checks for non-D fileops present.
resolve 1..$
