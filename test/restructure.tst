## Test of canonicalization-after-commit cases
!echo This exercises many restructure cases in the test repo
echo 1
read <testrepo.fi
coverage
restructure :7,:8
coverage       # Expect this to show case 1 covered.
restructure :10,:11
coverage       # Expect this to show case 3 covered.
restructure :17,:18
coverage       # Expect this to show case 2 covered.
restructure :25,:26
coverage       # Expect this to show case 4 covered.
restructure :29,:30
coverage       # Expect this to show case 6 covered.
resolve 1..$
delete :34	# Test the code that checks for non-D fileops present.
resolve 1..$
