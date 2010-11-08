!echo This exercises many delete cases in the test repo
repeat 1
read testrepo.fi
coverage
delete :7,:8
coverage       # Expect this to show case 1 covered.
delete :10,:11
coverage       # Expect this to show case 3 covered.
delete :17,:18
coverage       # Expect this to show case 2 covered.
delete :25,:26
coverage       # Expect this to show case 4 covered.
delete :29,:30
coverage       # Expect this to show case 6 covered.
