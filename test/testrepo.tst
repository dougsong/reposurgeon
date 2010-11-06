!echo This exercises many delete cases in the test repo
repeat 1
read testrepo.dump
coverage
delete :7,:8
coverage       # Expect this to show case 1 covered.
delete :10,:11
coverage       # Expect this to show case 3 covered.
delete :17,:18
coverage       # Expect this to show case 2 covered.
