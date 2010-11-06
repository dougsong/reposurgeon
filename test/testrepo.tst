!echo This exercises many delete cases in the test repo
repeat 1
read testrepo.dump
delete :7,:8
coverage       # Expect this to show case 1 covered.
delete :10,:11
coverage       # Expect this to show case 2 covered.

