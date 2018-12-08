## Test use of legacy IDs after a blob command
read <x-blob-id.svn
blob </dev/null
blob </dev/null
<2> append "appended to legacy rev 2 comment\n"
prefer git
write -
