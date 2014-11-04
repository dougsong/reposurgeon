## Test the add primitive
read <sample2.fi
:15 add D .gitignore
:17 add M 100755 :9 hello
# Next one is expected to fail
:8 add C .gitignore wibble
:8 add C README README-STASH
write -
