## Test of the tagify command
echo 1
read <tagify.fi
tagify
write -
tagify 1..:6 --tipdeletes
write -
tagify 1..$ --tipdeletes
write -
tagify --canonicalize --tipdeletes
write -
