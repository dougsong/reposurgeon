## Test of the tagify command
set echo
read <tagify.fi
tagify
write -
1..:6 tagify --tipdeletes
write -
1..$ tagify --tipdeletes
write -
tagify --canonicalize --tipdeletes
write -
tagify --tagify-merges
write -
