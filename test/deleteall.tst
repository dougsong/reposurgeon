## Test if commands handling tree contents understand deleteall
echo 1
read <deleteall.fi
set interactive
:13 manifest
[/^README/a] resolve
[/^README$/a] resolve
