## Test if commands handling tree contents understand deleteall
echo 1
read <deleteall.fi
:13 manifest
[/^README/*] resolve
[/^README$/*] resolve
