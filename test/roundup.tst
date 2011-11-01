## Test cvspurge and delete pushback
echo 1
read roundup.fi
resolve :1?
cvspurge	# Expect one deleted commit
inspect :39,:42
delete :42 pushback
inspect :39
