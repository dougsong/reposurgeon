echo 1
read roundup.fi
resolve :1?
cvslift	# Expect one deleted commit
inspect :39,:42
delete :42 pushback
inspect :39
