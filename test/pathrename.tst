## Test path rename capability
relax
read <sample1.fi
path README rename REAMDE	# Should succeed
path .gitignore rename REAMDE	# Should fail
write -
