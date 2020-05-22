## Test the setfield-commitdate and timeoffset commands
read <min.fi
:4 setfield commitdate "0 +0000"
timequake
write -
