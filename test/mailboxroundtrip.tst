## Test msgout/msgin round-trip

read <min.fi
msgout >/tmp/rsmsgbox$$$$
msgin </tmp/rsmsgbox$$$$
shell rm /tmp/rsmsgbox$$$$
write -
