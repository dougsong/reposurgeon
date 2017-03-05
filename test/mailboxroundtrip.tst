## Test mailbox_out/mailbox_in round-trip

read <min.fi
mailbox_out >/tmp/rsmailbox$$$$
mailbox_in </tmp/rsmailbox$$$$
shell rm /tmp/rsmailbox$$$$
write -
