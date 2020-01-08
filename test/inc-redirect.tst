## Test incorporate command with input redirect
set testmode
read <min.fi
@min(=C) incorporate <<EOF
sample.tar
sample2.tar
EOF
write -
