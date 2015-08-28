## Test host suffixing in repomapper

trap "rm -f /tmp/contrib$$" 0 12 2 15

cat >/tmp/contrib$$ <<EOF
fubar = J. Random Fubar <j@random.net>
foonly = foonly <foonly>
EOF

# Only the foonly line should be modified
repomapper -h frobnitz.net /tmp/contrib$$

#end
