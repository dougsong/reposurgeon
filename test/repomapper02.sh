#!/bin/sh
## Test host suffixing in repomapper

trap 'rm -f /tmp/contrib$$' EXIT HUP INT QUIT TERM

cat >/tmp/contrib$$ <<EOF
fubar = J. Random Fubar <j@random.net>
foonly = foonly <foonly>
EOF

# Only the foonly line should be modified
${REPOMAPPER:-repomapper} -h frobnitz.net /tmp/contrib$$

#end
