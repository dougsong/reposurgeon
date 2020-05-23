#!/bin/sh
## Test incomplete (-i) mode of repomapper

trap 'rm -f /tmp/contrib$$' EXIT HUP INT QUIT TERM

cat >/tmp/contrib$$ <<EOF
fubar = J. Random Fubar <j@random.net>
foonly = foonly <foonly>
EOF

# Only the foonly line should be emitted
${REPOMAPPER:-repomapper} -i /tmp/contrib$$

#end
