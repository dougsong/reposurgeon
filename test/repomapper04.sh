#!/bin/sh
## Test processing of additional maps in repomapper

trap 'rm -f /tmp/contrib$$ /tmp/update$$' EXIT HUP INT QUIT TERM

cat >/tmp/contrib$$ <<EOF
fubar = J. Random Fubar <j@random.net>
EOF

cat >/tmp/update$$ <<EOF
fubar = Not J. Random Fubar <j@not-random.net>
foonly = Fred Foonly <fred@foonly.net>
EOF

# Only the foonly line should be merged.
${REPOMAPPER:-repomapper} /tmp/contrib$$ /tmp/update$$ 

#end
