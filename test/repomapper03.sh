#!/bin/sh
## Test password-file processing code in repomapper

trap 'rm -f /tmp/contrib$$ /tmp/passwd$$' EXIT HUP INT QUIT TERM

cat >/tmp/contrib$$ <<EOF
fubar = J. Random Fubar <j@random.net>
foonly = foonly <foonly>
EOF

cat >/tmp/passwd$$ <<EOF
foonly:x:1000:1000:Fred Föonly,,,:/home/foonly:/bin/bash
EOF


# Only the foonly line should be modified
${REPOMAPPER:-repomapper}  /tmp/contrib$$ /tmp/passwd$$ 2>&1 | sort

#end
