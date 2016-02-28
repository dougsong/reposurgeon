## Test password-processing -p mode of repomapper

trap "rm -f /tmp/contrib$$ /tmp/passwd$$" 0 12 2 15

cat >/tmp/contrib$$ <<EOF
fubar = J. Random Fubar <j@random.net>
foonly = foonly <foonly>
EOF

cat >/tmp/passwd$$ <<EOF
foonly:x:1000:1000:Fred Föonly,,,:/home/foonly:/bin/bash
EOF


# Only the foonly line should be modified
${REPOMAPPER:-repomapper} -p /tmp/passwd$$ /tmp/contrib$$ 2>&1 | sort

#end
