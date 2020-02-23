## Test update (-u) mode of repomapper

trap "rm -f /tmp/contrib$$ /tmp/update$$" 0 12 2 15

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
