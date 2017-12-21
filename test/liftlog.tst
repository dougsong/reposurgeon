## Test mining authorship from Changelog
read <liftlog.fi
# Should be different TZ than the liftlog committer so we
# can see that a substitution has occurred.
authors read <<EOF
hilda = Hilda J. Foonly <hilda@foonly.org> America/Los_Angeles
+ Hildegarde J. Foonly <hilda@not-foonly.org> America/New_York
EOF
changelogs
write -

