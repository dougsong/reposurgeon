## Test the custom extension feature
exec <<EOF
print("I am a custom extension.")

def length(selection):
    print("Selection length: %d" % len(selection))
EOF
read <testrepo.fi
=C eval length
