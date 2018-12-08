## Test the custom extension feature
exec <<EOF
print("I am a custom extension.")

def report(repository,selection):
    print("Repository name: %s" % repository.name)
    print("Selection length: %d" % len(selection))
EOF
read <testrepo.fi
=C eval report(_repository,_selection)

