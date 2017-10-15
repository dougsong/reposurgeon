## Test incorporate command - before case

trap "rm -fr /tmp/sub$$ tarball.tar" 0 12 2 15

mkdir /tmp/sub$$

# Build a tarball to be incorporated
mkdir /tmp/sub$$/tarball
echo "first sample small file" >/tmp/sub$$/tarball/snip
echo "second sample small file" >/tmp/sub$$/tarball/snap
chmod a+x /tmp/sub$$/tarball/snap
here=`pwd`
(cd /tmp/sub$$; tar cf tarball.tar tarball)
mv /tmp/sub$$/tarball.tar .

# Incorporate it
reposurgeon "set testmode" "read <min.fi" "@min(=C) incorporate tarball.tar" "write -"
