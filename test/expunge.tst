## Test file expunge operation
verbose 1
echo 1
quiet on
read --nobranch <expunge.svn
1..$ expunge /^releases\/v1.0\/.*/
choose
