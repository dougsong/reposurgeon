## test expunging delete ops
echo 1
quiet on
verbose 1
read deletion.svn
expunge doomed
choose deletion.svn-expunges
inspect
