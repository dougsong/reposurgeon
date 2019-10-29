## test expunging delete ops
echo 1
set quiet
read <deletion.svn
expunge doomed
choose deletion-expunges
inspect
