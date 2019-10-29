## test expunging delete ops
set echo
set quiet
read <deletion.svn
expunge doomed
choose deletion-expunges
inspect
