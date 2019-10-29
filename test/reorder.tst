## Test commit re-ordering
set quiet
set echo
set relax
read <reorder.fi

# basic operation
:22,:24,:26,:21,:30,:28 reorder
write

# boundary case: first commit
:5,:2 reorder
write

# boundary case: last commit
:32,:33,:31 reorder
write

# boundary case: maximum event: multiple children
:7,:2 reorder
write

# boundary case: minimum event: multiple parents
:19,:17 reorder
write

# error: no repo
drop reorder
reorder
read <reorder.fi

# error: incorrect number of arguments
1..$ reorder now

# error: no event selection
reorder

# error: no commits in selection
2,4,5 reorder

# error: range not contiguous
:9,:14,:16 reorder

# error: non-linear history: multiple children
:9,:7 reorder
# error: non-linear history: multiple parents
:17,:16 reorder

# warning: only 1 commit selected; nothing to re-order
:2 reorder
:2..:4 reorder

# warning: commits already in desired order
:2,:5,:7 reorder

# warning: fileop references non-existent path
:26,:24 reorder

# suppress warnings
drop reorder
read <reorder.fi
:26,:24 reorder --quiet

# warning: no fileops after re-order
:32,:30,:31:28 reorder
