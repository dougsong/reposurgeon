## Test commit re-ordering
echo 1
read <reorder.fi

# basic operation
:22,:24,:26,:21,:30,:28 reorder
20..31 index
20..31 & =C inspect

# boundary case: first commit
:5,:2 reorder
1..6 index
1..6 & =C inspect

# boundary case: last commit
:32,:33,:31 reorder
32..$ index
32..$ & =C inspect

# boundary case: maximum event: multiple children
:7,:2 reorder
7..10,13 index
7..10,13 & =C inspect

# boundary case: minimum event: multiple parents
:19,:17 reorder
17..22 index
17..22 & =C inspect

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

# warning: no fileops after re-order
:32,:30,:31:28 reorder
