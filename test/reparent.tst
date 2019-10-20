## Reparenting parents with and w/o tree preservation
echo 1
relax
read <simple.fi
set interactive
127 inspect
127..$ manifest
127,29 reparent
127 inspect
127..$ manifest
129,3 reparent --rebase
129 inspect
129 manifest

129 reparent
@par(129) resolve parents of root commit
129,127,3 reparent
@par(129) resolve parents of octopus merge

# this next one should fail because it would create a cycle
:123,:121 reparent --use-order
:121 inspect
:121 manifest
# swap the order of :123 and :121
:119,:123 reparent --use-order
:123 inspect
:123 manifest
(:119..:123)|(:119..:121) index
:123,:121 reparent --use-order
:121 inspect
:121 manifest
(:119..:123)|(:119..:121) index
