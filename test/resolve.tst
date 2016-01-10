## Test selection sets
read <debranch.svn
echo 1
1,3 resolve
1..3 resolve
:2,:4 resolve
:2..:4 resolve
<1>,<2>,<3> resolve
<1>..<2> resolve
<3>..<7> resolve
3,1 resolve
@srt(3,1) resolve
