## Test selection sets
set relax
read <testrepo.fi
set echo
set interactive
1,3 resolve
1..3 resolve
:2,:4 resolve
:2..:4 resolve
3,1 resolve
@srt(3,1) resolve
@rev(3,4,1) resolve
# Bogus inputs
1.3 resolve
1...3 resolve
