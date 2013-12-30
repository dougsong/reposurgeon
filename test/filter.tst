## Test content filtering
read <sample1.fi
=B filter --shell tr e X
=C filter --shell tr e Y
=C filter --regex /causing/FROBNICATING/
write -
