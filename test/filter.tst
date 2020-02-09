## Test content filtering
read <sample1.fi
set interactive
print Testing shell filtering of blobs
=B filter --shell tr e X
print Testing shell filtering of commits
=C filter --shell tr e Y
print Testing regexp filtering of blobs
=B filter --regex /This/THIS PATHETIC HEAP/
print Testing regexp filtering of commits
=C filter --regex /causing/FROBNICATING/
print Testing replace filtering of commits
=C filter --replace /commit./COMMIT./
print Testing replace filtering of commits, comment only
=C filter --replace /dirYctory/froggle/c
print Following substitution should be a no-op, committer only
=C filter --replace /froggle/fraggle/C
print Testing replace filtering of commits (all fields)
=C filter --replace /Eric/Thranduil/
print Testing replace filtering of tags
=T filter --replace /Eric/Thorin/
print Testing %PATHS% feature
=B filter --shell sed /spacXr/s//%PATHS%/ || cat
clear interactive
write -
