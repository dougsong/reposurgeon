## Test content filtering
read <sample1.fi
=B filter --shell tr e X
=C filter --shell tr e Y
=B filter --regex /This/THIS PATHETIC HEAP/
=C filter --regex /causing/FROBNICATING/
=C filter --replace /commit./COMMIT./
=C filter --replace /dirYctory/froggle/c
print Following substitution should be a no-op
=C filter --replace /froggle/fraggle/C
=C filter --replace /Eric/Thranduil/
=T filter --replace /Eric/Thorin/
write -
