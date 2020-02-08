set key top lmargin
set title "Reposurgeon run-time vs readlimit for gcc.svn"
set xlabel "number of SVN revisions read in by Reposurgeon"
set xrange [0:275000]
set ylabel "run-time (s)"
set yrange [0:5100]
f(x) = a*x + b
g(x) = c*x**2 + d*x + e
fit f(x) file using 1:2 via a,b
fit g(x) file using 1:2 via c,d,e
plot file u 1:2 title "run-time" lw 2, \
     f(x) title "linear fit" lw 2, \
     g(x) title "quadratic fit" lw 2
