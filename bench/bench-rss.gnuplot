set key top lmargin
set title "Reposurgeon resident set size vs readlimit for gcc.svn"
set xlabel "number of SVN revisions read in by Reposurgeon"
set xrange [0:275000]
set ylabel "RSS"
set yrange [0:65000000]
f(x) = a*x + b
g(x) = c*x**2 + d*x + e
fit f(x) file using 1:3 via a,b
fit g(x) file using 1:3 via c,d,e
plot file u 1:3 title "memory (RSS)" lw 2, \
     f(x) title "linear fit" lw 2, \
     g(x) title "quadratic fit" lw 2
