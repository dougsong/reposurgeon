set key top lmargin
set title "Reposurgeon run-time vs readlimit for gcc.svn"
set xlabel "number of SVN revisions read in by Reposurgeon"
set xrange [0:50000]
set ylabel "run-time (s)"
set yrange [0:250]
plot for [i=1:words(files)] word(files, i) using 1:2 title word(files, i) noenhanced lw 2
