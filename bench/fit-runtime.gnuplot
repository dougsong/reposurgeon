f(x) = a*x**2 + b*x + c
fit f(x) file using 1:2 via a,b,c
plot file u 1:2 title "run-time" lw 2, \
     f(x) title "quadratic fit" lw 2
