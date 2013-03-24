#set title "Efficiency scatter plot"
set xlabel "RP(p)"
set ylabel "LU(RPI(p))"
#set log x
#set log y
set xrange [0:0.4]
set yrange [0:0.4]
set terminal pdf mono size 5,5
set output "LURPIvsRP.pdf"
set size square
set multiplot
set pointsize 0.6
#set style line 6 pt 6
set datafile separator ","
set border 3
set grid
set xtics 0.1 nomirror
set ytics 0.1 nomirror
plot 'LURPIvsRP.csv' using 1:2 with points pt 1 lt 3 notitle 

plot x notitle
#plot 2*x notitle
#plot 0.5*x notitle
