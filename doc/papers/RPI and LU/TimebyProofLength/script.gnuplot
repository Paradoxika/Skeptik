#set title "Efficiency scatter plot"
set xlabel "Proofs (ordered by proof length)"
set ylabel "Time (in seconds)"
#set log x
#set log y
set xrange [-1:12]
#set yrange [0:0.4]
set terminal pdf mono dashed size 8,4 # size 5,5
set output "TimebyProofLength.pdf"
#set size square
#set multiplot
set pointsize 0.6
set style line 6 pt 6
set datafile separator ","
set border 3
set grid
set style data lines
set xtics nomirror rotate by -45
set ytics 100
set key at 2,400000
plot 'TimebyProofLength.csv' using 4:xtic(3) title columnheader(4), \
 'TimebyProofLength.csv' using 5 title columnheader(5), \
 'TimebyProofLength.csv' using 6 title columnheader(6), \
 'TimebyProofLength.csv' using 7 title columnheader(7), \
 'TimebyProofLength.csv' using 8 title columnheader(8)
