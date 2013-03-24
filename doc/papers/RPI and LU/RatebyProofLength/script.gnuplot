#set title "Efficiency scatter plot"
set xlabel "Proofs (ordered by proof length)"
set ylabel "Compression rate"
#set log x
#set log y
set xrange [-1:12]
#set yrange [0:0.4]
set terminal pdf mono dashed size 8,4 # size 5,5
set output "RatebyProofLength.pdf"
#set size square
#set multiplot
set pointsize 0.6
set style line 6 pt 6
set datafile separator ","
set border 3
set grid
set style data lines
set xtics nomirror rotate by -45
set ytics 0.1
set key at 2,0.3
plot 'RatebyProofLength.csv' using 4:xtic(3) title columnheader(4), \
 'RatebyProofLength.csv' using 5 title columnheader(5), \
 'RatebyProofLength.csv' using 6 title columnheader(6), \
 'RatebyProofLength.csv' using 7 title columnheader(7), \
 'RatebyProofLength.csv' using 8 title columnheader(8)
