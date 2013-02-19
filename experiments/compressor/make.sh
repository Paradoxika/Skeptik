#!/bin/bash

#ToDo: Relative paths should be used here
PATH=/home/jogo/gsoc/git/scripts/:$PATH
export PERL5LIB=/home/jogo/gsoc/git/scripts
cd /home/jogo/gsoc/git/experiments/compressor



# Compute data files

cat slice1.csv slice2.csv slice3.csv slice4.csv slice5.csv slice6.csv slice7.csv slice8.csv slice9.csv | cut -d, -f 1,2,4- >full.csv
cat header-full.csv full.csv >/home/jogo/Dropbox/Experiment/full.csv
LFUL=$( wc -l full.csv | sed 's: .*::' )

( cut -d, -f 1-161,176-182,197-203 full.csv
  cat slice7m.csv slice8m.csv slice9m.csv slice10m.csv | cut -d, -f 1,2,4-
) >medium.csv
cut -d, -f 1-161,176-182,197-203 header-full.csv >header-medium.csv
cat header-medium.csv medium.csv >/home/jogo/Dropbox/Experiment/medium.csv
LMED=$( wc -l medium.csv | sed 's: .*::' )

#             *  LU   RPI   RPI_R LURPI _R    RPILU _R    3pass   LUniv   -RPI    _R      RPILUniv _R     RednRec Split   DAG
( cut -d, -f 1-6,8-13,22-27,29-34,36-41,43-48,50-55,57-62,106-111,113-118,120-125,127-132,134-139,141-146,148-153,155-160,169-174 medium.csv
  cat slice9l.csv | cut -d, -f 1,2,4-
) >light.csv
cut -d, -f 1-6,8-13,22-27,29-34,36-41,43-48,50-55,57-62,106-111,113-118,120-125,127-132,134-139,141-146,148-153,155-160,169-174 header-medium.csv >header-light.csv
cat header-light.csv light.csv >/home/jogo/Dropbox/Experiment/light.csv
LLIG=$( wc -l light.csv | sed 's: .*::' )


# Per algo aggregates

cut -d, -f 1-22,25,28     header-full >header-medium
cut -d, -f 1,3-8,15-22,28 header-full >header-light

( cat header-full
  csvaggregate full.csv "%o + (%_/${LFUL}000)" 7,14,21,28,35,42,49,50,63,70,77,84,91,98,105,112,119,126,133,140,147,154,161,168,175,182,189,196
  csvaggregate full.csv "%o + ((1 - (%_/%2)) / ${LFUL})" 9,16,23,30,37,44,51,58,65,72,79,86,93,100,107,114,121,128,135,142,149,156,163,170,177,184,191,198
) >nodes-average-full.csv

{ cat header-medium
  csvaggregate medium.csv "%o + (%_/${LMED}000)" 7,14,21,28,35,42,49,50,63,70,77,84,91,98,105,112,119,126,133,140,147,154,161,168
  csvaggregate medium.csv "%o + ((1 - (%_/%2)) / ${LMED})" 9,16,23,30,37,44,51,58,65,72,79,86,93,100,107,114,121,128,135,142,149,156,163,170
} >nodes-average-medium.csv

{ cat header-light
  csvaggregate light.csv "%o + (%_/${LLIG}000)" 6,12,18,24,30,36,42,48,54,60,66,72,78,84,90,96
  csvaggregate light.csv "%o + ((1 - (%_/%2)) / ${LLIG})" 8,14,20,26,32,38,44,50,56,62,68,74,80,86,92,98
} >nodes-average-light.csv

( cat header-full
  csvaggregate full.csv "%o + (%_/${LFUL}000)" 7,14,21,28,35,42,49,50,63,70,77,84,91,98,105,112,119,126,133,140,147,154,161,168,175,182,189,196
  csvaggregate -l "1-(%_/%0)" full.csv '%o + %_' 2,9,16,23,30,37,44,51,58,65,72,79,86,93,100,107,114,121,128,135,142,149,156,163,170,177,184,191,198
) >nodes-total-full.csv

( cat header-medium
  csvaggregate medium.csv "%o + (%_/${LMED}000)" 7,14,21,28,35,42,49,50,63,70,77,84,91,98,105,112,119,126,133,140,147,154,161,168
  csvaggregate -l "1-(%_/%0)" medium.csv '%o + %_' 2,9,16,23,30,37,44,51,58,65,72,79,86,93,100,107,114,121,128,135,142,149,156,163,170
) >nodes-total-medium.csv

( cat header-light
  csvaggregate light.csv "%o + (%_/${LLIG}000)" 6,12,18,24,30,36,42,48,54,60,66,72,78,84,90,96
  csvaggregate -l "1-(%_/%0)" light.csv '%o + %_' 2,8,14,20,26,32,38,44,50,56,62,68,74,80,86,92,98
) >nodes-total-light.csv
  

# function

function two_common { # h v # file # hname vname #
  cat <<EOT
\begin{figure}[hbt]
  \begin{subfigure}{0.5\textwidth}
    \centering
EOT
  let a=$1+2
  let b=$2+2
  mkcloudid -h "$a:$4" -v "$b:$5" -r 2 -d 0.1 $3
  cat <<EOT
    \caption{Nodes compression}
  \end{subfigure}
  \begin{subfigure}{0.5\textwidth}
    \centering
EOT
  let a=$a+1
  let b=$b+1
  mkcloudid -h "$a:$4" -v "$b:$5" -r 3 -d 0.05 $3
  cat <<EOT
    \caption{Axioms compression}
  \end{subfigure}
  \begin{subfigure}{0.5\textwidth}
    \centering
EOT
  let a=$a+1
  let b=$b+1
  mkcloudid -h "$a:$4" -v "$b:$5" -r 4 -d 0.05 $3
  cat <<EOT
    \caption{Variables compression}
  \end{subfigure}
  \begin{subfigure}{0.5\textwidth}
    \centering
EOT
}

function two_generic { # file nb_measures # hcol hname vcol vname divx #
  let c=$3*$2
  let d=$5*$2
  two_common $c $d "$1" "$4" "$6"
  mkcloudid -h "$c:$4" -v "$d:$6" -f 0.001 -d $7 $1
  cat <<EOT
    \caption{Duration in seconds}
  \end{subfigure}
EOT
  echo "  \\caption{Comparing $4 and $6}"
  echo '\end{figure}'
}
function two_full   { two_generic full.csv   7 "$@" ; }
function two_medium { two_generic medium.csv 7 "$@" ; }
function two_light  { two_generic light.csv  6 "$@" ; }

function two_rep_generic { # file nb_measures # hcol hname vcol vname divx #
  let c=$3*$2
  let d=$5*$2
  two_common $c $d "$1" "$4" "$6"
  let a=$c+1
  let b=$d+1
  mkcloudid -h "$a:$4" -v "$b:$6" -d $7 $1
  cat <<EOT
    \caption{Number of iterations}
  \end{subfigure}
EOT
  echo "  \\caption{Comparing $4 and $6}"
  echo '\end{figure}'
}
function two_rep_full   { two_rep_generic full.csv   7 "$@" ; }
function two_rep_medium { two_rep_generic medium.csv 7 "$@" ; }
function two_rep_light  { two_rep_generic light.csv  6 "$@" ; }

function group_no_generic { # kind colstep # caption algos-range #
  cat <<EOT
\begin{table}[hbt]
  \centering
EOT
  mktab -s $2 "$1.csv" $4 '2:Nodes Compression,3:Axioms Compression' <"header-$1"
  echo "  \\caption{$3}"
  echo '\end{table}'
}
function group_no_full   { group_no_generic full   7 "$@" ; }
function group_no_medium { group_no_generic medium 7 "$@" ; }
function group_no_light  { group_no_generic light  6 "$@" ; }

function group_generic { # full|medium|light colstep # caption algos-range divx divy #
  cat <<EOT
\begin{figure}[hbt]
  \begin{subfigure}{0.5\textwidth}
    \centering
EOT
  cut -d, -f $4 "nodes-average-$1.csv" | mkdots $5 $6
  cat <<EOT
    \caption{Average nodes compression}
  \end{subfigure}
  \begin{subfigure}{0.5\textwidth}
    \centering
EOT
  cut -d, -f $4 "nodes-total-$1.csv" | mkdots $5 $6
  cat <<EOT
    \caption{Total nodes compression}
  \end{subfigure}
EOT
  echo "  \\caption{$3}"
  echo '\end{figure}'
  group_no_generic "$@"
}
function group_full   { group_generic full   7 "$@" ; }
function group_medium { group_generic medium 7 "$@" ; }
function group_light  { group_generic light  6 "$@" ; }

function solo_common { # full|medium|light full|medium colstep # algoid algoname #
  cat <<EOT
\begin{figure}[hbt]
  \begin{subfigure}{\textwidth}
    \centering
EOT
  let c=($4*$3)+2
  plotgroupby -x 'Proof size' -i '[0,0]' -f '1 - (%_->[1] / %_->[0])' "$1.csv" '%2 < 1000 ? 0 : (log(%2/1000)/log(2) + 1)' "[%_->[0] + %2, %_->[1] + %$c]" '1000 * (2 ** %i)' 0.1
  cat <<EOT
    \caption{Compression ratio w.r.t. proof size}
  \end{subfigure}
  \begin{subfigure}{\textwidth}
    \centering
EOT
  if [[ "$1" == 'light' ]]
  then if (($4 == 1))
    then let k=9
    elif (($4 < 8))
    then let k=($4+1)*7+2
    elif (($4 < 16))
    then let k=($4+7)*7+2
    else let k=170
    fi
  else let k=$c
  fi
  plotgroupby -x 'Amount of irregular nodes (in percents)' -i '[0,0]' -f '1 - (%_->[1] / %_->[0])' "$2.csv" '10 * %6 / %2' "[%_->[0] + %2, %_->[1] + %$k]" '(%i + 1) * 10' 0.1
  cat <<EOT
    \caption{Compression ratio w.r.t. irregular nodes}
  \end{subfigure}
  \begin{subfigure}{\textwidth}
    \centering
EOT
  plotgroupby -x 'Average number of children per node' -i '[0,0]' -f '1 - (%_->[1] / %_->[0])' "$1.csv" 'int(10 - ((20 * %3) / %2))' "[%_->[0] + %2, %_->[1] + %$c]" '1 + (%i + 1) / 10' 0.1
  cat <<EOT
    \caption{Compression ratio w.r.t. DAG degree}
  \end{subfigure}
EOT
}

function solo_generic { # full|medium|light full|medium colstep # algoid algoname #
  solo_common "$@"
  echo "  \\caption{$5}"
  echo '\end{figure}'
}
function solo_full   { solo_generic full   full   7 "$@" ; }
function solo_medium { solo_generic medium medium 7 "$@" ; }
function solo_light  { solo_generic light  medium 6 "$@" ; }

function solo_rep_generic { # full|medium|light full|medium colstep # algoid algoname minrep #
  solo_common "$@"
  cat <<EOT
  \begin{subfigure}{\textwidth}
    \centering
EOT
  let c=($4*$3)+2
  let r=$c-1
  plotgroupby -x 'Number of iterations' -i '[0,0]' -f '1 - (%_->[1] / %_->[0])' "$1.csv" "%$r < $6 ? 0 : (log(%$r/$6)/log(2) + 1)" "[%_->[0] + %2, %_->[1] + %$c]" "$6 * (2 ** %i)" 0.1
  cat <<EOT
    \caption{Compression ratio w.r.t. number of iterations}
  \end{subfigure}
EOT
  echo "  \\caption{$5}"
  echo '\end{figure}'
}
function solo_rep_full   { solo_rep_generic full   full   7 "$@" ; }
function solo_rep_medium { solo_rep_generic medium medium 7 "$@" ; }
function solo_rep_light  { solo_rep_generic light  medium 6 "$@" ; }

function global_table { # full|medium|light step caption algos cols
  cat <<EOT
\begin{table}[hbt]
  \centering
EOT
  mktab -s $2 "$1.csv" "$4" "$5" <"header-$1"
  echo "  \\caption{$3}"
  echo '\end{table}'
}

function section_generic { # kind step caption algos
  cat <<EOT
\begin{table}[hbt]
  \centering
EOT
  tabaverage "$1.csv" $2 $4 <"header-$1"
  echo "  \\caption{Averages for $3}"
  cat <<EOT
\end{table}
\begin{table}[hbt]
  \centering
EOT
  tabtotal "$1.csv" $2 $4 <"header-$1"
  echo "  \\caption{Total Compression Ratio for $3}"
  echo '\end{table}'
}
function section_full { section_generic full 7 "$@" ; }
function section_medium { section_generic medium 7 "$@" ; }
function section_light { section_generic light 6 "$@" ; }

# Ouput charts

{
cat header.tex

echo '\section{Benchmarks}'

# Full

cat <<EOT
\begin{figure}[hbt]
  \begin{subfigure}{\textwidth}
    \centering
EOT

plotgroupby -x 'Proof size' full.csv  "%2 < 1000 ? 0 : (log(%2/1000)/log(2) + 1)" '%_+1' "1000 * (2 ** %i)" 50

cat <<EOT
  \caption{Repartition of proofs by size}
  \end{subfigure}
  \begin{subfigure}{\textwidth}
    \centering
EOT

plotgroupby -x 'Amount of Irregular Nodes (in percents)' full.csv '10 * %6 / %2' '%_+1' '(%i + 1) * 10' 50

cat <<EOT
  \caption{Repartition of proofs by number of irregular nodes}
  \end{subfigure}
  \begin{subfigure}{\textwidth}
    \centering
EOT

plotgroupby -x 'Average number of children per node' full.csv 'int(10 - ((20 * %3) / %2))' "%_+1" '1 + (%i + 1) / 10' 50

cat <<EOT
  \caption{Repartition of proofs by DAG degree}
  \end{subfigure}
\caption{Repartition of proofs from the \emph{full} set}
\end{figure}
EOT

# Medium

cat <<EOT
\begin{figure}[hbt]
  \begin{subfigure}{\textwidth}
    \centering
EOT

plotgroupby -x 'Proof size' medium.csv  "%2 < 1000 ? 0 : (log(%2/1000)/log(2) + 1)" '%_+1' "1000 * (2 ** %i)" 50

cat <<EOT
  \caption{Repartition of proofs by size}
  \end{subfigure}
  \begin{subfigure}{\textwidth}
    \centering
EOT

plotgroupby -x 'Amount of Irregular Nodes (in percents)' medium.csv '10 * %6 / %2' '%_+1' '(%i + 1) * 10' 50

cat <<EOT
  \caption{Repartition of proofs by number of irregular nodes}
  \end{subfigure}
  \begin{subfigure}{\textwidth}
    \centering
EOT

plotgroupby -x 'Average number of children per node' medium.csv 'int(10 - ((20 * %3) / %2))' "%_+1" '1 + (%i + 1) / 10' 50

cat <<EOT
  \caption{Repartition of proofs by DAG degree}
  \end{subfigure}
\caption{Repartition of proofs from the \emph{medium} set}
\end{figure}
EOT

# Light

cat <<EOT
\begin{figure}[hbt]
  \begin{subfigure}{\textwidth}
    \centering
EOT

plotgroupby -x 'Proof size' light.csv  "%2 < 1000 ? 0 : (log(%2/1000)/log(2) + 1)" '%_+1' "1000 * (2 ** %i)" 50

cat <<EOT
  \caption{Repartition of proofs by size}
  \end{subfigure}
  \begin{subfigure}{\textwidth}
    \centering
EOT

plotgroupby -x 'Average number of children per node' light.csv 'int(10 - ((20 * %3) / %2))' "%_+1" '1 + (%i + 1) / 10' 50

cat <<EOT
  \caption{Repartition of proofs by DAG degree}
  \end{subfigure}
\caption{Repartition of proofs from the \emph{light} set}
\end{figure}
EOT

echo '\section{Reimplementing algorithms}'

section_medium 'Reimplemented Algorithms' 1-4

solo_light 1 LU
solo_light 2 RPI
two_light 1 LU 2 RPI 10
two_medium 2 RP 3 RPI 3
two_light 2 RPI 3 'RPI-R' 15
group_medium "Comparison of LU, RP and RPI" 1-3 0.5 0.05

echo '\section{Combining RPI and LU}'

section_medium 'Combined Algorithms' 5-15

solo_light 4 LURPI
solo_light 6 RPILU
two_light 4 LURPI 6 RPILU 15
solo_light 5 'LURPI-R' 2
solo_light 7 'RPILU-R' 2
two_light 5 'LURPI-R' 7 'RPILU-R' 20

two_medium 5 LURPI  9 'IU-Reg' 10
two_medium 7 RPILU 10 'IU-Low' 10
group_medium "Irregular Units Algorithms Comparison" 5,7,9,10 1 0.1

two_medium 5 LURPI 11 'RI-Reg'   10
two_medium 7 RPILU 12 'RI-Low'   10
two_medium 5 LURPI 13 'RI-alReg' 60
two_medium 7 RPILU 14 'RI-Quad'  60
group_medium "Regularization Informations Algorithms Comparison" 5,7,11-14 2 0.05

two_light 6 RPILU 8 '3pass-LU' 10

echo '\section{Lowering Univalents}'

section_light 'Lowering Univalents Algorithms' 9-13

solo_light 9 LUniv
two_light 1 LU 9 LUniv 10

solo_light 10 LUnivRPI
two_light 4 LURPI 10 LUnivRPI 10
solo_light 12 RPILUniv
two_light 6 RPILU 12 RPILUniv 10

solo_light 11 'LUnivRPI-R' 2
two_light 10 LUnivRPI 11 'LUnivRPI-R' 15
solo_light 13 'RPILUniv-R' 2
two_light 12 RPILUniv 13 'RPILUniv-R' 15

two_light 10 LUnivRPI 12 RPILUniv 10
two_light 11 'LUnivRPI-R' 13 'RPILUniv-R' 20
two_light 10 LUnivRPI 8 '3pass-LU' 10

group_light "Comparing LUniv with others" 1,2,4,6,9,10,12 1 0.05
group_light "Comparing combined algorithms" 4,6,8,10,12 1 0.05
group_light "Comparing combined repeating algorithms" 5,7,11,13 2 0.05

echo '\section{Repeatable Algorithms}'

section_full 'Repeatable Algorithms' 21-27

solo_rep_light 14 'ReduceAndReconstruct' 4
solo_rep_light 15 'Split' 4

two_rep_light 15 'Split' 14 'ReduceAndReconstruct' 250

two_rep_full 24 'TSPlit-Random' 23 'TSplit-Deterministic' 25
two_rep_medium 22 'Split' 23 'MSplit2' 250

group_no_full 'Comparison of Split algorithms' 22-27 15 0.02
group_no_medium 'Comparison of some repeatable algorithms' 21-23 10 0.01

echo '\section{Global overview}'

section_full 'all Algorithms' 1-28

global_table full 7 "Overview of nodes compression ratio" 1-28 '2:Nodes Compression'
global_table full 7 "Overview of unSAT core compression" 1-28 '3:Axioms Compression,4:Variables Compression'

global_table light 6 "Overview of nodes compression ratio" 1-16 '2:Nodes Compression'
global_table light 6 "Overview of unSAT core compression" 1-16 '3:Axioms Compression,4:Variables Compression'

cat footer.tex
} >experiments.tex

# Create and view PDF

lualatex experiments.tex && mupdf experiments.pdf
