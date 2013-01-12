#! /bin/bash

FILE=all-final.csv

PATH=../../../scripts/:$PATH
export PERL5LIB=../../../scripts

function make_charts { # caption algo_h algo_v col_base_h col_base_v
  cat <<EOT
\begin{figure}[tbh]
  \centering
  \subfloat[Nodes compression]{
    \centering
EOT
  let h=$4+1
  let v=$5+1
  mkcloudid -h "$h:$2" -v "$v:$3" -r 2 -d 0.2 "${FILE}"
  cat <<EOT
  } \qquad
  \subfloat[Unsat core compression]{
    \centering
EOT
  let h=$h+1
  let v=$v+1
  mkcloudid -h "$h:$2" -v "$v:$3" -r 3 -d 0.2 "${FILE}"
  cat <<EOT
  } \\
  \subfloat[Nodes compression difference]{
    \centering
EOT
  let h=$4+1
  let v=$5+1
  mkbarcomparison -f $h -s $v -p 0.01 "${FILE}"
  cat <<EOT
  } \\
  \subfloat[Duration difference]{
    \centering
EOT
  mkbarcomparison -f $4 -s $5 -p 0.1 "${FILE}"
  cat <<EOT
  }
EOT
  echo "  \\caption{$1}"
  echo '\end{figure}'
}

make_charts "Comparison between LU and LUniv" LU LUniv 6 11 >LU_charts.tex
make_charts "Comparison between LU.RPI and LUnivRPI" LU.RPI LUnivRPI 26 31 >LURPI_charts.tex
make_charts "Comparison between the LU and LUniv combinations" RPI/LU RPI/LUniv 51 56 >best_charts.tex
