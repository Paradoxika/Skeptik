all-final.csv is a valid Comma-Separated values (CSV) file. Each line
corresponds to a proof on which experiments have been performed. The first
column gives the name of the proof. For the remaining columns, compute the
quotient q and remainder r of the euclidean division of the column identifier by
5 and search in the following tables.  The column next to the proof's name has
identifier 0.

Table for the quotient q correspond to the algorithms
q=0  The original proof (no algorithm, the identity)
q=1  LU
q=2  LUniv
q=3  RPILU
q=4  RPILUniv
q=5  LU.RPI
q=6  LUnivRPI
q=7  RPI
q=8  Split
q=9  RedRec
q=10 Best LU/RPI
q=11 Best LU/LUniv/RPI

Table for the remainder r corresponds to the measures
r=0 Time needed to produce the proof (parsing time or compression time)
r=1 Size of the proof (number of nodes)
r=2 Number of axioms
r=3 Size of axioms (sum of the number of literals in all axioms)
r=4 Size of nodes (sum of the number of literals in all nodes)
