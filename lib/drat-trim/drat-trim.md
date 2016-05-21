To convert a DRUP proof to a TraceCheck proof, the following commands should be used:

```
./drat-trim FILE.cnf PROOF.drup -l LEMMAS.drup
./drat-trim FILE.cnf LEMMAS.drup -f -r TRACE
```