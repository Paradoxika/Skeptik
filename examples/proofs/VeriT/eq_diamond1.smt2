(set .c1 (input :conclusion ((not #1:(= x0 x0)))))
(set .c2 (eq_reflexive :conclusion (#1)))
(set .c3 (resolution :clauses (.c2 .c1) :conclusion ()))
