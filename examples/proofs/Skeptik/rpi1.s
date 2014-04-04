n0 = {p, x ⊢ }
n1 = {q ⊢ p}
n2 = { ⊢ p}
n3 = { ⊢ q}
np = (n1.n0)
m0 = {p ⊢ x}
m1 = { ⊢ x, q}
qed = ((m1.(n3.np)).(n2.(m0.np)))
