u0 = { ⊢ a}
n0 = (({a ⊢ b}.u0).(u0.{b, a ⊢ c}))
u1 = {a ⊢ }
n1 = (({c ⊢ d, a}.u1).(u1.{d ⊢ a}))
qed= (n0.n1)
