a0 = { ⊢ b, a}
u0 = ({b ⊢ a}.a0)
u1 = ({a ⊢ b}.a0)
n0 = (({a, c, d ⊢ }.u0).(u0.{a ⊢ c}))
n1 = (({b, e ⊢ }.u1).(u1.{b ⊢ e, d}))
qed= (n0.n1)
