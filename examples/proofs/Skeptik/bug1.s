e0 = { ⊢ a, d}
e1 = (e0.{d, e ⊢ c})
mi = ((e1.{d ⊢ e}).{ ⊢ d, c})
un = (({c, b ⊢ }.mi).(mi.{c ⊢ b}))
qed= ((un.{a ⊢ f}).{f ⊢ })
