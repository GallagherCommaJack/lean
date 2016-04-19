import data.reflection

open lean lean.syntax lean.syntax.expr lean.syntax.level list sum string bool
eval quote (λ x, x)
eval quote (λ A (x : A), x)
eval quote (λ x, nat.succ x)
eval quote ((λ x, x) nat.zero)
