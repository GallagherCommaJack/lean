import data.reflection
import data.list
open monoid
open [notation] list
section
  parameters {A : Type} [monoid A]

  inductive monexp : Type :=
  | ident : monexp
  | var : A → monexp
  | op : monexp → monexp → monexp
/-
  definition mdenote : monexp → A :=
   monexp.rec 1 (λ a, a) (λ e1 e2 m1 m2, m1 * m2)
  --| mdenote monexp.ident := 1
  --| mdenote (monexp.op m1 m2) := mdenote m1 * mdenote m2
  --| mdenote (monexp.var m) := m

  definition flatten : monexp → list A :=
    monexp.rec [] (λ a, [a]) (λ m1 m2 ms1 ms2, ms1 ++ ms2)
  --| flatten monexp.ident := []
  --| flatten (monexp.var a) := [a]
  --| flatten (monexp.op m1 m2) := flatten m1 ++ flatten m2

  definition mconcat : list A → A :=
    list.rec 1 (λ x xs, mul x)
  --| mconcat (x :: xs) := x * mconcat xs
  --| mconcat [] := 1

  definition mconcat_nil [defeq] : mconcat [] = 1 := rfl
  definition mconcat_cons [defeq] : ∀ m l, mconcat (m :: l) = m * mconcat l := λ m l, rfl

  definition mdenote_id [defeq] : mdenote monexp.ident = 1 := rfl
  definition mdenote_var [defeq] : ∀ a, mdenote (monexp.var a) = a := λ a, rfl
  definition mdenote_op [defeq] : ∀ e1 e2, mdenote (monexp.op e1 e2) = mdenote e1 * mdenote e2 := λ m1 m2, rfl

  definition flat_id [defeq] : flatten monexp.ident = [] := rfl
  definition flat_var [defeq] : ∀ a, flatten (monexp.var a) = [a] := λ a, rfl
  definition flat_op [defeq] : ∀ m1 m2, flatten (monexp.op m1 m2) = flatten m1 ++ flatten m2 := λ m1 m2, rfl

  definition app_nil [defeq] (A : Type) : ∀ (l : list A), [] ++ l = l := λ l, rfl
  definition app_cons [defeq] (A : Type) : ∀ a (l1 l2 : list A), (a :: l1) ++ l2 = a :: (l1 ++ l2) := λ a l1 l2, rfl
  lemma app_nil_r [simp] (A : Type) (l : list A) : l ++ [] = l := by induction l; all_goals inst_simp

  attribute [forward] mul_assoc
  attribute [simp] one_mul mul_one
  attribute [forward] one_mul mul_one

  lemma flat_concat [simp] (l1 l2 : list A) : mconcat (l1 ++ l2) = mconcat l1 * mconcat l2 := by induction l1; all_goals inst_simp
  theorem monexp_mdenote (m : monexp) : mconcat (flatten m) = mdenote m := by induction m; all_goals inst_simp
-/
end


-- monexp.{l_1} : Π {A : Type.{l_1}} [_inst_1 : monoid.{l_1} A], Type.{max 1 l_1}

constants (A : Type.{1}) (A_monoid : monoid A)
attribute A_monoid [instance]

open lean.syntax lean.syntax.expr

set_option pp.all true
check (one : A)
check (mul.{1} : A → A → A)

-- @one.{1} A (@monoid.to_has_one.{1} A A_monoid) : A
-- @monoid.mul.{1} A A_monoid : A → A → A

definition reify_monoid (A : Type.{1}) [A_monoid : monoid.{1} A] : expr →  @monexp.{1} A A_monoid
| (quote (@one.{1} A A_monoid)) := monexp.ident
| (app (app (quote (@monoid.mul.{1} A A_monoid)) e₁) e₂) := monexp.op (reify_monoid e₁) (reify_monoid e₂)
| a := monexp.ident

print reify_monoid

eval quote reify_monoid
-- print reify_monoid
