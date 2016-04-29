import data.list data.hlist data.tuple data.num data.string data.nat data.option data.sum
import logic
open sum sigma prod function list subtype
open num string nat
open eq

definition nary (n : ℕ) (A B : Type) := nat.rec_on n B (λ n' B', A → B')

namespace lean
  abbreviation name := list (string + num)
  definition name.dec_eq : ∀ (i j : name), decidable (i = j) := _
  attribute [instance] name.dec_eq
  --axiom [H : decidable_eq name]
  --attribute [instance] H
  namespace syntax
    inductive level : Type₁ :=
    | meta   : name → level
    | zero   : level
    | succ   : level → level
    | max    : level → level → level
    | imax   : level → level → level
    | param  : name → level
    | global : name → level

    inductive expr : Type₁ :=
    | var   : ℕ → expr
    | const : name  → list level → expr
    | loc   : name  → expr → expr
    | meta  : name  → expr → expr
    | sort  : level → expr
    | pi    : name  → expr → expr → expr
    | lam   : name  → expr → expr → expr
    | app   : expr  → expr → expr
    | elet  : name  → expr → expr → expr → expr


    definition expr.eq_dec [instance] : ∀ (e1 e2 : expr), decidable (e1 = e2) := sorry
    definition level.eq_dec [instance] : ∀ (l1 l2 : level), decidable (l1 = l2) := sorry

    namespace varops
      open expr
      section
        parameters (bop : ℕ → ℕ → expr)
        private abbreviation bvop : ℕ → expr → expr
        | d (var i) := bop d i
        | d (pi nm A B) := pi nm (bvop d A) (bvop (d + 1) B)
        | d (lam nm A b) := lam nm (bvop d A) (bvop (d + 1) b)
        | d (app f x) := app (bvop d f) (bvop d x)
        | d (elet nm val ty b) := elet nm (bvop d val) (bvop d ty) (bvop (d + 1) b) -- is this correct?
        | d e := e
      end

      private abbreviation wk_var (n d ix : nat) : expr :=
        if d ≤ ix then var (n + ix) else var ix

      definition wk := bvop ∘ wk_var

      private abbreviation instantiate_var (vs : list expr) (d ix : nat) : expr :=
        if ix < d then var ix
        else if ix < (d + length vs)
             then wk ix 0 (ith vs (ix - d) sorry)
             else var (ix - length vs)

      definition instantiate := bvop ∘ instantiate_var 

      private abbreviation fvop : (name → option expr) → expr → expr
      | o (const nm ls) := option.rec (const nm ls) id (o nm)
      | o (loc nm ls) := option.rec (loc nm (fvop o ls)) id (o nm)
      | o (pi nm A B) := let o' := λ nm', if nm = nm' then option.none else o nm'
                         in pi nm (fvop o A) (fvop o' B)
      | o (lam nm A B) := let o' := λ nm', if nm = nm' then option.none else o nm'
                          in lam nm (fvop o A) (fvop o' B)
      | o (elet nm val ty b) := let o' := λ nm', if nm = nm' then option.none else o nm'
                                in elet nm (fvop o val) (fvop o ty) (fvop o b)
      | o (app f x) := app (fvop o f) (fvop o x)
      | o e := e

      definition inst_vars := fvop
    end varops
  end syntax
end lean


