import data.list data.hlist data.tuple data.num data.string data.nat data.option data.sum
import logic
open sum sigma prod function list subtype
open num string nat
open eq

definition nary (n : ℕ) (A B : Type) := nat.rec_on n B (λ n' B', A → B')

namespace lean
  abbreviation name := list (string + num)
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

    namespace expr
      definition arity : expr → ℕ
      | (pi _ A B) := 1 + arity B
      | _ := 0

      definition arglength (α : name → ℕ) : expr → ℕ
      | (var i) := 0
      | (const nm _) := α nm
      | (loc nm t) := arity t
      | (meta nm t) := arity t
      | (app f x) := arglength f - 1
      | (lam _ _ b) := arglength b + 1
      | _ := 0

      namespace autoquote
        -- an attempt at formalizing autoquoters as seen in Agda reflection
        inductive qexp : ℕ → Type₁ := -- simple exprs tagged with arity
        | fvr : ∀ a, name → qexp a -- free var w/o type, `con`
        | tvr : ∀ t, name → qexp (arity t) -- free var w/type, `loc` and `meta`
        | app : ∀{n}, qexp (n + 1) → qexp 0 → qexp n -- should use vecs like in Agda, but Lean is bad at inductives
        | def : ∀{n}, qexp n -- default value
  
        private definition tag (α : name → ℕ) : ∀ e, qexp (arglength α e)
        | (const nm l) := qexp.fvr (α nm) nm
        | (loc nm t) := qexp.tvr t nm
        | (meta nm t) := qexp.tvr t nm
        | (app f x) := if arglength α f = 0 then qexp.def -- this whole thing needs to be cleaned
                       else if arglength α x = 0
                            then qexp.app (cast sorry (tag f)) (cast sorry (tag x)) -- thanks to UIP, this computes
                            else qexp.def
        | e := qexp.def

        structure table (A : Type) :=
          mk :: (vars : list (name × syntax.expr))
                (nmap : hlist (λ nme, nary (arity (pr₂ nme)) A A) vars)
                (fvars : list (name × ℕ))
                (fvmap : hlist (λ nme, nary (pr₂ nme) A A) fvars)

        private definition convert (A : Type) (θ : table A) {n : ℕ} (e : qexp n) : option (nary n A A) :=
          qexp.rec_on e
            (λ a nm, sum.rec_on (decide ((nm,a) ∈ table.fvars θ))
                                (λ v, option.some (hlist.get (table.fvmap θ) v))
                                (λ nv, option.none))
            (λ t nm, sum.rec_on (decide ((nm,t) ∈ table.vars θ))
                                (λ v, option.some (hlist.get (table.nmap θ) v))
                                (λ nv, option.none))
          (λ n f x f' x', by eapply option.monad.ap; apply f'; apply x') -- why this works and not the other I don't know
          (λ n, option.none)

        private definition lookup {A B : Type} [H : decidable_eq A] (a : A) : list (A × B) → option B
        | [] := option.none
        | ((k,v) :: xs) := if a = k then option.some v else lookup xs

        private abbreviation tagFromTable {A : Type} (θ : table A) (nm : name) : ℕ :=
          option.rec_on (lookup nm (table.fvars θ)) 0 id

        abbreviation convertManages {A : Type} (θ : table A) (e : expr) : Prop :=
          match convert A θ (tag (tagFromTable θ) e) with (option.some t) := true | option.none := false end

        definition doConvert {A : Type} (θ : table A) (e : expr) :
          ∀ {thm : convertManages θ e}, nary (arglength (tagFromTable θ) e) A A :=
          option.rec_on (convert A θ (tag (tagFromTable θ) e)) (false.rec _) (λ t thm, t)
      end autoquote
    end expr

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


