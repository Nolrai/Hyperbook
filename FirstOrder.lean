import MathLib
import Lean.Meta.WHNF

inductive Term (α : ℕ → Type) (v : ℕ) : ℕ → Type where
  | Var : Fin v → Term α v 0
  | Const : α n → Term α v n
  | App : Term α v (n + 1) → Term α v 0 → Term α v n 

structure Vector (n : ℕ) (α : Type) : Type where
  data : List α
  sized : data.length = n

def Vector.get : Vector n α → Fin n → α 
  | {data := l, sized := p} =>
    match p with
    | rfl => l.get

def Vector.cons : α → Vector n α → Vector (n+1) α
  | x, xs => ⟨x :: xs.data, by simp [List.length, xs.sized] ⟩

infix:50 "∷" => Vector.cons 

def Vector.map : (α → β) → Vector n α → Vector n β 
  | f, v => ⟨v.data.map f, Eq.trans (List.length_map _ _) v.sized⟩

inductive Formula {α rel op : ℕ → Type} {quant : Type} : ℕ → ℕ → Type where
  | Rel : rel n → Vector n (Term α v 0) → Formula v 0 
  | Op : op n → Formula v n
  | App : Formula v (n + 1) → Formula v 0 → Formula v n
  | Quant : quant → Formula (v + 1) 0 → Formula v 0

instance : EmptyCollection (Vector 0 α) where
  emptyCollection := ⟨[], List.length_nil⟩

def Term.semantics 
  (on_α : ∀ {n}, α n → Vector n β → β) :
  Term α v m → (Vector v β) → (Vector m β) → β 
  | t, varArgs, termArgs =>
    match t with
    | Var fin => varArgs.get fin
    | Const a => on_α a termArgs
    | App func arg => 
      have func' := func.semantics on_α varArgs 
      have arg' := arg.semantics on_α varArgs ∅ 
      func' (arg' ∷ termArgs)

section

variable 
  {α rel op : ℕ → Type} {quant : Type}
  (on_α : ∀ {n}, α n → Vector n β → β) 
  (on_rel : ∀ {n}, rel n → Vector n β → γ)
  (on_op : ∀ {n}, op n → Vector n γ → γ)
  (on_quant : quant → ∀ {n}, (Vector (n + 1) β → γ) → Vector n β → γ)

def Formula.semantics :
  @Formula α rel op quant v m -> Vector v β → Vector m γ → γ
  | formula, varArgs, formulaArgs =>
    match formula with
    | App func arg => 
      have func' := func.semantics varArgs 
      have arg' := arg.semantics varArgs ∅ 
      func' (arg' ∷ formulaArgs)
    | Rel r args => on_rel r (args.map (λ (t : Term α v 0) => t.semantics on_α varArgs ∅))
    | Op x => on_op x formulaArgs
    | Quant q body => on_quant q (λ varArgs' => body.semantics varArgs' formulaArgs) varArgs

end

section FO

inductive Op : ℕ → Type where
  | True : Op 0
  | False : Op 0
  | Not : Op 1
  | And : Op 2
  | Or : Op 2

inductive Quant : Type where
  | Uni : Quant
  | Exi : Quant

def FOFormula α rel := @Formula α rel Op Quant

def on_op : ∀ {n}, Op n → Vector n Prop → Prop
  | 0, Op.True, ⟨[], _⟩ => true 
  | 0, Op.False, ⟨[], _⟩ => false
  | 1, Op.Not, ⟨[x], _⟩ => ¬ x
  | 2, Op.And, ⟨[x, y], _⟩ => x ∧ y
  | 2, Op.Or, ⟨[x, y], _⟩ => x ∨ y

def on_quant : Quant → ∀ {n}, (Vector (n + 1) β → Prop) → Vector n β → Prop
  | Quant.Uni, _, f, ys => ∀ b : β, f (b ∷ ys) 
  | Quant.Exi, _, f, ys => ∃ b : β, f (b ∷ ys) 

abbrev TT : FOFormula α rel n 0 := Formula.Op Op.True
abbrev FF : FOFormula α rel n 0 := Formula.Op Op.True
abbrev UU : FOFormula α rel (n + 1) m → FOFormula α rel n m :=
  λ f =>
    have f' : Formula n (m + 1) := _
    Formula.Quant Quant.Uni f' 

def FO.app1 (x : Op 1) (f : FOFormula α rel n 0) : FOFormula α rel n 0 :=
  Formula.App (Formula.Op x) f

def FO.app2 (x : Op 2) (l r : FOFormula α rel n 0) : FOFormula α rel n 0 :=
  Formula.App (Formula.App (Formula.Op x) l) r

def FO.rel_app2 (x : rel 2) (l r : Term func n 0) : FOFormula func rel n 0 :=
  Formula.Rel x ⟨[l, r], rfl⟩

prefix:50 "¬' " => FO.app1 Op.Not
infix:50 "∧'" => FO.app2 Op.And
infix:50 "∨'" => FO.app2 Op.And

variable 
  {β : Type}
  {func rel : ℕ → Type}
  (on_func : ∀ {n}, func n → Vector n β → β) 
  (on_rel : ∀ {n}, rel n → Vector n β → Prop)

def FOFormula.toProp : FOFormula func rel 0 0 → Prop :=
  λ f => Formula.semantics (β := β) (γ := Prop) (α := func) (rel := rel) on_func on_rel on_op on_quant f ∅ ∅

end FO

class FirstOrder (Class : Type → Type) : Type 2 where
  fun_symbols : ℕ → Type
  rel_symbols : ℕ → Type
  formula : FOFormula fun_symbols rel_symbols 0 0
  existsImp : 
    ∀ α : Type, 
      (∃ _ : Class α, True) ↔ 
      ∃ (on_β : ∀ {n}, fun_symbols n → Vector n α → α) 
        (on_γ : ∀ {n}, rel_symbols n → Vector n α → Prop) , 
          formula.toProp on_β on_γ

inductive OrderSymbols : ℕ → Type where
  | LE : OrderSymbols 2

def LE_REFL : FOFormula func OrderSymbols 0 0 :=

instance : FirstOrder Preorder where
  fun_symbols := λ _ => Empty
  rel_symbols := OrderSymbols
  formula := 