import GreedyDeriv.Locations
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Linarith

inductive Regex (α :  Type u) : Type u where
  | emptyset : Regex α
  | epsilon : Regex α
  | char : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Bool → Regex α
  | lookahead : Regex α → Regex α
  deriving Repr

namespace Regex

variable {α : Type}

@[simp]
def size : Regex α → Nat
  | emptyset => 1
  | epsilon => 1
  | char _ => 1
  | plus r₁ r₂ => 1 + r₁.size + r₂.size
  | mul r₁ r₂ => 1 + r₁.size + r₂.size
  | star r _ => 1 + r.size
  | lookahead r => 1 + r.size

@[simp]
def left : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => epsilon
  | char c => char c
  | plus r₁ r₂ => plus r₁ r₂
  | mul r₁ _ => r₁
  | star r lazy? => star r lazy?
  | lookahead r => lookahead r

/-! ### Derivatives -/

variable [DecidableEq α]

@[simp]
def alwaysNullable : Regex α → Bool
  | emptyset => false
  | epsilon => true
  | char _ => false
  | plus r₁ r₂ => r₁.alwaysNullable || r₂.alwaysNullable
  | mul r₁ r₂ => r₁.alwaysNullable && r₂.alwaysNullable
  | star _ _ => true
  | lookahead r => r.alwaysNullable

mutual

@[simp]
def nullable : Regex α → Loc α → Bool
  | emptyset, _ => false
  | epsilon, _ => true
  | char _, _ => false
  | plus r₁ r₂, l => r₁.nullable l || r₂.nullable l
  | mul r₁ r₂, l => r₁.nullable l && r₂.nullable l
  | star _ _, _ => true
  | lookahead r, l => r.existsMatch l
  termination_by r l => (l.right.length, r.size, r.left.size, 0)

@[simp]
def deriv : Regex α → Loc α → Regex α
  | emptyset, _ => emptyset
  | epsilon, _ => emptyset
  | char _, ⟨_, []⟩ => emptyset
  | char c, ⟨_, d::_⟩ => if c = d then epsilon else emptyset
  | plus r₁ r₂, c => (r₁.deriv c).plus (r₂.deriv c)
  | mul emptyset _, _ => emptyset
  | mul epsilon r₂, c => r₂.deriv c
  | mul (char _) _, ⟨_, []⟩ => emptyset
  | mul (char c) r₂, ⟨_, d::_⟩ => if c = d then r₂ else emptyset
  | mul (plus r₁₁ r₁₂) r₂, c => plus ((r₁₁.mul r₂).deriv c) ((r₁₂.mul r₂).deriv c)
  | mul (mul r₁₁ r₁₂) r₂, c => (r₁₁.mul (r₁₂.mul r₂)).deriv c
  | mul (star r false) r₂, c => plus ((r.deriv c).mul ((r.star false).mul r₂)) (r₂.deriv c)
  | mul (star r true) r₂, c => plus (r₂.deriv c) ((r.deriv c).mul ((r.star true).mul r₂))
  | mul (lookahead r) r₂, l => if r.existsMatch l then r₂.deriv l else emptyset
  | star r false, c => (r.deriv c).mul (r.star false)
  | star r true, c => (r.deriv c).mul (r.star true)
  | lookahead _, _ => emptyset
  termination_by r l => (l.right.length, r.size, r.left.size, 0)
  decreasing_by
    any_goals (simp only [size]; decreasing_tactic)
    · simp only [size, left]
      apply Prod.Lex.right
      apply Prod.Lex.right'
      omega
      apply Prod.Lex.left
      decreasing_tactic

def existsMatch : Regex α → Loc α → Bool
  | r, ⟨u, []⟩ => r.nullable ⟨u, []⟩
  | r, ⟨u, c::v⟩ => r.nullable ⟨u, c::v⟩ || (r.deriv ⟨u, c::v⟩).existsMatch ⟨c::u, v⟩
termination_by r l => (l.right.length, r.size, r.left.size, 1)

end

def denullify : Regex α → Loc α → Regex α
  | emptyset, _ => emptyset
  | epsilon, _ => emptyset
  | char c, _ => char c
  | plus r₁ r₂, l => plus (r₁.denullify l) (r₂.denullify l)
  | mul r₁ r₂, l =>
    if r₁.nullable l
      then (r₁.denullify l).mul r₂
      else r₁.mul r₂
  | star r false, l => mul (r.denullify l) (star r false)
  | star _ true, _ => emptyset
  | lookahead _, _ => emptyset

theorem alwaysNullable_nullable {r : Regex α} :
  r.alwaysNullable → ∀ l, r.nullable l := by
  intro h
  induction r with
  | emptyset => nomatch h
  | epsilon => simp
  | char => nomatch h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at h
    cases h with
    | inl h =>
      simp [ih₁ h]
    | inr h =>
      simp [ih₂ h]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at h
    simp [ih₁ h.left, ih₂ h.right]
  | star => simp
  | lookahead r ih =>
    simp at h
    intro l
    simp
    unfold existsMatch
    split <;> simp [ih h]

theorem alwaysNullable_existsMatch (r : Regex α) :
  r.alwaysNullable → ∀ l, r.existsMatch l := by
  intro h l
  unfold existsMatch
  split <;>
  simp [alwaysNullable_nullable h]

theorem existsMatch_emptyset (l : Loc α) :
  emptyset.existsMatch l = false := by
  rcases l with ⟨u, v⟩
  induction v generalizing u with
  | nil => simp [existsMatch]
  | cons x xs ih =>
    simp [existsMatch]
    apply ih

theorem existsMatch_epsilon (l : Loc α) :
  epsilon.existsMatch l = true := by
  unfold existsMatch
  split <;> simp

/-- Definition 13 -/
@[simp]
def prune : Regex α → Loc α → Regex α
  | emptyset, _ => emptyset
  | epsilon, _ => epsilon
  | char c, _  => char c
  | plus r₁ r₂, l =>
    if r₁.nullable l
      then r₁.prune l
      else plus (r₁.prune l) (r₂.prune l)
  | mul r₁ r₂, l =>
    if r₂.nullable l
      then plus (mul ((r₁.prune l).denullify l) r₂) (r₂.prune l)
      else mul r₁ r₂
  | star r false, _ => r.star false
  | star _ true, _ => epsilon
  -- If we are ever in the position to prune a lookahead, then it must have
  -- already been satisfied
  | lookahead _, _ => epsilon

/-! ### Partial Matching -/

/-- Definition 1 -/
inductive PartialMatch : Regex α → Loc α → Loc α → Prop
  | epsilon {l : Loc α} :
    PartialMatch epsilon l l
  | char {c : α} {u v : List α} :
    PartialMatch (char c) ⟨u, c::v⟩ ⟨c::u, v⟩
  | plus_left {r₁ r₂ : Regex α} {l l' : Loc α} :
    PartialMatch r₁ l l' →
    PartialMatch (plus r₁ r₂) l l'
  | plus_right {r₁ r₂ : Regex α} {l l' : Loc α} :
    PartialMatch r₂ l l' →
    PartialMatch (plus r₁ r₂) l l'
  | mul {r₁ r₂ : Regex α} {l k l' : Loc α} :
    PartialMatch r₁ l k →
    PartialMatch r₂ k l' →
    PartialMatch (mul r₁ r₂) l l'
  | star_nil {r : Regex α} {lazy? : Bool} {l : Loc α} :
    PartialMatch (star r lazy?) l l
  | stars {r : Regex α} {lazy? : Bool} {l k l' : Loc α} :
    PartialMatch r l k →
    PartialMatch (star r lazy?) k l' →
    PartialMatch (star r lazy?) l l'
  | lookahead {r : Regex α} {l l' : Loc α} :
    PartialMatch r l l' →
    PartialMatch (lookahead r) l l

notation:100 "(" r ", " l ")" " → " l':40 => PartialMatch r l l'

/-- Definition 14 -/
def matchEnd : Regex α → Loc α → Option (Loc α)
  | r, (u, []) =>
    if r.nullable (u, [])
      then some (u, [])
      else none
  | r, (u, c :: v) =>
    match matchEnd ((r.prune (u, c::v)).deriv (u, c::v)) (c :: u, v) with
    | none => if r.nullable (u, c::v) then some (u, c::v) else none
    | some loc => some loc
termination_by _ loc => loc.right.length
