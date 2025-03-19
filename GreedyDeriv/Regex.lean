import GreedyDeriv.Locations
import Mathlib.Tactic.ApplyAt

inductive Regex (α :  Type u) : Type u where
  | emptyset : Regex α
  | epsilon : Regex α
  | char : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Bool → Regex α
  deriving Repr

namespace Regex

variable {α : Type u}

@[simp]
def size : Regex α → Nat
  | emptyset => 1
  | epsilon => 1
  | char _ => 1
  | plus r₁ r₂ => 1 + r₁.size + r₂.size
  | mul r₁ r₂ => 1 + r₁.size + r₂.size
  | star r _ => 1 + r.size

@[simp]
def left : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => epsilon
  | char c => char c
  | plus r₁ r₂ => plus r₁ r₂
  | mul r₁ _ => r₁
  | star r lazy? => star r lazy?

def reverse : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => epsilon
  | char c => char c
  | plus r₁ r₂ => plus r₁.reverse r₂.reverse
  | mul r₁ r₂ => mul r₂.reverse r₁.reverse
  | star r lazy? => star r.reverse lazy?

/-! ### Derivatives -/

@[simp]
def nullable : Regex α → Bool
  | emptyset => false
  | epsilon => true
  | char _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ _ => true

/-- Definition 10 -/
 @[simp]
def prune : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => epsilon
  | char c => char c
  | plus r₁ r₂ =>
    if r₁.nullable
      then r₁.prune
      else plus r₁.prune r₂.prune
  | mul emptyset _ => emptyset
  | mul epsilon r₂ => r₂.prune
  | mul (char c) r₂ => mul (char c) r₂.prune
  | mul (plus r₁₁ r₁₂) r₂ =>
    if (r₁₁.mul r₂).nullable
      then (r₁₁.mul r₂).prune
      else plus (r₁₁.mul r₂).prune (r₁₂.mul r₂).prune
  | mul (mul r₁₁ r₁₂) r₂ => (mul r₁₁ (r₁₂.mul r₂)).prune
  | mul (star r false) r₂ => mul (r.star false) r₂.prune
  | mul (star r true) r₂ =>
    if r₂.nullable
      then r₂.prune
      else mul (r.star true) r₂.prune
  | star r false => r.star false
  | star _ true => epsilon
termination_by r => (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

variable [DecidableEq α]

@[simp]
def deriv : Regex α → α → Regex α
  | emptyset, _ => emptyset
  | epsilon, _ => emptyset
  | char c, d => if c = d then epsilon else emptyset
  | plus r₁ r₂, c => (r₁.deriv c).plus (r₂.deriv c)
  | mul emptyset _, _ => emptyset
  | mul epsilon r₂, c => r₂.deriv c
  | mul (char c) r₂, d => if c = d then r₂ else emptyset
  | mul (plus r₁₁ r₁₂) r₂, c => plus ((r₁₁.mul r₂).deriv c) ((r₁₂.mul r₂).deriv c)
  | mul (mul r₁₁ r₁₂) r₂, c => (r₁₁.mul (r₁₂.mul r₂)).deriv c
  | mul (star r false) r₂, c => plus ((r.deriv c).mul ((r.star false).mul r₂)) (r₂.deriv c)
  | mul (star r true) r₂, c => plus (r₂.deriv c) ((r.deriv c).mul ((r.star true).mul r₂))
  | star r false, c => (r.deriv c).mul (r.star false)
  | star r true, c => (r.deriv c).mul (r.star true)
  termination_by r => (r.size, r.left.size)
  decreasing_by all_goals (simp only [left, size]; omega)

/-! ### Partial Matching -/

inductive PartialMatch : Regex α → Loc α → Loc α → Prop
  | epsilon {l : Loc α} :
    PartialMatch epsilon l l
  | pred {c : α} {d : α} {u v : List α} :
    c = d →
    PartialMatch (char c) ⟨u, d::v⟩ ⟨d::u, v⟩
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

notation:100 "(" r ", " l ")" " → " l':40 => PartialMatch r l l'

/-- Definition 11 -/
def matchEnd : Regex α → Loc α → Option (Loc α)
  | r, (u, []) =>
    if r.nullable
      then some (u, [])
      else none
  | r, (u, c :: v) =>
    match matchEnd (r.prune.deriv c) (c :: u, v) with
    | none => if r.nullable then some (u, c::v) else none
    | some loc => some loc
termination_by _ loc => loc.right.length
