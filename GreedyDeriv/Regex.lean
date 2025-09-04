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

@[simp]
def denullify : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => emptyset
  | char c => char c
  | plus r₁ r₂ => plus r₁.denullify r₂.denullify
  | mul r₁ r₂ =>
    if r₁.nullable ∧ r₂.nullable
      then (r₁.denullify.mul r₂).plus r₂.denullify
      else r₁.mul r₂
  | star r lazy? => mul r.denullify (star r lazy?)

theorem denullify_not_nullable (r : Regex α) (hn : ¬r.nullable) :
  r.denullify = r := by
  induction r with
  | emptyset => rfl
  | epsilon => simp at hn
  | char c => rfl
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp
    rw [ih₁ (by simp [hn.left]), ih₂ (by simp [hn.right])]
    exact ⟨rfl, rfl⟩
  | mul r₁ r₂ ih₁ ih₂ => simp_all
  | star r lazy? => simp at hn

/-- Definition 13 -/
 @[simp]
def prune : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => epsilon
  | char c => char c
  | plus r₁ r₂ =>
    if r₁.nullable
      then r₁.prune
      else plus r₁.prune r₂.prune
  | mul r₁ r₂ =>
    if r₁.nullable ∧ r₂.nullable
      then plus (r₁.prune.denullify.mul r₂) r₂.prune
      else mul r₁ r₂
  | star r false => r.star false
  | star _ true => epsilon

theorem prune_not_nullable (r : Regex α) (hn : ¬r.nullable) :
  r.prune = r := by
  induction r with
  | emptyset => rfl
  | epsilon => simp at hn
  | char c => rfl
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [hn]
    rw [ih₁ (by simp [hn.left]), ih₂ (by simp [hn.right])]
    exact ⟨rfl, rfl⟩
  | mul r₁ r₂ ih₁ ih₂ => simp_all
  | star r lazy? => simp at hn

theorem prune_mul_nullable {r₁ r₂ : Regex α} (hn₂ : r₂.nullable) :
  (r₁.mul r₂).prune = r₁.prune.mul r₂.prune := by
  sorry
  -- simp [prune, hn₂]

theorem prune_mul_not_nullable {r₁ r₂ : Regex α} (hn₂ : ¬r₂.nullable) :
  (r₁.mul r₂).prune = r₁.mul r₂.prune := by
  sorry
  -- simp [prune, hn₂]

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

notation:100 "(" r ", " l ")" " → " l':40 => PartialMatch r l l'

/-- Definition 14 -/
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
