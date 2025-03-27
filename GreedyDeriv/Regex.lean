import GreedyDeriv.Locations
import Mathlib.Tactic.ApplyAt

inductive Regex (α :  Type u) : Type u where
  | emptyset : Regex α
  | epsilon : Regex α
  | char : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  deriving Repr

namespace Regex

variable {α : Type u}

def repr [Repr α] : Regex α → Std.Format
  | emptyset => "∅"
  | epsilon => "ε"
  | char c => reprPrec c 0
  | plus r₁ r₂ => r₁.repr ++ " + " ++ r₂.repr
  | mul r₁ r₂ => "(" ++ r₁.repr ++ " · " ++ r₂.repr ++ ")"
  | star r => "(" ++ r.repr ++ ")*"

instance [Repr α] : Repr (Regex α) where
  reprPrec r _ := r.repr

@[simp]
def size : Regex α → Nat
  | emptyset => 1
  | epsilon => 1
  | char _ => 1
  | plus r₁ r₂ => 1 + r₁.size + r₂.size
  | mul r₁ r₂ => 1 + r₁.size + r₂.size
  | star r => 1 + r.size

@[simp]
def left : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => epsilon
  | char c => char c
  | plus r₁ r₂ => plus r₁ r₂
  | mul r₁ _ => r₁
  | star r => star r

def reverse : Regex α → Regex α
  | emptyset => emptyset
  | epsilon => epsilon
  | char c => char c
  | plus r₁ r₂ => plus r₁.reverse r₂.reverse
  | mul r₁ r₂ => mul r₂.reverse r₁.reverse
  | star r => star r.reverse

/-! ### Derivatives -/

@[simp]
def nullable : Regex α → Bool
  | emptyset => false
  | epsilon => true
  | char _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ => true

@[simp]
def highNullable : Regex α → Bool
  | emptyset => false
  | epsilon => true
  | char _ => false
  | plus r₁ _ => r₁.highNullable
  | mul r₁ r₂ => r₁.highNullable && r₂.highNullable
  | star r => r.highNullable

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
  | mul (star r) r₂, c => plus ((r.deriv c).mul (r.star.mul r₂)) (r₂.deriv c)
  | star r , c => (r.deriv c).mul r.star
  termination_by r => (r.size, r.left.size)
  decreasing_by all_goals (simp only [left, size]; omega)

@[simp]
def existsMatch : Regex α → Loc α → Bool
  | r, ⟨_, []⟩ => r.nullable
  | r, ⟨u, c::v⟩ => r.nullable || (r.deriv c).existsMatch ⟨c::u, v⟩
termination_by _ l => l.right.length

def existsMatchNonNullable : Regex α → Loc α → Bool
  | _, ⟨_, []⟩ => false
  | r, ⟨u, c::v⟩ => (r.deriv c).existsMatch (c::u, v)

inductive SubBranch : Regex α → Regex α → Prop
  | same {r : Regex α} :
    SubBranch r r
  | left (r₁ r₂ : Regex α) :
    SubBranch r₁ (plus r₁ r₂)
  | right {r₁ r₂ : Regex α} :
    SubBranch r₂ (plus r₁ r₂)

def dist_star_alts : Regex α → Regex α → Regex α → Regex α
  | emptyset, _, r₂ => r₂
  | epsilon, _, r₂ => r₂
  | char c, r_star, r₂ => mul (char c) (mul r_star r₂)
  | plus r₁₁ r₁₂, r_star, r₂ =>
    if (dist_star_alts r₁₁ r_star r₂).nullable
      then dist_star_alts r₁₁ r_star r₂
      else plus (dist_star_alts r₁₁ r_star r₂) (dist_star_alts r₁₂ r_star r₂)
  | mul r₁₁ r₁₂, r_star, r₂ => mul (mul r₁₁ r₁₂) (mul r_star r₂)
  | star r, r_star, r₂ => plus (dist_star_alts r r_star r₂) r₂

/-- Definition 10 -/
 @[simp]
def prune : Regex α →  Regex α
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
  | mul (plus r₁₁ r₁₂) r₂=>
    if (r₁₁.mul r₂).nullable
      then (r₁₁.mul r₂).prune
      else plus (r₁₁.mul r₂).prune (r₁₂.mul r₂).prune
  | mul (mul r₁₁ r₁₂) r₂=> (mul r₁₁ (r₁₂.mul r₂)).prune
  | mul (star r) r₂ =>
    plus (dist_star_alts r (star r) r₂.prune) r₂.prune
  | star r => r.prune.star
termination_by r => (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem prune_star_def {α : Type u} {r : Regex α} :
  r.star.prune = r.prune.star := by
  rw [prune]

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
  | star_nil {r : Regex α} {l : Loc α} :
    PartialMatch (star r) l l
  | stars {r : Regex α} {l k l' : Loc α} :
    PartialMatch r l k →
    PartialMatch (star r) k l' →
    PartialMatch (star r) l l'

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
