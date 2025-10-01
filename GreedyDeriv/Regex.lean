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

inductive Matches : Regex α → List α → Prop
  | epsilon : Matches epsilon []
  | char {c : α} : Matches (char c) [c]
  | left {s : List α} {r₁ r₂ : Regex α} :
    Matches r₁ s →
    Matches (r₁.plus r₂) s
  | right {s : List α} {r₁ r₂ : Regex α} :
    Matches r₂ s →
    Matches (r₁.plus r₂) s
  | mul {s₁ s₂ s : List α} {r₁ r₂ : Regex α} :
    s₁ ++ s₂ = s →
    Matches r₁ s₁ →
    Matches r₂ s₂ →
    Matches (r₁.mul r₂) s
  | star_nil {r : Regex α} {lazy? : Bool} :
    Matches (r.star lazy?) []
  | stars {s₁ s₂ s : List α} {r : Regex α} {lazy? : Bool} :
    s₁ ++ s₂ = s →
    Matches r s₁ →
    Matches (r.star lazy?) s₂ →
    Matches (r.star lazy?) s

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

theorem PartialMatch.word_eq {r : Regex α} {l l' : Loc α} (h : (r, l) → l') :
  l.word = l'.word := by
  induction h with
  | epsilon => rfl
  | char => simp
  | plus_left h ih =>
    exact ih
  | plus_right h ih =>
    exact ih
  | mul h₁ h₂ ih₁ ih₂ =>
    exact Eq.trans ih₁ ih₂
  | star_nil => rfl
  | stars h₁ h₂ ih₁ ih₂ =>
    exact Eq.trans ih₁ ih₂

theorem PartialMatch.pos_le {r : Regex α} {l l' : Loc α} (h : (r, l) → l') :
  l.pos ≤ l'.pos := by
  induction h with
  | epsilon =>
    exact Nat.le_refl _
  | char => simp
  | plus_left h ih =>
    exact ih
  | plus_right h ih =>
    exact ih
  | mul h₁ h₂ ih₁ ih₂ =>
    exact Nat.le_trans ih₁ ih₂
  | star_nil =>
    exact Nat.le_refl _
  | stars h₁ h₂ ih₁ ih₂ =>
    exact Nat.le_trans ih₁ ih₂

theorem Matches.partial_match {r : Regex α} {s u v : List α} (h : Matches r s) :
  (r, (u, s ++ v)) → (s.reverse ++ u, v) := by
  induction h generalizing u v with
  | epsilon =>
    exact PartialMatch.epsilon
  | char =>
    exact PartialMatch.char
  | left h ih =>
    exact PartialMatch.plus_left ih
  | right h ih =>
    exact PartialMatch.plus_right ih
  | mul hs h₁ h₂ ih₁ ih₂ =>
    simp [←hs]
    exact PartialMatch.mul ih₁ ih₂
  | star_nil =>
    exact PartialMatch.star_nil
  | stars hs h₁ h₂ ih₁ ih₂ =>
    simp [←hs]
    exact PartialMatch.stars ih₁ ih₂

theorem PartialMatch.matches {r : Regex α} {l l' : Loc α} (h : (r, l) → l') :
  Matches r (Loc.match l l') := by
  induction h with
  | epsilon =>
    simp [Loc.match]
    exact Matches.epsilon
  | char =>
    simp [Loc.match]
    rw [Nat.succ_sub (by simp), Nat.sub_self]
    exact Matches.char
  | plus_left h ih =>
    exact Matches.left ih
  | plus_right h ih =>
    exact Matches.right ih
  | mul h₁ h₂ ih₁ ih₂ =>
    refine Matches.mul ?_ ih₁ ih₂
    exact Loc.match_append (word_eq h₁) (pos_le h₁) (pos_le h₂)
  | star_nil =>
    simp [Loc.match]
    exact Matches.star_nil
  | stars h₁ h₂ ih₁ ih₂ =>
    refine Matches.stars ?_ ih₁ ih₂
    exact Loc.match_append (word_eq h₁) (pos_le h₁) (pos_le h₂)

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
    if r₂.nullable
      then mul r₁.prune r₂.prune
      else mul r₁ r₂.prune
  | star r false => r.star false
  | star _ true => epsilon

theorem prune_mul_nullable {r₁ r₂ : Regex α} (hn₂ : r₂.nullable) :
  (r₁.mul r₂).prune = r₁.prune.mul r₂.prune := by
  simp [prune, hn₂]

theorem prune_mul_not_nullable {r₁ r₂ : Regex α} (hn₂ : ¬r₂.nullable) :
  (r₁.mul r₂).prune = r₁.mul r₂.prune := by
  simp [prune, hn₂]

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
