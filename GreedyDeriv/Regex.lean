import GreedyDeriv.Locations
import GreedyDeriv.EffectiveBooleanAlgebra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ApplyAt

inductive Regex (α :  Type u) : Type u where
  | epsilon : Regex α
  | pred : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  deriving Repr

namespace Regex

variable {α : Type u}

@[simp]
def size : Regex α → Nat
  | epsilon => 1
  | pred _ => 1
  | plus r₁ r₂ => 1 + r₁.size + r₂.size
  | mul r₁ r₂ => 1 + r₁.size + r₂.size
  | star r => 1 + r.size

@[simp]
def left : Regex α → Regex α
  | epsilon => epsilon
  | pred c => pred c
  | plus r₁ r₂ => plus r₁ r₂
  | mul r₁ _ => r₁
  | star r => star r

def reverse : Regex α → Regex α
  | epsilon => epsilon
  | pred c => pred c
  | plus r₁ r₂ => plus r₂.reverse r₁.reverse
  | mul r₁ r₂ => mul r₂.reverse r₁.reverse
  | star r => star r.reverse

/-! ### Derivatives -/

@[simp]
def nullable : Regex α → Bool
  | epsilon => true
  | pred _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ => true

@[simp]
def highNullable : Regex α → Bool
  | epsilon => true
  | pred _ => false
  | plus r₁ _ => r₁.highNullable
  | mul r₁ r₂ => r₁.highNullable && r₂.highNullable
  | star _ => false

theorem highNullable_nullable {r : Regex α} :
  r.highNullable → r.nullable := by
  induction r with
  | epsilon => simp
  | pred => simp
  | plus r₁ r₂ ih₁ _ =>
    simp
    intro h
    apply ih₁ at h
    exact Or.inl h
  | mul r₁ r₂ ih₁ ih₂ =>
    simp
    intro h₁ h₂
    apply ih₁ at h₁
    apply ih₂ at h₂
    exact ⟨h₁, h₂⟩
  | star => simp

 @[simp]
def prune : Regex α → Regex α
  | epsilon => epsilon
  | pred c => pred c
  | plus r₁ r₂ =>
    if r₁.highNullable
      then epsilon
    else if r₁.nullable
      then r₁.prune
      else plus r₁.prune r₂.prune
  | mul r₁ r₂ =>
    if r₁.highNullable ∧ r₂.highNullable
      then epsilon
      else match r₁ with
        | epsilon => r₂.prune
        | pred c => mul (pred c) r₂
        | plus r₁₁ r₁₂ =>
          if (r₁₁.mul r₂).highNullable
            then epsilon
            else if (r₁₁.mul r₂).nullable
              then (r₁₁.mul r₂).prune
              else plus (r₁₁.mul r₂).prune (r₁₂.mul r₂).prune
        | mul r₁₁ r₁₂ => (mul r₁₁ (r₁₂.mul r₂)).prune
        | star r => mul r.star r₂.prune
  | star r => r.star
termination_by r => (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem prune_highNullable {r : Regex α} (hn : r.highNullable) :
  r.prune = epsilon := by
  induction r with
  | epsilon => simp
  | pred => simp at hn
  | plus r₁ r₂ =>
    simp at hn
    simp [prune, hn]
  | mul r₁ r₂ =>
    simp at hn
    rw [prune.eq_def]
    simp [hn]
  | star r => simp at hn

variable {σ : Type u} [EffectiveBooleanAlgebra α σ]

@[simp]
def deriv : Regex α → σ → Regex α
  | epsilon, _ => pred ⊥
  | pred c, d => if denote c d then epsilon else pred ⊥
  | plus r₁ r₂, c => (r₁.deriv c).plus (r₂.deriv c)
  | mul epsilon r₂, c => r₂.deriv c
  | mul (pred c) r₂, d => if denote c d then r₂ else pred ⊥
  | mul (plus r₁₁ r₁₂) r₂, c => plus ((r₁₁.mul r₂).deriv c) ((r₁₂.mul r₂).deriv c)
  | mul (mul r₁₁ r₁₂) r₂, c => (r₁₁.mul (r₁₂.mul r₂)).deriv c
  | mul (star r) r₂, c => plus ((r.deriv c).mul (r.star.mul r₂)) (r₂.deriv c)
  | star r, c => (r.deriv c).mul r.star
  termination_by r => (r.size, r.left.size)
  decreasing_by all_goals (simp only [left, size]; omega)

def matchEnd : Regex α → Loc σ → Option (Loc σ)
  | r, (u, []) =>
    if r.nullable
      then some (u, [])
      else none
  | r, (u, c :: v) =>
    match matchEnd (r.prune.deriv c) (c :: u, v) with
    | none => if r.nullable then some (u, c::v) else none
    | some loc => some loc
termination_by _ loc => loc.right.length

def rmatch : Regex α → List σ → Option (Loc σ)
  | r, s => matchEnd r ([], s)

theorem matchEnd_soundness (r : Regex α) (s₁ s₂ s₁' s₂' : List σ) :
  r.matchEnd (s₁, s₂) = some (s₁', s₂') → Loc.word (s₁, s₂) = Loc.word (s₁', s₂') := by
  intro h
  induction s₂ generalizing r s₁ with
  | nil =>
    simp [matchEnd] at h
    rw [h.right.left, h.right.right]
  | cons x xs ih =>
    simp [matchEnd] at h
    cases k : (r.prune.deriv x).matchEnd (x::s₁, xs) with
    | none =>
      simp [k] at h
      rw [h.right.left, h.right.right]
    | some l =>
      simp [k] at h
      rw [h] at k
      apply ih at k
      rw [←k]
      simp

theorem soundness (r : Regex α) (s : List σ) (loc : Loc σ) :
  r.rmatch s = some loc → s = loc.word := by
  intro h
  cases s with
  | nil =>
    simp [rmatch, matchEnd] at h
    simp [←h.right]
  | cons x xs =>
    simp [rmatch, matchEnd] at h
    cases k : (r.prune.deriv x).matchEnd ([x], xs) with
    | none =>
      simp [k] at h
      simp [←h.right]
    | some l =>
      simp [k] at h
      rw [h] at k
      apply matchEnd_soundness at k
      exact k
