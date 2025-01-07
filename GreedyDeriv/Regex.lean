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
  | lazy_star : Regex α → Regex α
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
  | lazy_star r => 1 + r.size

@[simp]
def left : Regex α → Regex α
  | epsilon => epsilon
  | pred c => pred c
  | plus r₁ r₂ => plus r₁ r₂
  | mul r₁ _ => r₁
  | star r => star r
  | lazy_star r => lazy_star r

def reverse : Regex α → Regex α
  | epsilon => epsilon
  | pred c => pred c
  | plus r₁ r₂ => plus r₂.reverse r₁.reverse
  | mul r₁ r₂ => mul r₂.reverse r₁.reverse
  | star r => star r.reverse
  | lazy_star r => lazy_star r.reverse

/-! ### Derivatives -/

@[simp]
def nullable : Regex α → Bool
  | epsilon => true
  | pred _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ => true
  | lazy_star _ => true

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
  | mul (lazy_star r) r₂, c => plus (r₂.deriv c) ((r.deriv c).mul (r.lazy_star.mul r₂))
  | star r, c => (r.deriv c).mul r.star
  | lazy_star r, c => (r.deriv c).mul r.lazy_star
  termination_by r => (r.size, r.left.size)
  decreasing_by all_goals (simp only [left, size]; omega)

@[simp]
def existsMatch : Regex α → Loc σ → Bool
  | r, ⟨_, []⟩ => r.nullable
  | r, ⟨u, c::v⟩ => r.nullable || (r.deriv c).existsMatch ⟨c::u, v⟩
termination_by _ l => l.right.length

@[simp]
theorem epsilon_existsMatch (s₁ s₂ : List σ) :
  (@epsilon α).existsMatch (s₁, s₂) = true := by
  cases s₂ <;> simp

@[simp]
theorem bot_not_existsMatch (s₁ s₂ : List σ) :
  (@pred α ⊥).existsMatch (s₁, s₂) = false := by
  induction s₂ generalizing s₁ with
  | nil => simp
  | cons x xs ih =>
    simp
    apply ih

theorem nullable_existsMatch (r : Regex α) (s₁ s₂ : List σ) (hn : r.nullable) :
  r.existsMatch (s₁, s₂) = true := by
  cases s₂ <;> simp [hn]

theorem plus_existsMatch (r₁ r₂ : Regex α) (s₁ s₂ : List σ) :
  (r₁.plus r₂).existsMatch (s₁, s₂) = (r₁.existsMatch (s₁, s₂) || r₂.existsMatch (s₁, s₂)) := by
  induction s₂ generalizing s₁ r₁ r₂ with
  | nil => simp
  | cons x xs ih =>
    unfold existsMatch
    rw [Regex.deriv, ih]
    simp
    ac_rfl

 @[simp]
def prune : Regex α → Loc σ → Regex α
  | epsilon, _ => epsilon
  | pred c, _ => pred c
  | plus r₁ r₂, l =>
    if r₁.nullable
      then r₁.prune l
      else plus (r₁.prune l) (r₂.prune l)
  | mul epsilon r₂, l => r₂.prune l
  | mul (pred c) r₂, _ => mul (pred c) r₂
  | mul (plus r₁₁ r₁₂) r₂, l =>
    if (r₁₁.mul r₂).nullable
      then (r₁₁.mul r₂).prune l
      else plus ((r₁₁.mul r₂).prune l) ((r₁₂.mul r₂).prune l)
  | mul (mul r₁₁ r₁₂) r₂, l => (mul r₁₁ (r₁₂.mul r₂)).prune l
  | mul (star r) r₂, l =>
    if r₂.existsMatch l
      then mul (r.prune l).star (r₂.prune l)
      else mul r.star (r₂.prune l)
  | mul (lazy_star r) r₂, l =>
    if r₂.existsMatch l
      then r₂.prune l
      else mul r.lazy_star (r₂.prune l)
  | star r, l => (r.prune l).star
  | lazy_star _, _ => epsilon
termination_by r => (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

def matchEnd : Regex α → Loc σ → Option (Loc σ)
  | r, (u, []) =>
    if r.nullable
      then some (u, [])
      else none
  | r, (u, c :: v) =>
    match matchEnd ((r.prune (u, c::v)).deriv c) (c :: u, v) with
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
    cases k : ((r.prune (s₁, x::xs)).deriv x).matchEnd (x::s₁, xs) with
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
    cases k : ((r.prune ([], x::xs)).deriv x).matchEnd ([x], xs) with
    | none =>
      simp [k] at h
      simp [←h.right]
    | some l =>
      simp [k] at h
      rw [h] at k
      apply matchEnd_soundness at k
      exact k
