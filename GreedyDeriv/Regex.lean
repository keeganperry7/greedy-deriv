import GreedyDeriv.Locations
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ApplyAt

inductive Regex (α :  Type u) : Type u where
  | zero : Regex α
  | one : Regex α
  | char : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  deriving Repr

namespace Regex

variable {α : Type u}

@[simp]
def size : Regex α → Nat
  | zero => 1
  | one => 1
  | char _ => 1
  | plus r₁ r₂ => 1 + r₁.size + r₂.size
  | mul r₁ r₂ => 1 + r₁.size + r₂.size
  | star r => 1 + r.size

@[simp]
def left : Regex α → Regex α
  | zero => zero
  | one => one
  | char c => char c
  | plus r₁ r₂ => plus r₁ r₂
  | mul r₁ _ => r₁
  | star r => star r

inductive matches' : Regex α → List α → Prop where
  | one : matches' one []
  | char (c : α) : matches' (char c) [c]
  | plus_left {r₁ r₂ : Regex α} {s : List α} :
    r₁.matches' s →
    (r₁.plus r₂).matches' s
  | plus_right {r₁ r₂ : Regex α} {s : List α} :
    r₂.matches' s →
    (r₁.plus r₂).matches' s
  | mul {r₁ r₂ : Regex α} {s₁ s₂ s : List α} :
    r₁.matches' s₁ →
    r₂.matches' s₂ →
    s₁ ++ s₂ = s →
    (r₁.mul r₂).matches' s
  | star_nil {r : Regex α} :
    r.star.matches' []
  | star {r : Regex α} {s₁ s₂ s : List α} :
    r.matches' s₁ →
    r.star.matches' s₂ →
    s₁ ++ s₂ = s →
    r.star.matches' s

/-! ### Derivatives -/

variable [DecidableEq α]

@[simp]
def nullable : Regex α → Bool
  | zero => false
  | one => true
  | char _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ => true

theorem nullable_matches' {α : Type u} {r : Regex α} :
  r.nullable → r.matches' [] := by
  intro h
  induction r with
  | zero => simp at h
  | one => apply matches'.one
  | char => simp at h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at h
    cases h with
    | inl h =>
      apply ih₁ at h
      apply matches'.plus_left
      exact h
    | inr h =>
      apply ih₂ at h
      apply matches'.plus_right
      exact h
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at h
    simp [h] at ih₁ ih₂
    apply matches'.mul
    exact ih₁
    exact ih₂
    rfl
  | star => apply matches'.star_nil

@[simp]
def highNullable : Regex α → Bool
  | zero => false
  | one => true
  | char _ => false
  | plus r₁ _ => r₁.highNullable
  | mul r₁ r₂ => r₁.highNullable && r₂.highNullable
  | star _ => false

theorem highNullable_nullable {α : Type u} {r : Regex α} :
  r.highNullable → r.nullable := by
  induction r with
  | zero => simp
  | one => simp
  | char => simp
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
def deriv : Regex α → α → Regex α
  | zero, _ => zero
  | one, _ => zero
  | char c, c' => if c = c' then one else zero
  | plus r₁ r₂, c => (r₁.deriv c).plus (r₂.deriv c)
  | mul zero _, _ => zero
  | mul one r₂, c => r₂.deriv c
  | mul (char c) r₂, c' => if c = c' then r₂ else zero
  | mul (plus r₁₁ r₁₂) r₂, c => plus ((r₁₁.mul r₂).deriv c) ((r₁₂.mul r₂).deriv c)
  | mul (mul r₁₁ r₁₂) r₂, c => (r₁₁.mul (r₁₂.mul r₂)).deriv c
  | mul (star r) r₂, c => plus ((r.deriv c).mul (r.star.mul r₂)) (r₂.deriv c)
  | star r, c => (r.deriv c).mul r.star
  termination_by r => (r.size, r.left.size)
  decreasing_by
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic
    · simp
      omega
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic

 @[simp]
def prune : Regex α → Regex α
  | zero => zero
  | one => one
  | char c => char c
  | plus r₁ r₂ =>
    if r₁.highNullable
      then one
    else if r₁.nullable
      then r₁.prune
      else plus r₁.prune r₂.prune
  | mul r₁ r₂ =>
    if r₁.highNullable ∧ r₂.highNullable
      then one
      else match r₁ with
        | zero => zero
        | one => r₂.prune
        | char c => mul (char c) r₂
        | plus r₁₁ r₁₂ =>
          if (r₁₁.mul r₂).highNullable
            then one
            else if (r₁₁.mul r₂).nullable
              then (r₁₁.mul r₂).prune
              else plus (r₁₁.mul r₂).prune (r₁₂.mul r₂).prune
        | mul r₁₁ r₁₂ => (mul r₁₁ (r₁₂.mul r₂)).prune
        | star r => mul r.star r₂.prune
  | star r => r.star
termination_by r => (r.size, r.left.size)
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · simp only [size, left]
    omega
  · decreasing_tactic

theorem prune_highNullable {α : Type u} {r : Regex α} (hn : r.highNullable) :
  r.prune = one := by
  induction r with
  | zero => simp at hn
  | one => simp
  | char => simp at hn
  | plus r₁ r₂ =>
    simp at hn
    simp [prune, hn]
  | mul r₁ r₂ =>
    simp at hn
    rw [prune.eq_def]
    simp [hn]
  | star r => simp at hn

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

def rmatch : Regex α → List α → Option (Loc α)
  | r, s => matchEnd r ([], s)

theorem matchEnd_soundness (r : Regex α) (s₁ s₂ s₁' s₂' : List α) :
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

theorem soundness (r : Regex α) (s : List α) (loc : Loc α) :
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
