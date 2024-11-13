import GreedyDeriv.Locations
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ApplyAt
-- import Mathlib

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
  | star r => r.highNullable

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
  | mul r₁ r₂, c =>
    if highNullable r₁
      then (r₂.deriv c).plus ((r₁.deriv c).mul r₂)
      else if nullable r₁
        then ((r₁.deriv c).mul r₂).plus (r₂.deriv c)
        else (r₁.deriv c).mul r₂
  | star r, c => (r.deriv c).mul r.star

@[simp]
def prune (r : Regex α) : Regex α :=
  match r, r.nullable, r.highNullable with
  | r, false, _ => r
  | _, true, true => one
  | mul r₁ r₂, true, false =>
    if r₁.highNullable
      then r₂.prune
      else
        match r₁ with
        | zero => mul zero r₂
        | one => mul one r₂
        | char c => mul (char c) r₂
        -- | plus r₁₁ r₁₂ => prune (plus (mul r₁₁ r₂) (mul r₁₂ r₂))
        | plus r₁₁ r₁₂ => mul (plus r₁₁ r₁₂) r₂
        -- | mul r₁₁ r₁₂ => prune (mul r₁₁ (mul r₁₂ r₂))
        | mul r₁₁ r₁₂ => mul r₁₁ (mul r₁₂ r₂)
        | star r => plus (mul (prune r) (mul (star r) r₂)) (prune r₂)
  | plus r₁ r₂, true, false =>
    if r₁.nullable
      then r₁.prune
      else plus r₁ (r₂.prune)
  | r, true, false => r

theorem prune_highNullable {α : Type u} {r : Regex α} (h : r.highNullable) :
  r.prune = one := by
  unfold prune
  rw [h, highNullable_nullable h]
  simp

theorem prune_not_nullable {α : Type u} {r : Regex α} (hn : ¬r.nullable) :
  r.prune = r := by
  rw [prune]
  simp at hn
  exact hn

theorem prune_plus_left_nullable {α : Type u} {r₁ r₂ : Regex α} (hr : r₁.nullable) (hn : ¬r₁.highNullable) :
  (r₁.plus r₂).prune = r₁.prune := by
  simp_all

theorem prune_plus_right_nullable {α : Type u} {r₁ r₂ : Regex α} (hr₁ : ¬r₁.nullable) (hr₂ : r₂.nullable) (hn : ¬r₁.highNullable) :
  (r₁.plus r₂).prune = r₁.prune.plus (r₂.prune) := by
  simp_all

theorem prune_plus_left_highNullable {α : Type u} {r₁ r₂ : Regex α} (hr : r₁.highNullable) :
  (r₁.plus r₂).prune = one := by
  have hn : (r₁.plus r₂).nullable := by
    simp
    exact Or.inl (highNullable_nullable hr)

  unfold prune
  rw [hn]
  simp [hr]

theorem prune_star_highNullable {α : Type u} {r : Regex α} (hr : r.highNullable) :
  r.star.prune = one := by
  simp_all

theorem prune_star_not_highNullable {α : Type u} {r : Regex α} (hr : ¬r.highNullable) :
  r.star.prune = r.star := by
  simp_all

theorem prune_mul_left_highNullable {α : Type u} {r₁ r₂ : Regex α} (hr₁ : r₁.highNullable) (hr₂ : r₂.nullable) (hr₂' : ¬r₂.highNullable) :
  (r₁.mul r₂).prune = r₂.prune := by
  have hn : (r₁.mul r₂).nullable := by
    simp
    exact ⟨highNullable_nullable hr₁, hr₂⟩

  have hn' : (r₁.mul r₂).highNullable = false := by
    simp
    intro
    simp [hr₂']

  generalize h : r₂.prune = x
  unfold prune
  rw [hn, hn']
  simp [hr₁]
  exact h

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
