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
  | mul {r₁ r₂ : Regex α} {s₁ s₂ : List α} :
    r₁.matches' s₁ →
    r₂.matches' s₂ →
    (r₁.mul r₂).matches' (s₁ ++ s₂)
  | star_nil {r : Regex α} :
    r.star.matches' []
  | star {r : Regex α} {s₁ s₂ : List α} :
    r.matches' s₁ →
    r.star.matches' s₂ →
    r.star.matches' (s₁ ++ s₂)

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

@[simp]
def highNullable : Regex α → Bool
  | zero => false
  | one => true
  | char _ => false
  | plus r₁ _ => r₁.highNullable
  | mul r₁ r₂ => r₁.highNullable && r₂.highNullable
  | star r => r.highNullable

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

def prune (r : Regex α) : Regex α :=
  match r, r.nullable, r.highNullable with
  | r, false, _ => r
  | _, true, true => one
  | mul r₁ r₂, true, false =>
    if r₁.highNullable
      then r₂.prune
      else mul r₁ r₂
  | r, true, false => r

def matchEnd : Regex α → Loc α → Option (Loc α) → Option (Loc α)
  | r, ⟨u, []⟩, cur =>
    if r.nullable
      then some ⟨u, []⟩
      else cur
  | r, ⟨u, c :: v⟩, cur =>
    if r.nullable
      then matchEnd (r.prune.deriv c) ⟨c :: u, v⟩ (some ⟨u, c::v⟩)
      else matchEnd (r.prune.deriv c) ⟨c :: u, v⟩ cur
termination_by _ loc => loc.right.length

def rmatch : Regex α → List α → Option (Loc α)
  | r, s => matchEnd r ⟨[], s⟩ none

theorem matchEnd_soundness (r : Regex α) (s₁ s₂ s₁' s₂': List α) (cur : Option (Loc α)) :
  (some (Loc.word (s₁, s₂)) = cur.map Loc.word  ∨ cur = none) →
  r.matchEnd (s₁, s₂) cur = some (s₁', s₂') → Loc.word (s₁, s₂) = Loc.word (s₁', s₂') := by
  intro h_cur h
  induction s₂ generalizing r s₁ cur with
  | nil =>
    cases h_cur with
    | inl h_cur =>
      simp [matchEnd] at h
      split_ifs at h
      · simp at h
        rw [h]
      · rw [h, Option.map_some'] at h_cur
        simp_all
    | inr h_cur =>
      rw [h_cur] at h
      simp [matchEnd] at h
      rw [h.right]
  | cons x xs ih =>
    cases h_cur with
    | inl h_cur =>
      simp [matchEnd] at h
      split_ifs at h with hr
      · have ih := ih _ _ _ (by simp) h
        rw [←ih]
        simp
      · have ih := ih (r.prune.deriv x) (x::s₁) (cur)
        rw [←h_cur] at ih
        have ih := ih (by simp) h
        rw [←ih]
        simp
    | inr h_cur =>
      rw [h_cur] at h
      simp [matchEnd] at h
      split_ifs at h with hr
      · have ih := ih _ _ _ (by simp) h
        rw [←ih]
        simp
      · have ih := ih _ _ none (by simp) h
        rw [←ih]
        simp

theorem soundness (r : Regex α) (s : List α) (loc : Loc α) :
  r.rmatch s = some loc → s = loc.word := by
  cases s with
  | nil =>
    intro h
    unfold rmatch matchEnd at h
    simp at h
    simp [←h.right]
  | cons x xs =>
    simp [rmatch, matchEnd]
    split_ifs with h'
    · intro h
      apply matchEnd_soundness at h
      simp at h
      exact h
      simp
    · intro h
      apply matchEnd_soundness at h
      simp at h
      exact h
      simp
