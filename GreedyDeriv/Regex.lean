import GreedyDeriv.Locations
import GreedyDeriv.EffectiveBooleanAlgebra
import Mathlib.Tactic.ApplyAt

inductive Regex (α :  Type u) : Type u where
  | epsilon : Regex α
  | pred : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Bool → Regex α
  deriving Repr

namespace Regex

variable {α : Type u}

@[simp]
def size : Regex α → Nat
  | epsilon => 1
  | pred _ => 1
  | plus r₁ r₂ => 1 + r₁.size + r₂.size
  | mul r₁ r₂ => 1 + r₁.size + r₂.size
  | star r _ => 1 + r.size

@[simp]
def left : Regex α → Regex α
  | epsilon => epsilon
  | pred c => pred c
  | plus r₁ r₂ => plus r₁ r₂
  | mul r₁ _ => r₁
  | star r lazy? => star r lazy?

def reverse : Regex α → Regex α
  | epsilon => epsilon
  | pred c => pred c
  | plus r₁ r₂ => plus r₁.reverse r₂.reverse
  | mul r₁ r₂ => mul r₂.reverse r₁.reverse
  | star r lazy? => star r.reverse lazy?

/-! ### Derivatives -/

@[simp]
def nullable : Regex α → Bool
  | epsilon => true
  | pred _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ _ => true

 @[simp]
def prune : Regex α → Regex α
  | epsilon => epsilon
  | pred c => pred c
  | plus r₁ r₂ =>
    if r₁.nullable
      then r₁.prune
      else plus r₁.prune r₂.prune
  | mul epsilon r₂ => r₂.prune
  | mul (pred c) r₂ => mul (pred c) r₂
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

variable {σ : Type u} [EffectiveBooleanAlgebra α σ]

inductive Matches : Regex α → Loc σ → Loc σ → Prop
  | epsilon (l : Loc σ) :
    Matches epsilon l l
  | pred (c : α) (d : σ) (u v : List σ) :
    denote c d →
    Matches (pred c) (u, d::v) (d::u, v)
  | plus_left {r₁ r₂ : Regex α} {l₁ l₂ : Loc σ} :
    Matches r₁ l₁ l₂ →
    Matches (plus r₁ r₂) l₁ l₂
  | plus_right {r₁ r₂ : Regex α} {l₁ l₂ : Loc σ} :
    Matches r₂ l₁ l₂ →
    Matches (plus r₁ r₂) l₁ l₂
  | mul {r₁ r₂ : Regex α} (l₁ l₂ l₃ : Loc σ) :
    Matches r₁ l₁ l₂ →
    Matches r₂ l₂ l₃ →
    Matches (mul r₁ r₂) l₁ l₃
  | star_nil {r : Regex α} {lazy? : Bool} {l : Loc σ} :
    Matches (star r lazy?) l l
  | stars {r : Regex α} {lazy? : Bool} (l₁ l₂ l₃ : Loc σ) :
    Matches r l₁ l₂ →
    Matches (star r lazy?) l₂ l₃ →
    Matches (star r lazy?) l₁ l₃

theorem Matches_distrib (r₁ r₂ r₃ : Regex α) (l₁ l₂ : Loc σ) :
  Matches (mul (plus r₁ r₂) r₃) l₁ l₂ ↔ Matches (plus (mul r₁ r₃) (mul r₂ r₃)) l₁ l₂ := by
  sorry

theorem Matches_mul_assoc (r₁ r₂ r₃ : Regex α) (l₁ l₂ : Loc σ) :
  Matches (mul (mul r₁ r₂) r₃) l₁ l₂ ↔ Matches (mul r₁ (mul r₂ r₃)) l₁ l₂ := by
  sorry

@[simp]
def deriv : Regex α → σ → Regex α
  | epsilon, _ => pred ⊥
  | pred c, d => if denote c d then epsilon else pred ⊥
  | plus r₁ r₂, c => (r₁.deriv c).plus (r₂.deriv c)
  | mul epsilon r₂, c => r₂.deriv c
  | mul (pred c) r₂, d => if denote c d then r₂ else pred ⊥
  | mul (plus r₁₁ r₁₂) r₂, c => plus ((r₁₁.mul r₂).deriv c) ((r₁₂.mul r₂).deriv c)
  | mul (mul r₁₁ r₁₂) r₂, c => (r₁₁.mul (r₁₂.mul r₂)).deriv c
  | mul (star r false) r₂, c => plus ((r.deriv c).mul ((r.star false).mul r₂)) (r₂.deriv c)
  | mul (star r true) r₂, c => plus (r₂.deriv c) ((r.deriv c).mul ((r.star true).mul r₂))
  | star r false, c => (r.deriv c).mul (r.star false)
  | star r true, c => (r.deriv c).mul (r.star true)
  termination_by r => (r.size, r.left.size)
  decreasing_by all_goals (simp only [left, size]; omega)

@[simp]
theorem deriv_star (r : Regex α) (lazy? : Bool) (c : σ) :
  (r.star lazy?).deriv c = (r.deriv c).mul (r.star lazy?) := by
  cases lazy? <;> simp

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

def matchEnd' : Regex α → Loc σ → Option (Loc σ)
  | r, (u, []) =>
    if r.nullable
      then some (u, [])
      else none
  | r, (u, c :: v) =>
    match matchEnd' (r.deriv c) (c :: u, v) with
    | none => if r.nullable then some (u, c::v) else none
    | some loc => some loc
termination_by _ loc => loc.right.length

def rmatch : Regex α → List σ → Option (Loc σ)
  | r, s => matchEnd r ([], s)

def rmatchAux : Regex α → List σ → List σ → Option (Span σ)
  | r, [], k => if r.nullable then some ⟨k, [], []⟩ else none
  | r, c::s, k =>
    match matchEnd r ([], c::s) with
    | none => r.rmatchAux s (c::k)
    | some ⟨u, v⟩ => some ⟨k, u.reverse, v⟩

def rmatch' : Regex α → List σ → Option (Span σ)
  | r, s => rmatchAux r s []

theorem matchEnd'_matches (r : Regex α) (s₁ s₂ : List σ) (l : Loc σ) :
  matchEnd' r (s₁, s₂) = some l → r.Matches (s₁, s₂) l := by
  intro h
  induction r with
  | epsilon =>
    cases s₂ with
    | nil =>
      rw [Regex.matchEnd'] at h
      simp at h
      rw [h]
      apply Matches.epsilon
    | cons x xs =>
      sorry
  | pred => sorry
  | plus => sorry
  | mul => sorry
  | star =>
    sorry

theorem matches_suffix (r : Regex α) (l l' : Loc σ) :
  Matches r l l' → l.pos ≤ l'.pos := by
  intro h
  induction r generalizing l l' with
  | epsilon =>
    cases h
    rfl
  | pred c =>
    cases h
    simp
  | plus r₁ r₂ ih₁ ih₂ =>
    cases h with
    | plus_left h => exact ih₁ l l' h
    | plus_right h => exact ih₂ l l' h
  | mul r₁ r₂ ih₁ ih₂ =>
    cases h with
    | mul _ k _ h₁ h₂ =>
      apply ih₁ at h₁
      apply ih₂ at h₂
      exact Nat.le_trans h₁ h₂
  | star r lazy? ih =>
    cases h with
    | star_nil => rfl
    | stars _ k _ h h' =>
      apply ih at h
      sorry

theorem matches_deriv (r : Regex α) (x : σ) (s₁ xs : List σ) (l : Loc σ) :
  Matches (r.deriv x) (x :: s₁, xs) l →
  Matches r (s₁, x::xs) l := by
  intro h
  induction r generalizing l with
  | epsilon =>
    simp at h
    cases h with
    | pred _ _ _ _ h => simp at h
  | pred f =>
    simp at h
    split_ifs at h with hf
    · cases h
      apply Matches.pred
      exact hf
    · cases h with
      | pred _ _ _ _ h => simp at h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at h
    cases h with
    | plus_left h =>
      apply ih₁ at h
      exact Matches.plus_left h
    | plus_right  h =>
      apply ih₂ at h
      exact Matches.plus_right h
  | mul r₁ r₂ ih₁ ih₂ =>
    sorry
  | star r lazy? ih =>
    simp at h
    cases h with
    | mul _ k _ h₁ h₂ =>
      apply ih at h₁
      apply Matches.stars
      exact h₁
      exact h₂

theorem matches_deriv_le (r : Regex α) (x : σ) (s₁ xs : List σ) (l l' : Loc σ) :
  Matches (r.deriv x) (x :: s₁, xs) l →
  Matches r (s₁, x::xs) l' →
  l'.pos ≤ l.pos := by
  intro h₁ h₂
  induction r with
  | epsilon =>
    simp at h₁
    cases h₁
    simp at *
  | pred c =>
    simp at h₁
    split_ifs at h₁ with hc
    · cases h₂
      cases h₁
      simp
    · cases h₁
      simp at *
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at h₁
    cases h₁ with
    | plus_left h₁ =>
      sorry
    | plus_right => sorry
  | mul r₁ r₂ => sorry
  | star r lazy => sorry

theorem matchEnd'_longest (r : Regex α) (s₁ s₂ : List σ) (l : Loc σ) (h : matchEnd' r (s₁, s₂) = some l) :
  (∀ l' : Loc σ, Matches r (s₁, s₂) l' → l'.pos ≤ l.pos) := by
  induction s₂ generalizing r s₁ with
  | nil =>
    intro l' hl'
    rw [Regex.matchEnd'] at h
    split_ifs at h
    · simp at h
      rw [←h]
      simp
      sorry
  | cons x xs ih =>
    intro l' hl'
    rw [Regex.matchEnd'] at h
    cases k : ((r.deriv x).matchEnd' (x :: s₁, xs)) with
    | none =>
      rw [k] at h
      simp at h
      sorry
    | some v =>
      rw [k] at h
      simp at h
      rw [h] at k
      have tmp := matchEnd'_matches (r.deriv x) (x::s₁) xs l k
      sorry

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
