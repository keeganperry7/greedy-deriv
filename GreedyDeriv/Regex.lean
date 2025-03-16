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
  | plus r₁ r₂ => plus r₂.reverse r₁.reverse
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
  | mul (pred c) r₂ => mul (pred c) r₂.prune
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

inductive PartialMatch : Regex α → Loc σ → Loc σ → Prop
  | epsilon {l : Loc σ} :
    PartialMatch epsilon l l
  | pred {c : α} {d : σ} {u v : List σ} :
    denote c d →
    PartialMatch (pred c) ⟨u, d::v⟩ ⟨d::u, v⟩
  | plus_left {r₁ r₂ : Regex α} {l l' : Loc σ} :
    PartialMatch r₁ l l' →
    PartialMatch (plus r₁ r₂) l l'
  | plus_right {r₁ r₂ : Regex α} {l l' : Loc σ} :
    PartialMatch r₂ l l' →
    PartialMatch (plus r₁ r₂) l l'
  | mul {r₁ r₂ : Regex α} {l k l' : Loc σ} :
    PartialMatch r₁ l k →
    PartialMatch r₂ k l' →
    PartialMatch (mul r₁ r₂) l l'
  | star_nil {r : Regex α} {lazy? : Bool} {l : Loc σ} :
    PartialMatch (star r lazy?) l l
  | stars {r : Regex α} {lazy? : Bool} {l k l' : Loc σ} :
    k.right.length < l.right.length →
    PartialMatch r l k →
    PartialMatch (star r lazy?) k l' →
    PartialMatch (star r lazy?) l l'

notation:100 "(" r ", " l ")" " → " l':40 => PartialMatch r l l'

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

theorem matches_nil (r : Regex α) (u : List σ) (l : Loc σ) :
  (r, ⟨u, []⟩) → l → l = ⟨u, []⟩ := by
  intro h
  induction r generalizing l with
  | epsilon =>
    cases h
    rfl
  | pred c => cases h
  | plus r₁ r₂ ih₁ ih₂ =>
    cases h with
    | plus_left h =>
      apply ih₁
      exact h
    | plus_right h =>
      apply ih₂
      exact h
  | mul r₁ r₂ ih₁ ih₂ =>
    cases h with
    | mul h₁ h₂ =>
      apply ih₁ at h₁
      rw [h₁] at h₂
      apply ih₂
      exact h₂
  | star r lazy? ih =>
    cases h with
    | star_nil => rfl
    | stars hk h₁ h₂ => simp at hk

theorem matchEnd'_longest (r : Regex α) (l l' : Loc σ) (h : r.matchEnd' l = some l') :
  (∀ k : Loc σ, (r, l) → k → k.pos ≤ l'.pos) := by
  intro k hm
  match l with
  | ⟨u, []⟩ =>
    simp [matchEnd'] at h
    apply matches_nil at hm
    rw [←h.right, hm]
  | ⟨u, c::v⟩ =>
    simp [matchEnd'] at h
    match h':(r.deriv c).matchEnd' (c::u, v) with
    | none =>
      rw [h'] at h
      simp at h
      sorry
    | some m =>
      sorry

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
