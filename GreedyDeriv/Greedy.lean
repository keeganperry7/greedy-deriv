import GreedyDeriv.Regex
import Mathlib.Tactic

variable {α : Type u}

inductive Greedy : Regex α → Loc α → Prop
  | one (s : List α) :
    Greedy .one ⟨[], s⟩
  | char (c : α) (s : List α) :
    Greedy (.char c) ⟨[c], s⟩
  | plus_left (r₁ r₂ : Regex α) (loc : Loc α) :
    Greedy r₁ loc →
    Greedy (r₁.plus r₂) loc
  | plus_right (r₁ r₂ : Regex α) (loc : Loc α) :
    ¬(∃ s₃ s₄, s₃ ++ s₄ = loc.word ∧ r₁.matches' s₃) →
    Greedy r₂ loc →
    Greedy (r₁.plus r₂) loc
  | mul (r₁ r₂ : Regex α) (s₁ s₂ s₃ : List α) :
    Greedy r₁ ⟨s₁.reverse, s₂ ++ s₃⟩ →
    Greedy r₂ ⟨s₂.reverse, s₃⟩ →
    Greedy (r₁.mul r₂) ⟨s₂.reverse ++ s₁.reverse, s₃⟩
  | star_nil (r : Regex α) (s : List α) :
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s ∧ r.star.matches' s₃) →
    Greedy r.star ([], s)
  | star (r : Regex α) (s₁ s₂ s₃ : List α) :
    Greedy r ⟨s₁.reverse, s₂ ++ s₃⟩ →
    Greedy r.star ⟨s₂.reverse, s₃⟩ →
    Greedy r.star ⟨s₂.reverse ++ s₁.reverse, s₃⟩

theorem correctness (r : Regex α) (l : Loc α) :
  Greedy r l → r.matches' l.left.reverse := by
  intro h
  induction h with
  | one =>
    simp
    apply Regex.matches'.one
  | char c =>
    simp
    apply Regex.matches'.char
  | plus_left r₁ r₂ loc _ ih =>
    apply Regex.matches'.plus_left
    exact ih
  | plus_right r₁ r₂ loc _ _ ih =>
    apply Regex.matches'.plus_right
    exact ih
  | mul r₁ r₂ s₁ s₂ s₃ h₁ h₂ ih₁ ih₂ =>
    apply Regex.matches'.mul
    simp [h₁, h₂] at ih₁ ih₂
    exact ih₁
    exact ih₂
    simp
  | star_nil =>
    simp
    apply Regex.matches'.star_nil
  | star r s₁ s₂ s₃ h₁ h₂ ih₁ ih₂ =>
    simp
    simp_all
    apply Regex.matches'.star
    exact ih₁
    exact ih₂
    rfl

theorem uniqueness (r : Regex α) (l₁ l₂ : Loc α) (hl : l₁.word = l₂.word) :
  Greedy r l₁ ∧ Greedy r l₂ → l₁ = l₂ := by
  intro ⟨h₁, h₂⟩
  induction h₁ generalizing l₂ with
  | one =>
    cases h₂
    simp_all
  | char =>
    cases h₂
    simp_all
  | plus_left r₁ r₂ loc h₁ ih₁ =>
    cases h₂ with
    | plus_left =>
      apply ih₁ at hl
      simp_all
    | plus_right _ _ _ hn =>
      absurd hn
      apply correctness at h₁
      use loc.left.reverse
      use loc.right
      simp_all
  | plus_right r₁ r₂ loc hn h ih =>
    cases h₂ with
    | plus_left _ _ _ h' =>
      apply correctness at h'
      absurd hn
      use l₂.left.reverse
      use l₂.right
      simp_all
    | plus_right =>
      apply ih at hl
      simp_all
  | mul r₁ r₂ s₁ s₂ s₃ h h' ih ih'  =>
    cases h₂ with
    | mul _ _ s₁' s₂' s₃' k k' =>
      sorry
  | star_nil r s hn =>
    apply correctness at h₂
    by_cases hl' : l₂.left = []
    · simp at hl
      simp at hl'
      rw [hl'] at hl
      simp at hl
      rw [hl, ←hl']
    · absurd hn
      use l₂.left.reverse
      use l₂.right
      simp at hl
      rw [hl]
      simp
      exact ⟨hl', h₂⟩
  | star => sorry
