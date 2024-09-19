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
  | star (r : Regex α) (s : Loc α) :
    Greedy ((r.mul r.star).plus Regex.one) s →
    Greedy r.star s

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
  | star r s _ ih =>
    generalize hs' : s.left.reverse = s'
    rw [hs'] at ih
    cases ih with
    | plus_left ih =>
      cases ih with
      | mul h₁ h₂ hs' =>
        apply Regex.matches'.star
        exact h₁
        exact h₂
        exact hs'
    | plus_right ih =>
      cases ih
      apply Regex.matches'.star_nil

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
      cases r₁ with
      | zero => cases k
      | one =>
        generalize hh : s₁.reverse = t₁
        generalize hk : s₁'.reverse = t₁'
        rw [hh] at h
        rw [hk] at k
        cases h
        cases k
        simp at hh hk
        simp [hh, hk] at hl
        have ih' := ih' (s₂'.reverse, s₃')
        simp [hl] at ih'
        apply ih' at k'
        simp_all
      | char c =>
        generalize hh : s₁.reverse = t₁
        generalize hk : s₁'.reverse = t₁'
        rw [hh] at h
        rw [hk] at k
        cases h
        cases k
        simp at hh hk
        simp [hh, hk] at hl
        have ih' := ih' (s₂'.reverse, s₃')
        simp [hl] at ih'
        apply ih' at k'
        simp_all
      | plus =>
        sorry
      | mul => sorry
      | star =>
        sorry
  | star r s h₁ ih =>
    cases h₂ with
    | star _ _ h₂ =>
      apply ih at hl
      apply hl at h₂
      exact h₂
