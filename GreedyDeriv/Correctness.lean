import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

@[simp]
theorem zero_matchEnd (s₁ s₂ : List α) (cur : Option (Loc α)) :
  Regex.zero.matchEnd (s₁, s₂) cur = cur := by
  induction s₂ generalizing s₁ with
  | nil => simp [Regex.matchEnd]
  | cons x xs ih =>
    simp [Regex.matchEnd]
    apply ih

@[simp]
theorem one_matchEnd (s₁ s₂ : List α) (cur : Option (Loc α)) :
  Regex.one.matchEnd (s₁, s₂) cur = some (s₁, s₂) := by
  cases s₂ with
  | nil => simp [Regex.matchEnd]
  | cons x xs => simp [Regex.matchEnd]

@[simp]
theorem zero_rmatch (s : List α) :
  Regex.zero.rmatch s = none := by
  simp [Regex.rmatch]

@[simp]
theorem one_rmatch (s : List α) (loc : Loc α) :
  Regex.one.rmatch s = some loc ↔ ([], s) = loc := by
  cases s with
  | nil =>
    simp [Regex.rmatch, Regex.matchEnd]
  | cons x xs =>
    simp [Regex.rmatch, Regex.matchEnd]

theorem char_rmatch (c : α) (s : List α) (loc : Loc α) :
  (Regex.char c).rmatch s = some loc ↔ ∃ s', c::s' = s ∧ ([c], s') = loc := by
  cases s with
  | nil =>
    simp [Regex.rmatch, Regex.matchEnd]
  | cons x xs =>
    simp [Regex.rmatch, Regex.matchEnd]
    split_ifs with hc
    · simp [hc]
    · simp_all

theorem add_matchEnd (r₁ r₂ : Regex α) (s₁ s₂ : List α) (loc : Loc α) (cur : Option (Loc α)) :
  (r₁.plus r₂).matchEnd (s₁, s₂) cur = some loc →
  r₁.matchEnd (s₁, s₂) cur = some loc ∨ r₂.matchEnd (s₁, s₂) cur = some loc := by
  induction s₂ generalizing r₁ r₂ s₁ cur with
  | nil =>
    simp [Regex.matchEnd]
    split_ifs <;> (intro h; simp_all)
  | cons x xs ih =>
    intro h
    simp [Regex.matchEnd] at h
    split_ifs at h with hr
    · by_cases hr' : r₁.highNullable
      · rw [Regex.prune_plus_nullable_highNullable _ _ (by simp [hr]) hr'] at h
        simp at h
        left
        have hr'' := Regex.highNullable_nullable _ hr'
        simp [Regex.matchEnd, hr'']
        rw [Regex.prune_highNullable _ hr'' hr']
        simp
        exact h
      ·
        have h' := @Regex.prune_plus_nullable _ r₁ r₂ (by simp [hr]) (by simp [hr'])
        cases h' with
        | inl h' =>
          simp [Regex.matchEnd, h'.left]
          left
          rw [h'.right] at h
          exact h
        | inr h' =>
          rw [h'.right] at h
          cases hr with
          | inl hr => exact absurd hr h'.left
          | inr hr =>
            sorry
    · simp at hr
      simp [Regex.prune_not_nullable, hr, Regex.deriv] at h
      apply ih at h
      cases h with
      | inl h =>
        left
        simp [Regex.matchEnd, hr, Regex.prune_not_nullable]
        exact h
      | inr h =>
        right
        simp [Regex.matchEnd, hr, Regex.prune_not_nullable]
        exact h

-- TODO: Add restriction to r₂ case
theorem add_rmatch (r₁ r₂ : Regex α) (s : List α) (loc : Loc α) :
  (r₁.plus r₂).rmatch s = some loc →
  (r₁.rmatch s = some loc ∨ r₂.rmatch s = some loc) := by
  intro h
  apply add_matchEnd at h
  simp [Regex.rmatch]
  exact h

-- Main correctness theorem
theorem rmatch_greedy (r : Regex α) (s : List α) (loc : Loc α) :
  r.rmatch s = some loc → Greedy r loc := by
  induction r with
  | zero => simp
  | one =>
    intro h
    simp at h
    rw [←h]
    apply Greedy.one
  | char c =>
    intro h
    rw [char_rmatch] at h
    let ⟨s', _, h⟩ := h
    rw [←h]
    apply Greedy.char
  | plus r₁ r₂ ih₁ ih₂ =>
    intro h
    apply add_rmatch at h
    cases h with
    | inl h =>
      apply ih₁ at h
      apply Greedy.plus_left
      exact h
    | inr h =>
      apply ih₂ at h
      apply Greedy.plus_right
      sorry
      exact h
  | mul => sorry
  | star => sorry
