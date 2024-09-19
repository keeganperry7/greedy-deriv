import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

@[simp]
theorem zero_matchEnd (s₁ s₂ : List α) :
  Regex.zero.matchEnd (s₁, s₂) = none := by
  induction s₂ generalizing s₁ with
  | nil =>
    simp [Regex.matchEnd]
  | cons x xs ih =>
    simp [Regex.matchEnd]
    rw [ih]

@[simp]
theorem one_matchEnd (s₁ s₂ : List α) :
  Regex.one.matchEnd (s₁, s₂) = some (s₁, s₂) := by
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

theorem add_matchEnd_none (r₁ r₂ : Regex α) (s₁ s₂ : List α) :
  (r₁.plus r₂).matchEnd (s₁, s₂) = none →
  r₁.matchEnd (s₁, s₂) = none ∧ r₂.matchEnd (s₁, s₂) = none := by
  induction s₂ generalizing r₁ r₂ s₁ with
  | nil => simp [Regex.matchEnd]
  | cons x xs ih =>
    intro h
    simp [Regex.matchEnd] at h
    cases k : ((r₁.plus r₂).prune.deriv x).matchEnd (x :: s₁, xs) with
    | none =>
      rw [k] at h
      simp at h
      by_cases hr : (r₁.plus r₂).nullable
      · by_cases hr' : r₁.highNullable
        · apply Regex.highNullable_nullable at hr'
          simp_all
        · simp_all
      · simp at hr
        simp [Regex.prune_not_nullable, hr, Regex.deriv] at k
        apply ih at k
        simp [Regex.matchEnd, h, k]
    | some =>
      rw [k] at h
      simp at h

theorem add_matchEnd (r₁ r₂ : Regex α) (s₁ s₂ : List α) (loc : Option (Loc α)) :
  (r₁.plus r₂).matchEnd (s₁, s₂) = loc →
  r₁.matchEnd (s₁, s₂) = loc ∨ r₂.matchEnd (s₁, s₂) = loc := by
  induction s₂ generalizing r₁ r₂ s₁ loc with
  | nil =>
    simp [Regex.matchEnd]
    split_ifs <;> simp_all
  | cons x xs ih =>
    intro h
    simp [Regex.matchEnd] at h
    split_ifs at h with hr
    · by_cases hr' : r₁.highNullable
      · rw [Regex.prune_plus_nullable_highNullable _ _ (by simp [hr]) hr'] at h
        simp at h
        left
        simp [Regex.matchEnd, Regex.highNullable_nullable hr']
        simp [Regex.prune_highNullable hr']
        exact h
      · have h' := @Regex.prune_plus_nullable _ r₁ r₂ (by simp [hr]) (by simp [hr'])
        cases h' with
        | inl h' =>
          simp [Regex.matchEnd, h'.left]
          left
          rw [h'.right] at h
          exact h
        | inr h' =>
          have hr := Or.resolve_left hr h'.left
          simp [Regex.matchEnd, hr, h'.left]
          rw [h'.right, Regex.deriv] at h
          cases k : (((r₁.prune.deriv x).plus (r₂.prune.deriv x))).matchEnd (x :: s₁, xs) with
          | none =>
            simp [k] at h
            apply add_matchEnd_none at k
            simp [k.right, h]
          | some l =>
            simp at ih
            cases ih (r₁.deriv x) (r₂.prune.deriv x) (x::s₁) <;> simp_all
    · simp at hr ih
      simp [Regex.prune_not_nullable, hr, Regex.deriv] at h
      cases ih (r₁.deriv x) (r₂.deriv x) (x::s₁) <;> simp_all [Regex.matchEnd]

theorem add_rmatch (r₁ r₂ : Regex α) (s : List α) (loc : Loc α) :
  (r₁.plus r₂).rmatch s = some loc →
  (r₁.rmatch s = some loc ∨ r₂.rmatch s = some loc) := by
  intro h
  apply add_matchEnd at h
  simp [Regex.rmatch]
  exact h

theorem add_rmatch_none (r₁ r₂ : Regex α) (s : List α) :
  (r₁.plus r₂).rmatch s = none →
  r₁.rmatch s = none ∧ r₂.rmatch s = none := by
  intro h
  apply add_matchEnd_none at h
  simp [Regex.rmatch]
  exact h

theorem mul_rmatch (r₁ r₂ : Regex α) (s s₁ s₂ : List α) :
  (r₁.mul r₂).rmatch s = some (s₁, s₂) →
  ∃ u v t₁ t₂ : List α, u ++ v = s ∧ t₂.reverse ++ t₁.reverse = s₁
  ∧ r₁.rmatch u = some (t₁.reverse, t₂ ++ s₂) ∧ r₂.rmatch v = some (t₂.reverse, s₂) := by
  sorry

theorem rmatch_not_matches (r : Regex α) (s : List α) :
  r.rmatch s = none → ∀ s₁ s₂, s₁ ++ s₂ = s → ¬r.matches' s₁ := by
  intro h s₁ s₂ hs
  induction r with
  | zero =>
    intro h'
    cases h'
  | one => simp [Regex.rmatch] at h
  | char c =>
    intro h'
    cases h'
    rw [←hs] at h
    simp [Regex.rmatch, Regex.matchEnd] at h
  | plus r₁ r₂ ih₁ ih₂ =>
    apply add_rmatch_none at h
    simp [h] at ih₁ ih₂
    intro h'
    cases h' with
    | plus_left h' =>
      absurd h'
      exact ih₁
    | plus_right h' =>
      absurd h'
      exact ih₂
  | mul r₁ r₂ ih₁ ih₂ => sorry
  | star r ih => sorry

theorem rmatch_matches (r : Regex α) (s s₁ s₂ : List α) :
  r.rmatch s = some (s₁, s₂) → r.matches' s₁.reverse := by
  intro h
  induction r generalizing s s₁ s₂ with
  | zero => simp at h
  | one =>
    simp at h
    simp [h]
    apply Regex.matches'.one
  | char c =>
    rw [char_rmatch] at h
    let ⟨s', h⟩ := h
    simp at h
    simp [←h.right.left]
    apply Regex.matches'.char
  | plus r₁ r₂ ih₁ ih₂ =>
    apply add_rmatch at h
    cases h with
    | inl h =>
      apply ih₁ at h
      apply Regex.matches'.plus_left
      exact h
    | inr h =>
      apply ih₂ at h
      apply Regex.matches'.plus_right
      exact h
  | mul r₁ r₂ ih₁ ih₂ =>
    apply mul_rmatch at h
    let ⟨u, v, t₁, t₂, hs, hs₁, hu, hv⟩ := h
    apply ih₁ at hu
    apply ih₂ at hv
    simp [←hs₁]
    simp at hu hv
    apply Regex.matches'.mul
    exact hu
    exact hv
    rfl
  | star => sorry

-- Main correctness theorem
theorem rmatch_greedy (r : Regex α) (s : List α) (loc : Loc α) :
  r.rmatch s = some loc → Greedy r loc := by
  induction r generalizing s loc with
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
      have hs : s = loc.word := by
        apply Regex.soundness at h
        exact h
      apply ih₂ at h
      apply Greedy.plus_right
      -- TODO: Add this to add_rmatch
      have tmp : r₁.rmatch s = none := sorry
      apply rmatch_not_matches at tmp
      rw [←hs]
      simp
      exact tmp
      exact h
  | mul r₁ r₂ ih₁ ih₂ =>
    intro h
    apply mul_rmatch at h
    let ⟨u, v, t₁, t₂, hs, hs₁, hu, hv⟩ := h
    apply ih₁ at hu
    apply ih₂ at hv
    rw [eq_comm, Prod.fst_eq_iff] at hs₁
    rw [hs₁]
    apply Greedy.mul
    exact hu
    exact hv
  | star => sorry
