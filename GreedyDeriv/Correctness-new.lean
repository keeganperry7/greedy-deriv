import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

def Regex.matchEnd' : Regex α → Loc α → Option (Loc α)
  | r, (u, []) =>
    if r.nullable
      then some (u, [])
      else none
  | r, (u, c :: v) =>
    match matchEnd' (r.prune.deriv c) (c :: u, v) with
    | none => if r.nullable then some (u, c::v) else none
    | some loc => some loc
termination_by _ loc => loc.right.length

def Regex.rmatch' : Regex α → List α → Option (Loc α)
  | r, s => matchEnd' r ([], s)

@[simp]
theorem zero_matchEnd' (s₁ s₂ : List α) :
  Regex.zero.matchEnd' (s₁, s₂) = none := by
  induction s₂ generalizing s₁ with
  | nil =>
    simp [Regex.matchEnd']
  | cons x xs ih =>
    simp [Regex.matchEnd']
    rw [ih]

@[simp]
theorem one_matchEnd' (s₁ s₂ : List α) :
  Regex.one.matchEnd' (s₁, s₂) = some (s₁, s₂) := by
  cases s₂ with
  | nil => simp [Regex.matchEnd']
  | cons x xs => simp [Regex.matchEnd']

@[simp]
theorem zero_rmatch' (s : List α) :
  Regex.zero.rmatch' s = none := by
  simp [Regex.rmatch']

@[simp]
theorem one_rmatch' (s : List α) (loc : Loc α) :
  Regex.one.rmatch' s = some loc ↔ ([], s) = loc := by
  cases s with
  | nil =>
    simp [Regex.rmatch', Regex.matchEnd']
  | cons x xs =>
    simp [Regex.rmatch', Regex.matchEnd']

theorem char_rmatch' (c : α) (s : List α) (loc : Loc α) :
  (Regex.char c).rmatch' s = some loc ↔ ∃ s', c::s' = s ∧ ([c], s') = loc := by
  cases s with
  | nil =>
    simp [Regex.rmatch', Regex.matchEnd']
  | cons x xs =>
    simp [Regex.rmatch', Regex.matchEnd']
    split_ifs with hc
    · simp [hc]
    · simp_all

theorem add_matchEnd'_none (r₁ r₂ : Regex α) (s₁ s₂ : List α) :
  (r₁.plus r₂).matchEnd' (s₁, s₂) = none →
  r₁.matchEnd' (s₁, s₂) = none ∧ r₂.matchEnd' (s₁, s₂) = none := by
  induction s₂ generalizing r₁ r₂ s₁ with
  | nil => simp [Regex.matchEnd']
  | cons x xs ih =>
    intro h
    simp [Regex.matchEnd'] at h
    cases k : ((r₁.plus r₂).prune.deriv x).matchEnd' (x :: s₁, xs) with
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
        simp [Regex.matchEnd', h, k]
    | some =>
      rw [k] at h
      simp at h

theorem add_matchEnd' (r₁ r₂ : Regex α) (s₁ s₂ : List α) (loc : Option (Loc α)) :
  (r₁.plus r₂).matchEnd' (s₁, s₂) = loc →
  r₁.matchEnd' (s₁, s₂) = loc ∨ r₂.matchEnd' (s₁, s₂) = loc := by
  induction s₂ generalizing r₁ r₂ s₁ loc with
  | nil =>
    simp [Regex.matchEnd']
    split_ifs <;> simp_all
  | cons x xs ih =>
    intro h
    simp [Regex.matchEnd'] at h
    split_ifs at h with hr
    · by_cases hr' : r₁.highNullable
      · rw [Regex.prune_plus_nullable_highNullable _ _ (by simp [hr]) hr'] at h
        simp at h
        left
        have hr'' := Regex.highNullable_nullable _ hr'
        simp [Regex.matchEnd', hr'']
        simp [Regex.prune_highNullable _ hr'' hr']
        exact h
      · have h' := @Regex.prune_plus_nullable _ r₁ r₂ (by simp [hr]) (by simp [hr'])
        cases h' with
        | inl h' =>
          simp [Regex.matchEnd', h'.left]
          left
          rw [h'.right] at h
          exact h
        | inr h' =>
          have hr := Or.resolve_left hr h'.left
          simp [Regex.matchEnd', hr, h'.left]
          rw [h'.right, Regex.deriv] at h
          cases k : (((r₁.prune.deriv x).plus (r₂.prune.deriv x))).matchEnd' (x :: s₁, xs) with
          | none =>
            simp [k] at h
            apply add_matchEnd'_none at k
            simp [k.right, h]
          | some l =>
            simp at ih
            cases ih (r₁.deriv x) (r₂.prune.deriv x) (x::s₁) <;> simp_all
    · simp at hr ih
      simp [Regex.prune_not_nullable, hr, Regex.deriv] at h
      cases ih (r₁.deriv x) (r₂.deriv x) (x::s₁) <;> simp_all [Regex.matchEnd']

theorem add_rmatch' (r₁ r₂ : Regex α) (s : List α) (loc : Loc α) :
  (r₁.plus r₂).rmatch' s = some loc →
  (r₁.rmatch' s = some loc ∨ r₂.rmatch' s = some loc) := by
  intro h
  apply add_matchEnd' at h
  simp [Regex.rmatch']
  exact h

-- Main correctness theorem
theorem rmatch_greedy (r : Regex α) (s : List α) (loc : Loc α) :
  r.rmatch' s = some loc → Greedy r loc := by
  induction r with
  | zero => simp
  | one =>
    intro h
    simp at h
    rw [←h]
    apply Greedy.one
  | char c =>
    intro h
    rw [char_rmatch'] at h
    let ⟨s', _, h⟩ := h
    rw [←h]
    apply Greedy.char
  | plus r₁ r₂ ih₁ ih₂ =>
    intro h
    apply add_rmatch' at h
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
