import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α σ : Type u} [EffectiveBooleanAlgebra α σ]

open Regex

theorem existsMatch_accept (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  r.existsMatch (s₁, s₂) = (r.accept (s₁, s₂) k).isSome :=
  match r with
  | epsilon => by
    simp [accept]
    apply hk
  | pred c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs =>
      simp [accept]
      split_ifs with hc
      · simp
        apply hk
      · simp
  | plus r₁ r₂ => by
    simp [accept]
    rw [←existsMatch_accept r₁ _ _ _ hk]
    rw [←existsMatch_accept r₂ _ _ _ hk]
    rw [plus_existsMatch]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      cases s₂ with
      | nil =>
        simp [accept]
        rw [←existsMatch_accept r₂ _ _ _ hk]
        simp
      | cons x xs =>
        simp [accept]
        rw [←existsMatch_accept r₂ _ _ _ hk]
        simp
    | pred c =>
      cases s₂ with
      | nil => simp [accept]
      | cons x xs =>
        simp [accept]
        split_ifs
        · rw [existsMatch_accept r₂ _ _ _ hk]
        · simp
    | plus r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def]
      rw [←existsMatch_accept (r₁₁.mul r₂) _ _ _ hk]
      rw [←existsMatch_accept (r₁₂.mul r₂) _ _ _ hk]
      cases s₂ with
      | nil =>
        simp
        rw [Bool.and_or_distrib_right]
      | cons x xs =>
        simp
        rw [Bool.and_or_distrib_right, plus_existsMatch]
        ac_rfl
    | mul r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def]
      rw [←existsMatch_accept (r₁₁.mul (r₁₂.mul r₂)) _ _ _ hk]
      cases s₂ <;> (simp only [existsMatch, nullable, Regex.deriv]; rw [Bool.and_assoc])
    | .star r =>
      cases s₂ with
      | nil =>
        simp [accept]
        rw [←existsMatch_accept r₂ _ _ _ hk]
        simp
        intro h
        repeat rw [accept_nil_some_nullable] at h
        exact h.left.right
      | cons x xs =>
        sorry
    | lazy_star r =>
      cases s₂ with
      | nil =>
        simp [accept]
        rw [←existsMatch_accept r₂ _ _ _ hk]
        simp
        intro h
        repeat rw [accept_nil_some_nullable] at h
        exact h.left.right
      | cons x xs =>
        sorry
  | .star r => by
    rw [accept_nullable, nullable_existsMatch]
    simp only [Regex.nullable]
    simp only [Regex.nullable]
    apply hk
  | lazy_star r => by
    rw [accept_nullable, nullable_existsMatch]
    simp only [Regex.nullable]
    simp only [Regex.nullable]
    apply hk
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_cond (r : Regex α) (s₁ s₂ : List σ) (x : σ) (k : Loc σ → Option (Loc σ)) :
  (r.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) (fun l' ↦ if l'.right.length < (x::s₂).length then k l' else none) :=
  match r with
  | epsilon => by simp [accept]
  | pred c => by
    simp [accept]
    split_ifs
    · simp [accept]
    · simp [accept]
  | plus r₁ r₂ => by
    simp [accept]
    rw [accept_deriv_cond, accept_deriv_cond]
    simp
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      rw [accept_deriv_cond]
      simp
    | pred c =>
      simp [accept]
      split_ifs with hc
      · simp_rw [Nat.lt_add_one_iff]
        rw [accept_suffix r₂ _ none]
        rfl
      · simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      rw [accept_deriv_cond (r₁₁.mul r₂)]
      rw [accept_deriv_cond (r₁₂.mul r₂)]
      simp [accept]
    | mul r₁₁ r₁₂ =>
      simp [accept]
      rw [accept_deriv_cond (r₁₁.mul (r₁₂.mul r₂))]
      simp [accept]
    | .star r =>
      simp
      rw [accept, accept, accept, accept]
      rw [accept_deriv_cond r]
      rw [accept_deriv_cond r₂]
      simp
      simp_rw [accept_suffix r.star (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
      simp
      apply Option.or_eq
      apply fn_arg₃_eq
      ext loc t
      split_ifs with hl
      · rw [accept_mul_def]
        rw [accept_suffix r.star _ none]
        simp
        apply iff_eq_of_eq
        apply fn_arg₃_eq
        ext l u
        split_ifs with h₁
        · rw [accept_suffix r₂ _ none]
          nth_rw 2 [accept_suffix r₂ _ none]
          simp
          apply iff_eq_of_eq
          apply fn_arg₃_eq
          ext l' v
          split_ifs with h₂ h₃
          · rfl
          · absurd h₃
            apply Nat.lt_of_le_of_lt
            exact h₂
            apply Nat.lt_of_le_of_lt
            exact h₁
            exact hl
          · rfl
        · rfl
      · rfl
      rfl
    | lazy_star r =>
      simp
      rw [accept, accept, accept, accept]
      rw [accept_deriv_cond r]
      rw [accept_deriv_cond r₂]
      simp
      simp_rw [accept_suffix r.lazy_star (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
      simp
      apply Option.or_eq
      rfl
      apply fn_arg₃_eq
      ext loc t
      split_ifs with hl
      · rw [accept_mul_def]
        rw [accept_suffix r.lazy_star _ none]
        simp
        apply iff_eq_of_eq
        apply fn_arg₃_eq
        ext l u
        split_ifs with h₁
        · rw [accept_suffix r₂ _ none]
          nth_rw 2 [accept_suffix r₂ _ none]
          simp
          apply iff_eq_of_eq
          apply fn_arg₃_eq
          ext l' v
          split_ifs with h₂ h₃
          · rfl
          · absurd h₃
            apply Nat.lt_of_le_of_lt
            exact h₂
            apply Nat.lt_of_le_of_lt
            exact h₁
            exact hl
          · rfl
        · rfl
      · rfl
  | .star r => by
    simp
    rw [accept, accept_deriv_cond r]
    simp
    rw [accept]
    simp_rw [accept_suffix r.star (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
    simp
    apply fn_arg₃_eq
    ext loc t
    split_ifs with hl
    · rw [accept_suffix r.star k none]
      simp
      apply iff_eq_of_eq
      apply fn_arg₃_eq
      ext l u
      split_ifs with h₁ h₂
      · rfl
      · absurd h₂
        apply Nat.lt_of_le_of_lt
        exact h₁
        exact hl
      · rfl
    · rfl
  | lazy_star r => by
    simp
    rw [accept, accept_deriv_cond r]
    simp
    rw [accept]
    simp_rw [accept_suffix r.lazy_star (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
    simp
    apply fn_arg₃_eq
    ext loc t
    split_ifs with hl
    · rw [accept_suffix r.lazy_star k none]
      simp
      apply iff_eq_of_eq
      apply fn_arg₃_eq
      ext l u
      split_ifs with h₁ h₂
      · rfl
      · absurd h₂
        apply Nat.lt_of_le_of_lt
        exact h₁
        exact hl
      · rfl
    · rfl
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_prune (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  r.accept (s₁, s₂) k = (r.prune (s₁, s₂)).accept (s₁, s₂) k :=
  match r with
  | epsilon => by simp only [prune]
  | pred c => by simp only [prune]
  | plus r₁ r₂ => by
    simp only [prune]
    split_ifs with hn
    · simp [accept]
      rw [←accept_prune r₁]
      apply Option.or_of_isSome
      apply accept_nullable
      exact hn
      apply hk
      exact hk
    · simp [accept]
      rw [accept_prune r₁, accept_prune r₂]
      exact hk
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      rw [accept_prune r₂]
      exact hk
    | pred c => simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hn
      · rw [←accept_mul_def, ←accept_prune (r₁₁.mul r₂)]
        rw [Option.or_of_isSome]
        apply accept_nullable
        simp [hn]
        apply hk
        exact hk
      · simp [accept]
        rw [←accept_mul_def, ←accept_mul_def]
        rw [accept_prune (r₁₁.mul r₂), accept_prune (r₁₂.mul r₂)]
        exact hk
        exact hk
    | mul r₁₁ r₁₂ =>
      simp [accept]
      rw [←accept_prune (r₁₁.mul (r₁₂.mul r₂))]
      simp [accept]
      exact hk
    | .star r =>
      simp
      rw [accept, accept]
      rw [accept_suffix r.star _ none]
      nth_rw 2 [accept_suffix r.star _ none]

      have hr₂_prune :
        (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.prune.accept l' k else none) =
        (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' k else none) := by
        ext l t
        split_ifs with hl
        · rw [accept_prune r₂ _ _ k hk]
        · rfl

      rw [hr₂_prune]
    | lazy_star r =>
      simp
      split_ifs with hn
      · rw [accept, accept]
        rw [Option.or_of_isSome]
        rw [accept_prune r₂ _ _ k hk]
        apply accept_nullable
        exact hn
        apply hk
      · rw [accept, accept]
        rw [accept_suffix r.lazy_star _ none]
        nth_rw 2 [accept_suffix r.lazy_star _ none]

        have hr₂_prune :
          (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.prune.accept l' k else none) =
          (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' k else none) := by
          ext l t
          split_ifs with hl
          · rw [accept_prune r₂ _ _ k hk]
          · rfl

        rw [hr₂_prune]
  | .star r => by
    simp
    rw [accept, accept]
    simp
    rw [←accept_prune]
    congr
    funext loc'
    split_ifs with hl
    · rw [accept_prune]
      simp
      sorry
      exact hk
    · rfl
    intro s₃ s₄
    split_ifs
    · apply accept_nullable
      simp
      apply hk
    · apply hk
  | lazy_star r => by
    simp
    rw [accept, accept]
    rw [Option.or_of_isSome]
    apply hk
termination_by (s₂.length, r.size, r.left.size)
decreasing_by
  any_goals decreasing_tactic
  · simp
    apply Prod.Lex.right
    apply Prod.Lex.right'
    omega
    omega
  · apply Prod.Lex.right'
    exact hl
    apply Prod.Lex.left
    simp
  · apply Prod.Lex.right'
    exact hl
    apply Prod.Lex.left
    simp

theorem accept_deriv_none {r : Regex α} {s₁ s₂ : List σ} {k : Loc σ → Option (Loc σ)} (hn : ¬r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = none :=
  match r with
  | epsilon => by simp at hn
  | pred c => by
    simp [accept]
    split_ifs with hc
    · simp [accept, hc]
    · simp [accept, hc]
  | plus r₁ r₂ => by
    intro h
    simp at hn
    simp [accept, hn] at h
    let ⟨h₁, h₂⟩ := h
    apply @accept_deriv_none _ r₁ at h₁
    apply @accept_deriv_none _ r₂ at h₂
    simp [accept]
    exact ⟨h₁, h₂⟩
    simp [hn.right]
    exact hk
    simp [hn.left]
    exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      simp at hn
      apply accept_deriv_none
      simp [hn]
      exact hk
    | pred c =>
      simp
      split_ifs with hc
      · simp [accept, hc]
      · simp [accept, hc]
    | plus r₁₁ r₁₂ =>
      simp
      split_ifs with hn'
      · simp_all
      · simp [accept]
        intro h₁ h₂
        apply @accept_deriv_none _ (r₁₁.mul r₂) at h₁
        apply @accept_deriv_none _ (r₁₂.mul r₂) at h₂
        simp [accept] at h₁ h₂
        exact ⟨h₁, h₂⟩
        simp_all
        exact hk
        simp_all
        exact hk
    | mul r₁₁ r₁₂ =>
      simp
      intro h
      apply @accept_deriv_none _ (r₁₁.mul (r₁₂.mul r₂)) at h
      simp [accept]
      simp [accept] at h
      exact h
      simp_all
      exact hk
    | .star r =>
      intro h
      simp at h hn
      rw [accept, accept] at h
      rw [accept_deriv_cond] at h
      simp at h
      let ⟨h₁, h₂⟩ := h
      clear h
      apply @accept_deriv_none _ r₂ at h₂
      simp_rw [accept_mul_def] at h₁
      rw [accept, accept]
      simp
      refine ⟨?_, h₂⟩
      simp_rw [←accept_prune r₂ _ _ k hk] at h₁
      exact h₁
      simp [hn]
      exact hk
    | lazy_star r =>
      simp
      split_ifs with hn'
      · absurd hn
        simp [hn']
      · intro h
        simp at h hn
        rw [accept, accept] at h
        nth_rw 2 [accept_deriv_cond] at h
        simp at h
        let ⟨h₂, h₁⟩ := h
        clear h
        apply @accept_deriv_none _ r₂ at h₂
        simp_rw [accept_mul_def] at h₁
        rw [accept, accept]
        simp
        refine ⟨h₂, ?_⟩
        simp_rw [←accept_prune r₂ _ _ k hk] at h₁
        exact h₁
        simp [hn]
        exact hk
  | .star r => by simp at hn
  | lazy_star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_none_nullable {r : Regex α} {s₁ s₂ : List σ} {k : Loc σ → Option (Loc σ)} (hn : r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x :: s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = k (s₁, x::s₂) :=
  match r with
  | epsilon => by simp [accept]
  | pred c => by simp at hn
  | plus r₁ r₂ => by
    simp at hn
    simp [accept]
    intro h
    split_ifs at h with hn'
    · apply accept_deriv_none_nullable hn' hk at h
      rw [h]
      rw [Option.or_of_isSome]
      apply hk
    · simp [accept] at h
      let ⟨h₁, h₂⟩ := h
      clear h
      apply accept_deriv_none at h₁
      apply accept_deriv_none_nullable at h₂
      rw [h₁, h₂]
      simp
      exact Or.resolve_left hn hn'
      exact hk
      exact hn'
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      simp at hn
      intro h
      apply accept_deriv_none_nullable at h
      exact h
      exact hn
      exact hk
    | pred c => simp at hn
    | plus r₁₁ r₁₂ =>
      simp [accept]
      simp at hn
      split_ifs with hn'
      · intro h
        apply accept_deriv_none_nullable (by simp [hn']) hk at h
        simp [accept] at h
        rw [h, Option.or_of_isSome]
        apply hk
      · simp_all
        simp [accept]
        intro h₁ h₂
        apply accept_deriv_none (by simp [hn']) hk at h₁
        apply accept_deriv_none_nullable (by simp [hn]) hk at h₂
        simp [accept] at h₁ h₂
        rw [h₁, h₂]
        simp
    | mul r₁₁ r₁₂ =>
      simp [accept]
      intro h
      apply accept_deriv_none_nullable at h
      simp [accept] at h
      exact h
      simp at hn
      simp [hn]
      exact hk
    | .star r =>
      simp
      rw [accept, accept]
      simp
      rw [accept_deriv_cond, accept, accept]
      simp
      intro h₁ h₂
      simp_rw [accept_mul_def, ←accept_prune r₂ _ _ k hk] at h₁
      simp at hn
      apply accept_deriv_none_nullable hn hk at h₂
      rw [h₁, h₂]
      simp
    | lazy_star r =>
      simp at hn
      simp [hn]
      intro h
      apply accept_deriv_none_nullable at h
      rw [accept, accept, h]
      rw [Option.or_of_isSome]
      apply hk
      exact hn
      exact hk
  | .star r => by
    simp
    rw [accept, accept_deriv_cond, accept]
    simp
    intro h
    rw [h]
    simp
  | lazy_star r => by
    simp
    rw [accept, Option.or_of_isSome]
    apply hk
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (loc : Loc σ) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = some loc →
  r.accept (s₁, x::s₂) k = some loc :=
  match r with
  | epsilon => by simp [accept]
  | pred c => by
    simp [accept]
    split_ifs with hc
    · simp [accept, hc]
    · simp [accept]
  | plus r₁ r₂ => by
    simp [accept]
    intro h
    split_ifs at h with hn
    · apply accept_deriv r₁ at h
      exact Or.inl h
      exact hk
    · simp [Regex.deriv, accept] at h
      cases h with
      | inl h =>
        apply accept_deriv r₁ at h
        exact Or.inl h
        exact hk
      | inr h =>
        let ⟨h₁, h₂⟩ := h
        apply accept_deriv r₂ at h₂
        refine Or.inr ⟨?_, h₂⟩
        apply accept_deriv_none
        exact hn
        exact hk
        exact h₁
        exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      apply accept_deriv r₂
      exact hk
    | pred c =>
      simp [accept]
      split_ifs with hc
      · simp [accept, hc]
      · simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hn
      · intro h
        apply accept_deriv (r₁₁.mul r₂) at h
        simp [accept] at h
        exact Or.inl h
        exact hk
      · simp [accept]
        intro h
        cases h with
        | inl h =>
          apply accept_deriv (r₁₁.mul r₂) at h
          simp [accept] at h
          exact Or.inl h
          exact hk
        | inr h =>
          let ⟨h₁, h₂⟩ := h
          clear h
          apply accept_deriv (r₁₂.mul r₂) at h₂
          simp [accept] at h₂
          refine Or.inr ⟨?_, ?_⟩
          · have h := accept_deriv_none (by simp [hn]) hk h₁
            simp [accept] at h
            exact h
          · exact h₂
          exact hk
    | mul r₁₁ r₁₂ =>
      simp [accept]
      intro h
      apply accept_deriv (r₁₁.mul (r₁₂.mul r₂)) at h
      simp [accept] at h
      exact h
      exact hk
    | .star r =>
      simp
      rw [accept, accept, accept_deriv_cond]
      intro h
      simp at h
      simp_rw [accept_mul_def] at h
      simp_rw [←accept_prune r₂ _ _ k hk] at h
      cases h with
      | inl h =>
        rw [accept, accept]
        simp
        exact Or.inl h
      | inr h =>
        let ⟨h₁, h₂⟩ := h
        clear h
        apply accept_deriv r₂ _ _ k loc hk at h₂
        rw [accept, accept]
        simp
        exact Or.inr ⟨h₁, h₂⟩
    | lazy_star r =>
      simp
      split_ifs with hn
      · intro h
        apply accept_deriv r₂ _ _ k loc hk at h
        rw [accept, accept, h]
        simp
      · simp
        rw [accept, accept]
        nth_rw 2 [accept_deriv_cond]
        intro h
        simp at h
        simp_rw [accept_mul_def] at h
        simp_rw [←accept_prune r₂ _ _ k hk] at h
        rw [accept, accept]
        simp
        cases h with
        | inl h =>
          apply accept_deriv r₂ _ _ k loc hk at h
          exact Or.inl h
        | inr h =>
          let ⟨h₁, h₂⟩ := h
          clear h
          apply accept_deriv_none hn hk at h₁
          exact Or.inr ⟨h₁, h₂⟩
  | .star r => by
    simp
    rw [accept, accept_deriv_cond, accept]
    simp
    intro h
    exact Or.inl h
  | lazy_star r => by simp
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_not_nullable (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) (hn : ¬r.nullable) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) k :=
  match r with
  | epsilon => by simp at hn
  | pred c => by
    simp [accept]
    split_ifs with hc
    · simp [accept]
    · simp [accept]
  | plus r₁ r₂ => by
    simp at hn
    simp [accept]
    split_ifs with hn'
    · absurd hn'
      simp [hn]
    · simp [accept]
      rw [accept_deriv_not_nullable, accept_deriv_not_nullable]
      exact hk
      simp [hn]
      exact hk
      simp [hn]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp at hn
      simp [accept]
      rw [accept_deriv_not_nullable]
      exact hk
      simp [hn]
    | pred c =>
      simp [accept]
      split_ifs
      · rfl
      · simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hn'
      · simp_all
      · simp [accept]
        rw [accept_deriv_not_nullable, accept_deriv_not_nullable]
        simp [accept]
        exact hk
        simp_all
        exact hk
        simp_all
    | mul r₁₁ r₁₂ =>
      simp [accept]
      rw [accept_deriv_not_nullable]
      simp [accept]
      exact hk
      simp at *
      tauto
    | .star r =>
      simp at hn
      simp
      rw [accept, accept, accept_deriv_not_nullable r₂]
      rw [accept_deriv_cond, accept, accept]
      simp_rw [accept_mul_def, ←accept_prune r₂ _ _ k hk]
      simp
      exact hk
      simp [hn]
    | lazy_star r =>
      simp at *
      split_ifs with hn'
      · absurd hn
        simp [hn']
      · simp
        rw [accept, accept, accept_deriv_not_nullable r₂]
        rw [accept_deriv_cond, accept, accept]
        simp_rw [accept_mul_def, ←accept_prune r₂ _ _ k hk]
        simp
        exact hk
        exact hn'
  | .star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem matchEnd_accept (r : Regex α) (s₁ s₂ : List σ) :
  r.matchEnd (s₁, s₂) = r.accept (s₁, s₂) some := by
  induction s₂ generalizing r s₁ with
  | nil =>
    simp [Regex.matchEnd]
    split_ifs with hn
    · rw [accept_nil_nullable hn]
    · rw [accept_nil_not_nullable hn]
  | cons x xs ih =>
    simp [Regex.matchEnd]
    cases k : ((r.prune.deriv x).matchEnd (x :: s₁, xs)) with
    | none =>
      simp
      rw [ih] at k
      split_ifs with hn
      · apply accept_deriv_none_nullable at k
        rw [k]
        exact hn
        simp
      · apply accept_deriv_none at k
        rw [k]
        exact hn
        simp
    | some v =>
      simp
      rw [ih] at k
      apply accept_deriv at k
      rw [k]
      simp

theorem rmatch_gmatch (r : Regex α) (s : List σ) :
  r.rmatch s = r.gmatch s := by
  rw [Regex.rmatch, Regex.gmatch]
  apply matchEnd_accept
