import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

open Regex

theorem accept_deriv_cond (r : Regex α) (s₁ s₂ : List α) (x : α) (k : Loc α → Option (Loc α)) :
  (r.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) (fun l' ↦ if l'.right.length < (x::s₂).length then k l' else none) :=
  match r with
  | zero => by simp [accept]
  | one => by simp [accept]
  | char c => by
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
    | zero => simp [accept]
    | one =>
      simp [accept]
      rw [accept_deriv_cond]
      simp
    | char c =>
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
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_prune (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  r.accept (s₁, s₂) k = r.prune.accept (s₁, s₂) k :=
  match r with
  | zero => by simp only [prune]
  | one => by simp only [prune]
  | char c => by simp only [prune]
  | plus r₁ r₂ => by
    simp only [prune]
    split_ifs with hn hn'
    · simp [accept]
      rw [accept_prune r₁, prune_highNullable hn]
      simp [accept]
      apply Option.or_of_isSome
      apply hk
      exact hk
    · simp [accept]
      rw [←accept_prune r₁]
      apply Option.or_of_isSome
      apply accept_nullable
      exact hn'
      apply hk
      exact hk
    · simp [accept]
      rw [accept_prune r₁, accept_prune r₂]
      exact hk
      exact hk
  | mul r₁ r₂ => by
    rw [prune.eq_def]
    simp
    split_ifs with hn
    · simp [accept]
      rw [accept_prune r₁, prune_highNullable hn.left, accept]
      rw [accept_prune r₂, prune_highNullable hn.right, accept]
      exact hk
      intro s₃ s₄
      apply accept_nullable
      exact highNullable_nullable hn.right
      apply hk
    · match r₁ with
      | zero => simp [accept]
      | one =>
        simp [accept]
        rw [accept_prune r₂]
        exact hk
      | char c => simp [accept]
      | plus r₁₁ r₁₂ =>
        simp
        split_ifs with hn₁ hn₂
        · absurd hn
          simp
          exact hn₁
        · simp [accept]
          rw [←accept_mul_def, ←accept_prune (r₁₁.mul r₂)]
          apply Option.or_of_isSome
          apply accept_nullable
          simp
          exact hn₂
          apply hk
          exact hk
        · simp [accept]
          rw [←accept_mul_def, ←accept_mul_def]
          rw [accept_prune (r₁₁.mul r₂), accept_prune (r₁₂.mul r₂)]
          exact hk
          exact hk
      | mul r₁₁ r₁₂ =>
        simp
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
  | .star r => by
    simp
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

theorem accept_deriv_none {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : ¬r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = none :=
  match r with
  | zero => by simp [accept]
  | one => by simp at hn
  | char c => by
    simp [accept]
    split_ifs with hc
    · simp [accept, hc]
    · simp [accept, hc]
  | plus r₁ r₂ => by
    intro h
    simp at hn
    have hn' : ¬r₁.highNullable := by
      intro hn'
      absurd hn.left
      simp
      exact highNullable_nullable hn'
    simp [hn, hn'] at h
    simp [accept] at h
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
    intro h
    rw [prune.eq_def] at h
    simp at h
    split_ifs at h with hn'
    · absurd hn
      simp
      exact ⟨highNullable_nullable hn'.left, highNullable_nullable hn'.right⟩
    · match r₁ with
      | zero => simp [accept]
      | one =>
        simp at h
        simp [accept]
        apply @accept_deriv_none _ r₂
        simp at hn
        simp [hn]
        exact hk
        exact h
      | char c =>
        simp at h
        split_ifs at h with hc
        · simp [accept, hc]
          exact h
        · simp [accept, hc]
      | plus r₁₁ r₁₂ =>
        simp at h
        split_ifs at h with hn
        · simp_all
        · simp_all
        · simp [accept] at h
          let ⟨h₁, h₂⟩ := h
          simp [accept]
          apply @accept_deriv_none _ (r₁₁.mul r₂) at h₁
          apply @accept_deriv_none _ (r₁₂.mul r₂) at h₂
          simp [accept] at h₁ h₂
          exact ⟨h₁, h₂⟩
          simp_all
          exact hk
          simp_all
          exact hk
      | mul r₁₁ r₁₂ =>
        simp at h
        apply @accept_deriv_none _ (r₁₁.mul (r₁₂.mul r₂)) at h
        simp [accept]
        simp [accept] at h
        exact h
        simp_all
        exact hk
      | .star r =>
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
  | .star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_none_nullable {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x :: s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = k (s₁, x::s₂) :=
  match r with
  | zero => by simp at hn
  | one => by simp [accept]
  | char c => by simp at hn
  | plus r₁ r₂ => by
    simp at hn
    simp [accept]
    intro h
    split_ifs at h with hr₁ hr₂
    · rw [accept_highNullable]
      rw [Option.or_of_isSome]
      apply hk
      exact hr₁
      apply hk
    · apply accept_deriv_none_nullable hr₂ hk at h
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
      exact Or.resolve_left hn hr₂
      exact hk
      exact hr₂
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp at hn
    | one =>
      simp [accept]
      simp at hn
      split_ifs with hr
      · simp [accept]
        rw [accept_highNullable]
        exact hr
        apply hk
      · intro h
        apply accept_deriv_none_nullable at h
        exact h
        exact hn
        exact hk
    | char c => simp at hn
    | plus r₁₁ r₁₂ =>
      simp [accept]
      simp at hn
      split_ifs with hr₁ hr₂
      · simp [accept]
        rw [accept_highNullable hr₁.left, accept_highNullable hr₁.right]
        rw [Option.or_of_isSome]
        apply hk
        apply hk
        apply accept_nullable
        exact hn.right
        apply hk
      · intro h
        apply accept_deriv_none_nullable (by simp [hr₂]) hk at h
        simp [accept] at h
        rw [h, Option.or_of_isSome]
        apply hk
      · simp_all
        simp [accept]
        intro h₁ h₂
        apply accept_deriv_none (by simp [hr₂]) hk at h₁
        apply accept_deriv_none_nullable (by simp [hn]) hk at h₂
        simp [accept] at h₁ h₂
        rw [h₁, h₂]
        simp
    | mul r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hr
      · simp [accept]
        rw [accept_highNullable hr.left.left, accept_highNullable hr.left.right, accept_highNullable hr.right]
        apply hk
        apply accept_nullable
        exact highNullable_nullable hr.right
        apply hk
        apply accept_nullable
        exact highNullable_nullable hr.left.right
        apply accept_nullable
        exact highNullable_nullable hr.right
        apply hk
      · intro h
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
  | .star r => by
    simp
    rw [accept, accept_deriv_cond, accept]
    simp
    intro h
    rw [h]
    simp
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = some loc →
  r.accept (s₁, x::s₂) k = some loc :=
  match r with
  | zero => by simp [accept]
  | one => by simp [accept]
  | char c => by
    simp [accept]
    split_ifs with hc
    · simp [accept, hc]
    · simp [accept]
  | plus r₁ r₂ => by
    simp [accept]
    intro h
    split_ifs at h with hn hn'
    · simp [accept] at h
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
        exact hn'
        exact hk
        exact h₁
        exact hk
  | mul r₁ r₂ => by
    rw [Regex.prune.eq_def]
    simp
    split_ifs with hn
    · simp [accept]
    · match r₁ with
      | zero => simp [accept]
      | one =>
        simp [accept]
        apply accept_deriv r₂
        exact hk
      | char c =>
        simp [accept]
        split_ifs with hc
        · simp [accept, hc]
        · simp [accept]
      | plus r₁₁ r₁₂ =>
        intro h
        simp at h
        split_ifs at h with hn hn'
        · simp [accept] at h
        · simp [accept]
          apply accept_deriv (r₁₁.mul r₂) at h
          simp [accept] at h
          exact Or.inl h
          exact hk
        · simp [Regex.deriv] at h
          simp [accept] at h
          cases h with
          | inl h =>
            simp [accept]
            apply accept_deriv (r₁₁.mul r₂) at h
            simp [accept] at h
            exact Or.inl h
            exact hk
          | inr h =>
            let ⟨h₁, h₂⟩ := h
            simp [accept]
            apply accept_deriv (r₁₂.mul r₂) at h₂
            simp [accept] at h₂
            refine Or.inr ⟨?_, ?_⟩
            · have h := accept_deriv_none (by simp [hn']) hk h₁
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
  | .star r => by
    simp
    rw [accept, accept_deriv_cond, accept]
    simp
    intro h
    exact Or.inl h
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_not_nullable (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) (hn : ¬r.nullable) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) k :=
  match r with
  | zero => by simp [accept]
  | one => by simp at hn
  | char c => by
    simp [accept]
    split_ifs with hc
    · simp [accept]
    · simp [accept]
  | plus r₁ r₂ => by
    simp at hn
    simp [accept]
    split_ifs with hr₁ hr₂
    · absurd (highNullable_nullable hr₁)
      simp [hn]
    · absurd hr₂
      simp [hn]
    · simp [accept]
      rw [accept_deriv_not_nullable, accept_deriv_not_nullable]
      exact hk
      simp [hn]
      exact hk
      simp [hn]
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp at hn
      simp [accept]
      split_ifs with hr
      · absurd (highNullable_nullable hr)
        simp [hn]
      · rw [accept_deriv_not_nullable]
        exact hk
        simp [hn]
    | char c =>
      simp [accept]
      split_ifs
      · rfl
      · simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hr₁ hr₂
      · simp at hn
        have hr₁₁ := highNullable_nullable hr₁.left
        simp [hr₁₁] at hn
        absurd (highNullable_nullable hr₁.right)
        simp [hn]
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
      split_ifs with hr
      · absurd hn
        simp
        exact ⟨⟨highNullable_nullable hr.left.left, highNullable_nullable hr.left.right⟩, highNullable_nullable hr.right⟩
      · rw [accept_deriv_not_nullable]
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
  | .star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem matchEnd_accept (r : Regex α) (s₁ s₂ : List α) :
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

theorem rmatch_gmatch (r : Regex α) (s : List α) :
  r.rmatch s = r.gmatch s := by
  rw [Regex.rmatch, Regex.gmatch]
  apply matchEnd_accept
