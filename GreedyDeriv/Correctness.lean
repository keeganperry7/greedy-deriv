import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α σ : Type u} [EffectiveBooleanAlgebra α σ]

open Regex

theorem accept_deriv_cond (r : Regex α) (s₁ s₂ : List σ) (x : σ) (k : Loc σ → Option (Loc σ)) :
  (r.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) (fun l' ↦ if l'.right.length < (x::s₂).length then k l' else none) :=
  match r with
  | epsilon => by simp [accept]
  | pred c => by
    simp [accept]
    split_ifs
    · rw [accept]
    · apply accept_bot
  | plus r₁ r₂ => by
    simp [accept]
    rw [accept_deriv_cond, accept_deriv_cond]
    simp only [Loc.right, List.length_cons]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      rw [accept_deriv_cond]
      simp only [Loc.right, List.length_cons]
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
    | .star r false =>
      simp
      rw [accept, accept, accept, accept]
      rw [accept_deriv_cond r]
      rw [accept_deriv_cond r₂]
      simp only [Loc.right, List.length_cons]
      simp_rw [accept_suffix (r.star false) (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
      congr
      funext loc
      split_ifs with hl
      · rw [accept_mul_def]
        rw [accept_suffix (r.star false) _ none]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ none]
          nth_rw 2 [accept_suffix r₂ _ none]
          simp only [Prod.mk.eta, Loc.right]
          congr
          funext l'
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
    | .star r true =>
      simp
      rw [accept, accept, accept, accept]
      rw [accept_deriv_cond r]
      rw [accept_deriv_cond r₂]
      simp only [Loc.right, List.length_cons]
      simp_rw [accept_suffix (r.star true) (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
      simp only [Prod.mk.eta, Loc.right]
      congr
      funext loc
      split_ifs with hl
      · rw [accept_mul_def]
        rw [accept_suffix (r.star true) _ none]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ none]
          nth_rw 2 [accept_suffix r₂ _ none]
          simp only [Prod.mk.eta, Loc.right]
          congr
          funext l'
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
  | .star r  false => by
    simp
    rw [accept, accept_deriv_cond r]
    simp only [Loc.right, List.length_cons]
    rw [accept]
    simp_rw [accept_suffix (r.star false) (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
    simp
    congr
    funext loc
    split_ifs with hl
    · rw [accept_suffix (r.star false) k none]
      simp only [Prod.mk.eta, Loc.right]
      congr
      funext l
      split_ifs with h₁ h₂
      · rfl
      · absurd h₂
        apply Nat.lt_of_le_of_lt
        exact h₁
        exact hl
      · rfl
    · rfl
  | .star r true => by
    simp
    rw [accept, accept_deriv_cond r]
    simp only [Loc.right, List.length_cons]
    rw [accept]
    simp_rw [accept_suffix (r.star true) (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
    simp
    congr
    funext loc
    split_ifs with hl
    · rw [accept_suffix (r.star true) k none]
      simp only [Prod.mk.eta, Loc.right]
      congr
      funext l
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
  r.accept (s₁, s₂) k = r.prune.accept (s₁, s₂) k :=
  match r with
  | epsilon => by simp only [prune]
  | pred c => by simp only [prune]
  | plus r₁ r₂ => by
    simp only [prune]
    split_ifs with hn
    · rw [accept]
      rw [←accept_prune r₁]
      apply Option.or_of_isSome
      apply accept_nullable
      exact hn
      apply hk
      exact hk
    · rw [accept, accept]
      rw [accept_prune r₁, accept_prune r₂]
      exact hk
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp only [accept, prune]
      rw [accept_prune r₂]
      exact hk
    | pred c => simp only [accept, prune]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hn
      · rw [←accept_mul_def, ←accept_prune (r₁₁.mul r₂)]
        rw [Option.or_of_isSome]
        apply accept_nullable
        simp [hn]
        apply hk
        exact hk
      · rw [accept]
        rw [←accept_mul_def, ←accept_mul_def]
        rw [accept_prune (r₁₁.mul r₂), accept_prune (r₁₂.mul r₂)]
        exact hk
        exact hk
    | mul r₁₁ r₁₂ =>
      simp only [accept, prune]
      rw [←accept_prune (r₁₁.mul (r₁₂.mul r₂))]
      simp only [accept]
      exact hk
    | .star r false =>
      simp
      rw [accept, accept]
      rw [accept_suffix (r.star false) _ none]
      nth_rw 2 [accept_suffix (r.star false) _ none]

      have hr₂_prune :
        (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.prune.accept l' k else none) =
        (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' k else none) := by
        funext l
        split_ifs with hl
        · rw [accept_prune r₂ _ _ k hk]
        · rfl

      rw [hr₂_prune]
    | .star r true =>
      rw [prune]
      split_ifs with hn
      · rw [accept, accept]
        rw [Option.or_of_isSome]
        rw [accept_prune r₂ _ _ k hk]
        apply accept_nullable
        exact hn
        apply hk
      · rw [accept, accept]
        rw [accept_suffix (r.star true) _ none]
        nth_rw 2 [accept_suffix (r.star true) _ none]

        have hr₂_prune :
          (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.prune.accept l' k else none) =
          (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' k else none) := by
          funext l
          split_ifs with hl
          · rw [accept_prune r₂ _ _ k hk]
          · rfl

        rw [hr₂_prune]
  | .star r false => by
    rw [prune]
  | .star r true => by
    rw [prune]
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

theorem accept_deriv_none' {r : Regex α} {x : σ} {s₁ s₂ : List σ} {k : Loc σ → Option (Loc σ)} (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = if r.nullable then k (s₁, x::s₂) else none :=
  match r with
  | epsilon => by simp [accept]
  | pred c => by
    simp [accept]
    split_ifs with hc
    · simp [accept, hc]
    · simp [accept, hc]
  | plus r₁ r₂ => by
    simp [accept]
    intro h
    split_ifs at h with hn₁
    · apply accept_deriv_none' at h
      simp [hn₁] at h
      simp [hn₁]
      rw [h, Option.or_of_isSome]
      apply hk
      exact hk
    · simp [accept] at h
      rcases h with ⟨h₁, h₂⟩
      apply accept_deriv_none' at h₁
      apply accept_deriv_none' at h₂
      simp [hn₁] at h₁
      simp [h₁, hn₁]
      exact h₂
      exact hk
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      apply accept_deriv_none'
      exact hk
    | pred c =>
      simp [accept]
      split_ifs with hc
      · simp [hc]
      · simp [hc]
    | plus r₁₁ r₁₂ =>
      sorry
    | mul r₁₁ r₁₂ =>
      rw [prune]
      intro h
      apply accept_deriv_none' at h
      simp [accept]
      simp [accept] at h
      simp_rw [h, and_assoc]
      exact hk
    | .star r false =>
      intro h
      simp at h
      rw [accept, accept] at h
      rw [accept_deriv_cond] at h
      simp at h
      rcases h with ⟨h₁, h₂⟩
      apply accept_deriv_none' at h₂
      simp_rw [accept_mul_def] at h₁
      rw [accept, accept]
      simp
      simp_rw [←accept_prune r₂ _ _ k hk] at h₁
      rw [h₁, h₂, Option.none_or]
      exact hk
    | .star r true =>
      simp
      intro h
      split_ifs at h with hn
      · apply accept_deriv_none' at h
        rw [accept, accept, h, Option.or_of_isSome]
        simp [hn]
        apply hk
        exact hk
      · rw [Regex.deriv, accept, accept] at h
        simp at h
        rcases h with ⟨h₁, h₂⟩
        apply accept_deriv_none' at h₁
        rw [accept_deriv_cond] at h₂
        simp_rw [accept_mul_def] at h₂
        simp_rw [←accept_prune r₂ _ _ k hk] at h₂
        simp at h₂
        rw [accept, accept, h₁]
        simp [hn, h₂]
        exact hk
  | .star r false => by
    rw [prune, Regex.deriv]
    rw [accept, accept_deriv_cond, accept]
    rw [Loc.right, List.length_cons]
    intro h
    rw [h]
    exact Option.none_or
  | .star r true => by
    simp
    rw [accept, Option.or_of_isSome]
    apply hk
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

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
    rcases h with ⟨h₁, h₂⟩
    apply accept_deriv_none at h₁
    apply accept_deriv_none at h₂
    rw [accept, Option.or_eq_none]
    exact ⟨h₁, h₂⟩
    simp [hn.right]
    exact hk
    simp [hn.left]
    exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      rw [prune, accept, accept]
      simp at hn
      apply accept_deriv_none
      simp [hn]
      exact hk
    | pred c =>
      rw [prune, Regex.deriv]
      split_ifs with hc
      · simp [accept, hc]
      · simp [accept, hc]
    | plus r₁₁ r₁₂ =>
      simp
      split_ifs with hn'
      · simp_all
      · simp [accept]
        intro h₁ h₂
        apply accept_deriv_none at h₁
        apply accept_deriv_none at h₂
        rw [accept] at h₁ h₂
        exact ⟨h₁, h₂⟩
        simp_all
        exact hk
        simp_all
        exact hk
    | mul r₁₁ r₁₂ =>
      rw [prune]
      intro h
      apply accept_deriv_none at h
      rw [accept, accept]
      simp only [accept] at h
      exact h
      simp_all
      exact hk
    | .star r false =>
      intro h
      simp at h hn
      rw [accept, accept] at h
      rw [accept_deriv_cond] at h
      simp at h
      rcases h with ⟨h₁, h₂⟩
      apply accept_deriv_none at h₂
      simp_rw [accept_mul_def] at h₁
      rw [accept, accept]
      simp
      refine ⟨?_, h₂⟩
      simp_rw [←accept_prune r₂ _ _ k hk] at h₁
      exact h₁
      simp [hn]
      exact hk
    | .star r true =>
      rw [prune]
      split_ifs with hn'
      · absurd hn
        simp [hn']
      · intro h
        simp at h hn
        rw [accept, accept] at h
        nth_rw 2 [accept_deriv_cond] at h
        simp at h
        rcases h with ⟨h₂, h₁⟩
        apply accept_deriv_none at h₂
        simp_rw [accept_mul_def] at h₁
        rw [accept, accept]
        simp
        refine ⟨h₂, ?_⟩
        simp_rw [←accept_prune r₂ _ _ k hk] at h₁
        exact h₁
        simp [hn]
        exact hk
  | .star r _ => by simp at hn
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
    rw [prune, accept]
    intro h
    split_ifs at h with hn'
    · apply accept_deriv_none_nullable hn' hk at h
      rw [h, Option.or_of_isSome]
      apply hk
    · simp [accept] at h
      rcases h with ⟨h₁, h₂⟩
      apply accept_deriv_none at h₁
      apply accept_deriv_none_nullable at h₂
      rw [h₁, h₂]
      exact Option.none_or
      exact Or.resolve_left hn hn'
      exact hk
      exact hn'
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp only [prune, accept]
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
        rw [accept] at h
        rw [h, Option.or_of_isSome]
        apply hk
      · simp_all
        simp [accept]
        intro h₁ h₂
        apply accept_deriv_none (by simp [hn']) hk at h₁
        apply accept_deriv_none_nullable (by simp [hn]) hk at h₂
        rw [accept] at h₁ h₂
        rw [h₁, h₂]
        exact Option.none_or
    | mul r₁₁ r₁₂ =>
      simp only [prune, accept]
      intro h
      apply accept_deriv_none_nullable at h
      simp only [accept] at h
      exact h
      simp at hn
      simp [hn]
      exact hk
    | .star r false =>
      rw [prune, Regex.deriv]
      rw [accept, accept]
      rw [Option.or_eq_none, and_imp]
      rw [accept_deriv_cond, accept, accept]
      rw [Loc.right, List.length_cons]
      intro h₁ h₂
      simp_rw [accept_mul_def, ←accept_prune r₂ _ _ k hk] at h₁
      simp at hn
      apply accept_deriv_none_nullable hn hk at h₂
      rw [h₁, h₂]
      exact Option.none_or
    | .star r true =>
      simp at hn
      simp [hn]
      intro h
      apply accept_deriv_none_nullable at h
      rw [accept, accept, h]
      rw [Option.or_of_isSome]
      apply hk
      exact hn
      exact hk
  | .star r false => by
    rw [prune, Regex.deriv]
    rw [accept, accept_deriv_cond, accept]
    rw [Loc.right, List.length_cons]
    intro h
    rw [h]
    exact Option.none_or
  | .star r true => by
    simp only [prune, Regex.deriv, accept_bot, forall_const]
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
    rw [prune, accept, Option.or_eq_some]
    intro h
    split_ifs at h with hn
    · apply accept_deriv r₁ at h
      exact Or.inl h
      exact hk
    · rw [Regex.deriv, accept, Option.or_eq_some] at h
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
      rw [prune, accept, accept]
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
        rw [accept] at h
        exact Or.inl h
        exact hk
      · rw [Regex.deriv, accept, Option.or_eq_some]
        intro h
        cases h with
        | inl h =>
          apply accept_deriv (r₁₁.mul r₂) at h
          rw [accept] at h
          exact Or.inl h
          exact hk
        | inr h =>
          rcases h with ⟨h₁, h₂⟩
          apply accept_deriv (r₁₂.mul r₂) at h₂
          rw [accept] at h₂
          refine Or.inr ⟨?_, h₂⟩
          · apply accept_deriv_none (by simp [hn]) hk at h₁
            rw [accept] at h₁
            exact h₁
          exact hk
    | mul r₁₁ r₁₂ =>
      simp only [prune, accept]
      intro h
      apply accept_deriv (r₁₁.mul (r₁₂.mul r₂)) at h
      simp only [accept] at h
      exact h
      exact hk
    | .star r false =>
      rw [prune, Regex.deriv]
      rw [accept, accept, accept_deriv_cond]
      intro h
      simp at h
      simp_rw [accept_mul_def] at h
      simp_rw [←accept_prune r₂ _ _ k hk] at h
      cases h with
      | inl h =>
        rw [accept, accept]
        rw [Loc.right, List.length_cons, Option.or_eq_some]
        exact Or.inl h
      | inr h =>
        rcases h with ⟨h₁, h₂⟩
        apply accept_deriv r₂ _ _ k loc hk at h₂
        rw [accept, accept]
        rw [Loc.right, List.length_cons, Option.or_eq_some]
        exact Or.inr ⟨h₁, h₂⟩
    | .star r true =>
      rw [prune]
      split_ifs with hn
      · intro h
        apply accept_deriv r₂ _ _ k loc hk at h
        rw [accept, accept, h]
        rw [Loc.right, List.length_cons, Option.some_or]
      · rw [Regex.deriv, accept, accept]
        nth_rw 2 [accept_deriv_cond]
        intro h
        simp_rw [Loc.right, List.length_cons, Option.or_eq_some] at h
        simp_rw [accept_mul_def] at h
        simp_rw [←accept_prune r₂ _ _ k hk] at h
        rw [accept, accept]
        rw [Loc.right, List.length_cons, Option.or_eq_some]
        cases h with
        | inl h =>
          apply accept_deriv r₂ _ _ k loc hk at h
          exact Or.inl h
        | inr h =>
          rcases h with ⟨h₁, h₂⟩
          apply accept_deriv_none hn hk at h₁
          exact Or.inr ⟨h₁, h₂⟩
  | .star r false => by
    rw [prune, Regex.deriv]
    rw [accept, accept_deriv_cond, accept]
    rw [Loc.right, List.length_cons, Option.or_eq_some]
    intro h
    exact Or.inl h
  | .star r true => by simp
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_not_nullable (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) (hn : ¬r.nullable) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) k :=
  match r with
  | pred c => by
    rw [prune, Regex.deriv, accept]
    split_ifs with hc
    · rw [accept]
    · apply accept_bot
  | plus r₁ r₂ => by
    simp at hn
    rw [prune, accept]
    split_ifs with hn'
    · absurd hn'
      simp [hn]
    · rw [Regex.deriv, accept]
      rw [accept_deriv_not_nullable, accept_deriv_not_nullable]
      exact hk
      simp [hn]
      exact hk
      simp [hn]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp at hn
      rw [prune, accept, accept]
      rw [accept_deriv_not_nullable]
      exact hk
      simp [hn]
    | pred c =>
      simp only [prune, Regex.deriv, accept]
      split_ifs
      · rfl
      · apply accept_bot
    | plus r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hn'
      · simp_all
      · rw [Regex.deriv, accept]
        rw [accept_deriv_not_nullable, accept_deriv_not_nullable]
        rw [accept, accept]
        exact hk
        simp_all
        exact hk
        simp_all
    | mul r₁₁ r₁₂ =>
      rw [prune, accept]
      rw [accept_deriv_not_nullable]
      simp only [accept]
      exact hk
      simp at *
      tauto
    | .star r false =>
      simp at hn
      rw [prune, Regex.deriv]
      rw [accept, accept, accept_deriv_not_nullable r₂]
      rw [accept_deriv_cond, accept, accept]
      simp_rw [accept_mul_def, ←accept_prune r₂ _ _ k hk]
      rw [Loc.right, List.length_cons]
      exact hk
      simp [hn]
    | .star r true =>
      simp at *
      split_ifs with hn'
      · absurd hn
        simp [hn']
      · rw [Regex.deriv, accept, accept]
        rw [accept_deriv_not_nullable r₂]
        rw [accept_deriv_cond, accept, accept]
        simp_rw [accept_mul_def, ←accept_prune r₂ _ _ k hk]
        rw [Loc.right, List.length_cons]
        exact hk
        exact hn'
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem matchEnd_accept (r : Regex α) (l : Loc σ) :
  r.matchEnd l = r.accept l some := by
  match l with
  | ⟨u, []⟩ =>
    rw [Regex.matchEnd, accept_nil]
  | ⟨u, c::v⟩ =>
    rw [Regex.matchEnd]
    cases k : ((r.prune.deriv c).matchEnd (c :: u, v)) with
    | none =>
      simp only
      rw [matchEnd_accept] at k
      split_ifs with hn
      · apply accept_deriv_none_nullable at k
        rw [k]
        exact hn
        simp only [Option.isSome_some, implies_true]
      · apply accept_deriv_none at k
        rw [k]
        exact hn
        simp only [Option.isSome_some, implies_true]
    | some v =>
      simp only
      rw [matchEnd_accept] at k
      apply accept_deriv at k
      rw [k]
      simp only [Option.isSome_some, implies_true]
termination_by l.right

theorem rmatch_gmatch (r : Regex α) (s : List σ) :
  r.rmatch s = r.gmatch s := by
  rw [Regex.rmatch, Regex.gmatch]
  apply matchEnd_accept
