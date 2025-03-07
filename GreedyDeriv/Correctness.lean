import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α σ : Type u} [EffectiveBooleanAlgebra α σ]

open Regex

theorem accept''_deriv_cond (r : Regex α) (s₁ s₂ : List σ) (x : σ) (k : Loc σ → Option (Loc σ))
  (f : Option (Loc σ) → Option (Loc σ) → Option (Loc σ)) (hf₁ : ∀ x, f x none = x) (hf₂ : ∀ x, f none x = x) :
  (r.deriv x).accept'' (x::s₁, s₂) k f = r.accept'' (s₁, x::s₂) (fun l' ↦ if l'.right.length < (x::s₂).length then k l' else none) f :=
  match r with
  | epsilon => by simp [accept'']
  | pred c => by
    simp [accept'']
    split_ifs
    · rw [accept'']
    · apply accept''_bot
  | plus r₁ r₂ => by
    simp [accept'']
    rw [accept''_deriv_cond, accept''_deriv_cond]
    simp only [Loc.right, List.length_cons]
    exact hf₁
    exact hf₂
    exact hf₁
    exact hf₂
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept'']
      rw [accept''_deriv_cond]
      simp only [Loc.right, List.length_cons]
      exact hf₁
      exact hf₂
    | pred c =>
      simp [accept'']
      split_ifs with hc
      · simp_rw [Nat.lt_add_one_iff]
        rw [accept''_suffix r₂ _ _ none]
        rfl
      · simp
    | plus r₁₁ r₁₂ =>
      simp [accept'']
      rw [accept''_deriv_cond (r₁₁.mul r₂)]
      rw [accept''_deriv_cond (r₁₂.mul r₂)]
      simp [accept'']
      exact hf₁
      exact hf₂
      exact hf₁
      exact hf₂
    | mul r₁₁ r₁₂ =>
      simp [accept'']
      rw [accept''_deriv_cond (r₁₁.mul (r₁₂.mul r₂))]
      simp [accept'']
      exact hf₁
      exact hf₂
    | .star r false =>
      simp
      rw [accept'', accept'', accept'', accept'']
      rw [accept''_deriv_cond r]
      rw [accept''_deriv_cond r₂]
      simp only [Loc.right, List.length_cons]
      simp_rw [accept''_suffix (r.star false) (fun loc' ↦ r₂.accept'' loc' (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) f) f none]
      congr
      funext loc
      split_ifs with hl
      · rw [accept''_mul_def]
        rw [accept''_suffix (r.star false) _ _ none]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept''_suffix r₂ _ _ none]
          nth_rw 2 [accept''_suffix r₂ _ _ none]
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
      exact hf₁
      exact hf₂
      exact hf₁
      exact hf₂
    | .star r true =>
      simp
      rw [accept'', accept'', accept'', accept'']
      rw [accept''_deriv_cond r]
      rw [accept''_deriv_cond r₂]
      simp only [Loc.right, List.length_cons]
      simp_rw [accept''_suffix (r.star true) (fun loc' ↦ r₂.accept'' loc' (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) f) f none]
      simp only [Prod.mk.eta, Loc.right]
      congr
      funext loc
      split_ifs with hl
      · rw [accept''_mul_def]
        rw [accept''_suffix (r.star true) _ _ none]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept''_suffix r₂ _ _ none]
          nth_rw 2 [accept''_suffix r₂ _ _ none]
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
      exact hf₁
      exact hf₂
      exact hf₁
      exact hf₂
  | .star r  false => by
    simp
    rw [accept'', accept''_deriv_cond r]
    simp only [Loc.right, List.length_cons]
    rw [accept'']
    simp_rw [accept''_suffix (r.star false) (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) f none]
    simp [hf₁]
    congr
    funext loc
    split_ifs with hl
    · rw [accept''_suffix (r.star false) k f none]
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
    exact hf₁
    exact hf₂
  | .star r true => by
    simp
    rw [accept'', accept''_deriv_cond r]
    simp only [Loc.right, List.length_cons]
    rw [accept'']
    simp_rw [accept''_suffix (r.star true) (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) f none]
    simp [hf₂]
    congr
    funext loc
    split_ifs with hl
    · rw [accept''_suffix (r.star true) k f none]
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
    exact hf₁
    exact hf₂
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

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

theorem Option.none_max {α : Type u} [Max α] {x : Option α} :
  none.max x = x := by
  cases x with
  | none => rfl
  | some a => rfl

theorem Option.max_none {α : Type u} [Max α] {x : Option α} :
  x.max none = x := by
  cases x with
  | none => rfl
  | some a => rfl

@[simp]
theorem Option.max_eq_none {α : Type u} [Max α] {x y : Option α} :
  x.max y = none ↔ x = none ∧ y = none := by
  cases x with
  | none =>
    cases y with
    | none =>
      simp
      exact Option.max_none_none
    | some _ =>
      simp
      intro h
      cases h
  | some _ =>
    cases y with
    | none =>
      simp
      intro h
      cases h
    | some =>
      simp
      intro h
      cases h

theorem accept'_deriv_none {r : Regex α} {s₁ s₂ : List σ} {k : Loc σ → Option (Loc σ)} (hn : ¬r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.deriv x).accept'' (x::s₁, s₂) k Option.max = none →
  r.accept'' (s₁, x::s₂) k Option.max = none :=
  match r with
  | epsilon => by simp at hn
  | pred c => by
    simp [accept]
    split_ifs with hc
    · simp [accept'', hc]
    · simp [accept'', hc]
  | plus r₁ r₂ => by
    intro h
    simp at hn
    simp [accept'', hn] at h
    rcases h with ⟨h₁, h₂⟩
    apply accept'_deriv_none at h₁
    apply accept'_deriv_none at h₂
    rw [accept'', Option.max_eq_none]
    exact ⟨h₁, h₂⟩
    simp [hn.right]
    exact hk
    simp [hn.left]
    exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      rw [Regex.deriv, accept'', accept'']
      simp at hn
      apply accept'_deriv_none
      simp [hn]
      exact hk
    | pred c =>
      rw [Regex.deriv]
      split_ifs with hc
      · simp [accept'', hc]
      · simp [accept'', hc]
    | plus r₁₁ r₁₂ =>
      simp
      simp [accept'']
      intro h₁ h₂
      apply accept'_deriv_none at h₁
      apply accept'_deriv_none at h₂
      rw [accept''] at h₁ h₂
      exact ⟨h₁, h₂⟩
      simp_all
      exact hk
      simp_all
      exact hk
    | mul r₁₁ r₁₂ =>
      intro h
      rw [Regex.deriv] at h
      apply accept'_deriv_none at h
      rw [accept'', accept'']
      simp only [accept''] at h
      exact h
      simp_all
      exact hk
    | .star r false =>
      intro h
      simp at h hn
      rw [accept'', accept''] at h
      rw [accept''_deriv_cond] at h
      simp at h
      rcases h with ⟨h₁, h₂⟩
      apply accept'_deriv_none at h₂
      simp_rw [accept''_mul_def] at h₁
      rw [accept'', accept'']
      simp
      refine ⟨?_, h₂⟩
      exact h₁
      simp [hn]
      exact hk
      intro x
      cases x <;> rfl
      intro x
      cases x <;> rfl
    | .star r true =>
      intro h
      simp at h hn
      rw [accept'', accept''] at h
      nth_rw 2 [accept''_deriv_cond] at h
      simp at h
      rcases h with ⟨h₂, h₁⟩
      apply accept'_deriv_none at h₂
      simp_rw [accept''_mul_def] at h₁
      rw [accept'', accept'']
      simp
      refine ⟨h₂, ?_⟩
      exact h₁
      simp [hn]
      exact hk
      intro x
      cases x <;> rfl
      intro x
      cases x <;> rfl
  | .star r _ => by simp at hn
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

theorem accept'_deriv_none_nullable {r : Regex α} {s₁ s₂ : List σ} {k : Loc σ → Option (Loc σ)} (hn : r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.deriv x).accept'' (x :: s₁, s₂) k Option.max = none →
  r.accept'' (s₁, x::s₂) k Option.max = k (s₁, x::s₂) :=
  match r with
  | epsilon => by simp [accept'']
  | pred c => by simp at hn
  | plus r₁ r₂ => by
    simp at hn
    rw [accept'']
    intro h
    simp [accept''] at h
    rcases h with ⟨h₁, h₂⟩
    cases hn with
    | inl hn =>
      apply accept'_deriv_none_nullable at h₁
      by_cases hn' : r₂.nullable
      · apply accept'_deriv_none_nullable at h₂
        rw [h₁, h₂]
        -- max a a = a
        sorry
        exact hn'
        exact hk
      · apply accept'_deriv_none at h₂
        rw [h₁, h₂, Option.max_none]
        exact hn'
        exact hk
      exact hn
      exact hk
    | inr hn =>
      apply accept'_deriv_none_nullable at h₂
      by_cases hn' : r₁.nullable
      · apply accept'_deriv_none_nullable at h₁
        rw [h₁, h₂]
        -- max a a = a
        sorry
        exact hn'
        exact hk
      · apply accept'_deriv_none at h₁
        rw [h₁, h₂, Option.none_max]
        exact hn'
        exact hk
      exact hn
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp only [Regex.deriv, accept'']
      simp at hn
      intro h
      apply accept'_deriv_none_nullable at h
      exact h
      exact hn
      exact hk
    | pred c => simp at hn
    | plus r₁₁ r₁₂ =>
      simp [accept'']
      simp at hn
      sorry
      -- simp_all
      -- simp [accept]
      -- intro h₁ h₂
      -- apply accept_deriv_none (by simp [hn']) hk at h₁
      -- apply accept_deriv_none_nullable (by simp [hn]) hk at h₂
      -- rw [accept] at h₁ h₂
      -- rw [h₁, h₂]
      -- exact Option.none_or
    | mul r₁₁ r₁₂ =>
      simp only [Regex.deriv, accept'']
      intro h
      apply accept'_deriv_none_nullable at h
      simp only [accept''] at h
      exact h
      simp at hn
      simp [hn]
      exact hk
    | .star r false =>
      rw [Regex.deriv]
      rw [accept'', accept'']
      rw [Option.max_eq_none, and_imp]
      rw [accept''_deriv_cond, accept'', accept'']
      rw [Loc.right, List.length_cons]
      intro h₁ h₂
      simp_rw [accept''_mul_def] at h₁
      simp at hn
      apply accept'_deriv_none_nullable hn hk at h₂
      rw [h₁, h₂]
      rw [Option.none_max]
      intro x
      cases x <;> rfl
      intro x
      cases x <;> rfl
    | .star r true =>
      rw [Regex.deriv]
      rw [accept'', accept'']
      rw [Option.max_eq_none, and_imp]
      nth_rw 2 [accept''_deriv_cond]
      rw [accept'', accept'']
      rw [Loc.right, List.length_cons]
      intro h₂ h₁
      simp_rw [accept''_mul_def] at h₁
      simp at hn
      apply accept'_deriv_none_nullable hn hk at h₂
      rw [h₁, h₂, Option.max_none]
      intro x
      cases x <;> rfl
      intro x
      cases x <;> rfl
  | .star r false => by
    rw [Regex.deriv]
    rw [accept'', accept''_deriv_cond, accept'']
    rw [Loc.right, List.length_cons]
    intro h
    rw [h, Option.none_max]
    intro x
    cases x <;> rfl
    intro x
    cases x <;> rfl
  | .star r true => by
    rw [Regex.deriv]
    rw [accept'', accept''_deriv_cond, accept'']
    rw [Loc.right, List.length_cons]
    intro h
    rw [h, Option.max_none]
    intro x
    cases x <;> rfl
    intro x
    cases x <;> rfl
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

theorem accept'_deriv (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (loc : Loc σ) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.deriv x).accept'' (x::s₁, s₂) k Option.max = some loc →
  r.accept'' (s₁, x::s₂) k Option.max = some loc :=
  match r with
  | epsilon => by simp
  | pred c => by
    simp [accept'']
    split_ifs with hc
    · simp [accept'', hc]
    · simp [accept'']
  | plus r₁ r₂ => by
    rw [accept'']
    intro h
    rw [Regex.deriv, accept''] at h
    sorry
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      rw [Regex.deriv, accept'', accept'']
      apply accept'_deriv r₂
      exact hk
    | pred c =>
      simp [accept'']
      split_ifs with hc
      · simp [hc]
      · simp
    | plus r₁₁ r₁₂ =>
      simp [accept'']
      intro h
      sorry
    | mul r₁₁ r₁₂ =>
      simp only [accept'', Regex.deriv]
      intro h
      apply accept'_deriv (r₁₁.mul (r₁₂.mul r₂)) at h
      simp only [accept''] at h
      exact h
      exact hk
    | .star r false =>
      rw [Regex.deriv]
      rw [accept'', accept'', accept''_deriv_cond]
      intro h
      simp at h
      simp_rw [accept''_mul_def] at h
      sorry
      intro x
      cases x <;> rfl
      intro x
      cases x <;> rfl
    | .star r true =>
      rw [Regex.deriv, accept'', accept'']
      nth_rw 2 [accept''_deriv_cond]
      intro h
      sorry
      intro x
      cases x <;> rfl
      intro x
      cases x <;> rfl
  | .star r false => by
    rw [Regex.deriv]
    rw [accept'', accept''_deriv_cond, accept'']
    rw [Loc.right, List.length_cons]
    intro h
    rw [h]
    sorry
    intro x
    cases x <;> rfl
    intro x
    cases x <;> rfl
  | .star r true => by
    rw [Regex.deriv]
    rw [accept'', accept''_deriv_cond, accept'']
    rw [Loc.right, List.length_cons]
    intro h
    rw [h]
    sorry
    intro x
    cases x <;> rfl
    intro x
    cases x <;> rfl
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

theorem matchEnd_accept (r : Regex α) (s₁ s₂ : List σ) :
  r.matchEnd (s₁, s₂) = r.accept (s₁, s₂) some := by
  induction s₂ generalizing r s₁ with
  | nil =>
    rw [Regex.matchEnd]
    split_ifs with hn
    · rw [accept_nil_nullable hn]
    · rw [accept_nil_not_nullable hn]
  | cons x xs ih =>
    rw [Regex.matchEnd]
    cases k : ((r.prune.deriv x).matchEnd (x :: s₁, xs)) with
    | none =>
      simp only
      rw [ih] at k
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
      rw [ih] at k
      apply accept_deriv at k
      rw [k]
      simp only [Option.isSome_some, implies_true]

theorem matchEnd'_accept' (r : Regex α) (s₁ s₂ : List σ) :
  r.matchEnd' (s₁, s₂) = r.accept' (s₁, s₂) some := by
  induction s₂ generalizing r s₁ with
  | nil =>
    rw [Regex.matchEnd']
    split_ifs with hn
    · rw [Regex.accept', accept''_nil_nullable]
      intro x
      cases x with
      | none => rfl
      | some a =>
        unfold Option.max
        simp
        rw [max]
        unfold instMaxLoc
        simp
      intro x
      exact Option.none_max
      intro x
      exact Option.max_none
      exact hn
    · rw [Regex.accept', accept''_nil_not_nullable]
      exact Option.max_none_none
      exact hn
  | cons x xs ih =>
    rw [Regex.matchEnd']
    cases k : ((r.deriv x).matchEnd' (x :: s₁, xs)) with
    | none =>
      simp
      rw [ih] at k
      split_ifs with hn
      · apply accept'_deriv_none_nullable at k
        rw [accept', k]
        exact hn
        simp
      · apply accept'_deriv_none at k
        rw [accept', k]
        exact hn
        simp
    | some v =>
      simp
      rw [ih] at k
      apply accept'_deriv at k
      rw [accept', k]
      simp

theorem rmatch_gmatch (r : Regex α) (s : List σ) :
  r.rmatch s = r.gmatch s := by
  rw [Regex.rmatch, Regex.gmatch]
  apply matchEnd_accept
