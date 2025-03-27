import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

open Regex

theorem accept_dist_star (r r₂ : Regex α) (l : Loc α) (k : Loc α → Option (Loc α)) :
  (plus (dist_star_alts r r.star r₂) r₂).accept l k = (r.star.mul r₂).accept l k := by
  cases r with
  | emptyset =>
    rw [dist_star_alts]
    rw [accept, accept, accept, accept]
    simp
  | epsilon =>
    rw [dist_star_alts]
    rw [accept, accept, accept, accept]
    simp
  | char c =>
    rw [dist_star_alts]
    rw [accept, accept, accept, accept]
    simp
    match l with
    | ⟨u, []⟩ =>
      rw [accept, accept]
    | ⟨u, c::v⟩ =>
      rw [accept, accept]
      simp
      simp_rw [←accept_mul_def]
  | plus r₁₁ r₁₂ =>
    rw [dist_star_alts]
    split_ifs with hn
    · sorry
    · rw [accept, accept, accept, accept, accept]
      simp_rw [←accept_mul_def]

      sorry
  | mul r₁₂ r₁₂ => sorry
  | star r => sorry

/-- Theorem 12 -/
theorem accept_prune (r : Regex α) (l : Loc α) (k : Loc α → Option (Loc α)) (hk : ∀ l', (k l').isSome) :
  r.accept l k = r.prune.accept l k :=
  match r with
  | emptyset => by simp only [prune]
  | epsilon => by simp only [prune]
  | char c => by simp only [prune]
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
    | emptyset => simp [accept, prune]
    | epsilon =>
      simp only [accept, prune]
      rw [accept_prune r₂]
      exact hk
    | char c =>
      simp only [accept, prune]
      congr
      funext l
      rw [accept_prune r₂ l k hk]
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
    | .star r => sorry
  | .star r => by
    rw [prune]
    rw [accept, accept]
    rw [←accept_prune]
    congr
    funext l'
    split_ifs with hl
    · rw [←prune_star_def]
      rw [accept_prune]
      exact hk
    · rfl
    intro l'
    split_ifs with hl
    · apply accept_nullable
      simp only [nullable]
      apply hk
    · apply hk
termination_by (r.size, r.left.size)
decreasing_by all_goals sorry

/-- Theorem 13 -/
theorem accept_deriv_cond (r : Regex α) (u v : List α) (c : α) (k : Loc α → Option (Loc α)) :
  (r.deriv c).accept (c::u, v) k = r.accept (u, c::v) (fun l' ↦ if l'.right.length < (c::v).length then k l' else none) :=
  match r with
  | emptyset => by simp [accept]
  | epsilon => by simp [accept]
  | char c => by
    simp [accept]
    split_ifs
    · rw [accept]
    · rw [accept]
  | plus r₁ r₂ => by
    simp [accept]
    rw [accept_deriv_cond, accept_deriv_cond]
    simp only [Loc.right, List.length_cons]
  | mul r₁ r₂ => by
    match r₁ with
    | emptyset => simp [accept]
    | epsilon =>
      simp [accept]
      rw [accept_deriv_cond]
      simp only [Loc.right, List.length_cons]
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
      simp only [Loc.right, List.length_cons]
      simp_rw [accept_suffix r.star (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < v.length + 1 then k l' else none) none]
      congr
      funext loc
      split_ifs with hl
      · rw [accept_mul_def]
        rw [accept_suffix r.star _ none]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ none]
          rw [accept_suffix r₂ (fun l' ↦ if l'.2.length < _ then _ else _) none]
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
      · sorry
  | .star r => by
    simp
    rw [accept, accept_deriv_cond r]
    simp only [Loc.right, List.length_cons]
    rw [accept]
    simp_rw [accept_suffix r.star (fun l' ↦ if l'.2.length < v.length + 1 then k l' else none) none]
    simp
    congr
    funext loc
    split_ifs with hl
    · rw [accept_suffix r.star k none]
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

/-- Theorem 14 -/
theorem accept_deriv_none {r : Regex α} {c : α} {u v : List α} {k : Loc α → Option (Loc α)} (hk : ∀ l, (k l).isSome) :
  (r.prune.deriv c).accept (c::u, v) k = none →
  r.accept (u, c::v) k = if r.nullable then k (u, c::v) else none :=
  match r with
  | emptyset => by simp [accept]
  | epsilon => by simp [accept]
  | char d => by
    simp [accept]
    split_ifs with hc
    · simp [accept, hc]
    · simp [accept, hc]
  | plus r₁ r₂ => by
    simp [accept]
    intro h
    split_ifs at h with hn₁
    · apply accept_deriv_none at h
      simp [hn₁] at h
      simp [hn₁]
      rw [h, Option.or_of_isSome]
      apply hk
      exact hk
    · simp [accept] at h
      rcases h with ⟨h₁, h₂⟩
      apply accept_deriv_none at h₁
      apply accept_deriv_none at h₂
      simp [hn₁] at h₁
      simp [h₁, hn₁]
      exact h₂
      exact hk
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | emptyset => simp [accept]
    | epsilon =>
      simp [accept]
      apply accept_deriv_none
      exact hk
    | char c =>
      simp [accept]
      split_ifs with hc
      · simp [hc, accept_prune r₂ _ k hk]
      · simp [hc]
    | plus r₁₁ r₁₂ =>
      intro h
      simp [accept] at h
      split_ifs at h with hn
      · apply accept_deriv_none at h
        simp [hn]
        rw [accept, accept, ←accept_mul_def]
        simp [hn] at h
        rw [h, Option.or_of_isSome]
        apply hk
        exact hk
      · simp [accept] at h
        rcases h with ⟨h₁, h₂⟩
        apply accept_deriv_none at h₁
        apply accept_deriv_none at h₂
        simp [hn] at h₁
        simp only [nullable, Bool.and_eq_true] at h₂
        simp [or_and_right, hn]
        rw [accept, accept, ←accept_mul_def, ←accept_mul_def]
        rw [h₁, h₂, Option.none_or]
        exact hk
        exact hk
    | mul r₁₁ r₁₂ =>
      rw [prune]
      intro h
      apply accept_deriv_none at h
      simp [accept]
      simp [accept] at h
      simp_rw [h, and_assoc]
      exact hk
    | .star r => sorry
      -- intro h
      -- simp at h
      -- rw [accept, accept] at h
      -- rw [accept_deriv_cond] at h
      -- simp at h
      -- rcases h with ⟨h₁, h₂⟩
      -- apply accept_deriv_none at h₂
      -- simp_rw [accept_mul_def] at h₁
      -- rw [accept, accept]
      -- simp
      -- simp_rw [←accept_prune r₂ _ k hk] at h₁
      -- rw [h₁, h₂, Option.none_or]
      -- exact hk
  | .star r => by
    sorry
    -- rw [prune, Regex.deriv]
    -- rw [accept, accept_deriv_cond, accept]
    -- rw [Loc.right, List.length_cons]
    -- intro h
    -- rw [h]
    -- exact Option.none_or
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

/-- Theorem 15 -/
theorem accept_deriv (r : Regex α) (u v : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) (hk : ∀ l', (k l').isSome) :
  (r.prune.deriv c).accept (c::u, v) k = some loc →
  r.accept (u, c::v) k = some loc :=
  match r with
  | emptyset => by simp [accept]
  | epsilon => by simp [accept]
  | char d => by
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
        rw [accept_deriv_none]
        simp [hn]
        exact hk
        exact h₁
        exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | emptyset => simp [accept]
    | epsilon =>
      rw [prune, accept, accept]
      apply accept_deriv r₂
      exact hk
    | char c =>
      simp [accept]
      split_ifs with hc
      · simp [accept, hc]
        simp [accept_prune r₂ _ k hk]
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
          · rw [←accept_mul_def, accept_deriv_none]
            simp [hn]
            exact hk
            exact h₁
          exact hk
    | mul r₁₁ r₁₂ =>
      simp only [prune, accept]
      intro h
      apply accept_deriv (r₁₁.mul (r₁₂.mul r₂)) at h
      simp only [accept] at h
      exact h
      exact hk
    | .star r =>
      sorry
      -- rw [prune, Regex.deriv]
      -- rw [accept, accept, accept_deriv_cond]
      -- intro h
      -- simp at h
      -- simp_rw [accept_mul_def] at h
      -- simp_rw [←accept_prune r₂ _ k hk] at h
      -- cases h with
      -- | inl h =>
      --   rw [accept, accept]
      --   rw [Loc.right, List.length_cons, Option.or_eq_some]
      --   exact Or.inl h
      -- | inr h =>
      --   rcases h with ⟨h₁, h₂⟩
      --   apply accept_deriv r₂ _ _ k loc hk at h₂
      --   rw [accept, accept]
      --   rw [Loc.right, List.length_cons, Option.or_eq_some]
      --   exact Or.inr ⟨h₁, h₂⟩
  | .star r => by
    sorry
    -- rw [prune, Regex.deriv]
    -- rw [accept, accept_deriv_cond, accept]
    -- rw [Loc.right, List.length_cons, Option.or_eq_some]
    -- intro h
    -- exact Or.inl h
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

/-- Theorem 16 -/
theorem matchEnd_gmatch (r : Regex α) (l : Loc α) :
  r.matchEnd l = r.gmatch l := by
  rw [gmatch]
  match l with
  | ⟨u, []⟩ =>
    rw [Regex.matchEnd, accept_nil]
  | ⟨u, c::v⟩ =>
    rw [Regex.matchEnd]
    cases k : ((r.prune.deriv c).matchEnd (c :: u, v)) with
    | none =>
      simp only
      rw [matchEnd_gmatch] at k
      split_ifs with hn
      · apply accept_deriv_none at k
        simp [k, hn]
        simp only [Option.isSome_some, implies_true]
      · apply accept_deriv_none at k
        simp [k, hn]
        simp only [Option.isSome_some, implies_true]
    | some v =>
      simp only
      rw [matchEnd_gmatch] at k
      apply accept_deriv at k
      rw [k]
      simp only [Option.isSome_some, implies_true]
termination_by l.right
