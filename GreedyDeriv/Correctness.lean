import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

open Regex

theorem accept_prune (r : Regex α) (l : Loc α) (k : Loc α → Option (Loc α)) (hk : ∀ l', (k l').isSome) :
  r.accept l k = r.prune.accept l k := by
  induction r generalizing l k with
  | emptyset => simp only [prune]
  | epsilon => simp only [prune]
  | char c => simp only [prune]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [prune]
    split_ifs with hn
    · rw [accept, ←ih₁ _ _ hk]
      apply Option.or_of_isSome
      apply accept_nullable
      exact hn
      apply hk
    · rw [accept, accept]
      rw [ih₁ _ _ hk, ih₂ _ _ hk]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp only [prune]
    split_ifs with hn
    · simp only [accept]
      rw [ih₁]
      rw [←ih₂ _ k hk]

      -- generalize hr₁ : r₁.prune = r₁' at *
      -- generalize hr₂ : r₂.prune = r₂' at *
      generalize hk' : (fun loc' ↦ r₂.accept loc' k) = k' at *
      rw [congrFun hk' l]
      -- have hn₁' : r₁'.nullable := by
      --   -- r.prune.nullable = r.nullable
      --   sorry
      -- clear hn hr₁ hr₂ hk hk' ih₁ ih₂
      clear ih₁ ih₂
      induction r₁ with
      | emptyset => simp at hn
      | epsilon => simp [accept]
      | char => simp at hn
      | plus r₁ r₂ ih₁ ih₂ =>
        simp [accept]
        simp at hn
        split_ifs with hn₁
        · rw [ih₁]
          exact ⟨hn₁, hn.right⟩
        · simp [hn₁] at hn
          simp [accept]
          rw [ih₂ hn]
          -- True, since ¬r.nullable → r.denullify = r
          sorry
      | mul r₁ r₂ ih₁ ih₂ =>
        simp only [prune]
        split_ifs with hn₁
        · simp
          split_ifs with hn'
          · -- Contradiction: r.denullify.nullable = true
            sorry
          · simp at hn'
            simp [accept]
            rw [ih₂, Option.or_assoc]
            exact ⟨hn₁.right, hn.right⟩
        · simp_all
      | star r lazy? ih =>
        cases lazy? with
        | false =>
          simp [prune, denullify]
          simp_all
          rw [accept, accept_denullify, accept]
        | true => simp [accept]
      intro l'
      apply accept_nullable
      exact hn.right
      exact hk l'
      -- intro l'
      -- apply accept_nullable
      -- exact hn
      -- exact hk l'
    · simp [accept]
      -- simp_rw [ih₂ _ _ hk]
  | star r lazy? =>
    cases lazy? with
    | false => rw [prune]
    | true =>
      rw [prune]
      rw [accept, accept]
      rw [Option.or_of_isSome]
      apply hk

/-- Theorem 16 -/
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
    | .star r false =>
      simp
      rw [accept, accept, accept, accept]
      rw [accept_deriv_cond r]
      rw [accept_deriv_cond r₂]
      simp only [Loc.right, List.length_cons]
      simp_rw [accept_suffix (r.star false) (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < v.length + 1 then k l' else none) none]
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
      · rfl
    | .star r true =>
      simp
      rw [accept, accept, accept, accept]
      rw [accept_deriv_cond r]
      rw [accept_deriv_cond r₂]
      simp only [Loc.right, List.length_cons]
      simp_rw [accept_suffix (r.star true) (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < v.length + 1 then k l' else none) none]
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
      · rfl
  | .star r  false => by
    simp
    rw [accept, accept_deriv_cond r]
    simp only [Loc.right, List.length_cons]
    rw [accept]
    simp_rw [accept_suffix (r.star false) (fun l' ↦ if l'.2.length < v.length + 1 then k l' else none) none]
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
    simp_rw [accept_suffix (r.star true) (fun l' ↦ if l'.2.length < v.length + 1 then k l' else none) none]
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

/-- Theorem 17 -/
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
      intro h
      split_ifs at h with hn₂
      · simp [accept] at h
        apply accept_deriv_none hk
        exact h
      · simp [accept] at h
        rw [←prune_not_nullable _ hn₂] at h
        apply accept_deriv_none at h
        exact h
        exact hk
    | char c =>
      simp [accept]
      split_ifs with hc
      · simp [hc]
      · simp [hc]
    | plus r₁₁ r₁₂ =>
      intro h
      simp [accept] at h
      split_ifs at h with hn hn'
      · rw [accept, accept, ←accept_mul_def]
        rw [Option.or_of_isSome]
        have ih := @accept_deriv_none (r₁₁.mul r₂) c u v k hk
        simp [hn, hn'] at ih
        simp [hn, hn']
        rw [Regex.deriv] at h
        exact ih h
        apply accept_nullable
        simp [hn, hn']
        apply hk
      · simp [accept] at h
        rcases h with ⟨h₁, h₂⟩
        have ih₁ := @accept_deriv_none (r₁₁.mul r₂) c u v k hk
        have ih₂ := @accept_deriv_none (r₁₂.mul r₂) c u v k hk
        simp [hn, hn'] at ih₁
        rw [accept, accept, ←accept_mul_def, ←accept_mul_def]
        rw [Option.or_of_isNone]
        simp [hn, hn'] at ih₂
        simp [hn, hn']
        simp_all
        apply ih₂
        simp [accept]
        exact ⟨h₁.right, h₂⟩
        simp
        -- Need: ¬r.nullable → r.prune = r and ¬r.nullable → r.denullify = r
        sorry
        -- exact ih₂ h₂
        -- simp [ih₁ h₁]
      · simp [accept] at h
        rcases h with ⟨h₁, h₂⟩
        have ih₁ := @accept_deriv_none (r₁₁.mul r₂) c u v k hk
        have ih₂ := @accept_deriv_none (r₁₂.mul r₂) c u v k hk
        simp [hn] at ih₁ ih₂
        simp [hn]
        rw [accept, accept, ←accept_mul_def, ←accept_mul_def]
        split_ifs at ih₁
        · simp_all
        · split_ifs at ih₂
          · simp_all
          · simp
            exact ⟨ih₁ h₁, ih₂ h₂⟩
    | mul r₁₁ r₁₂ =>
      intro h
      simp [prune] at h
      have ih := @accept_deriv_none (r₁₁.mul (r₁₂.mul r₂)) c u v k hk
      split_ifs at h with hn₂ hn₁₂
      · simp [prune, hn₂, hn₁₂] at ih
        rw [Regex.deriv] at h
        simp [accept, hn₂, hn₁₂]
        simp_rw [←accept_mul_def]
        apply ih
        simp [accept] at h
        simp [accept]
        sorry
        -- exact ih h
      · simp [prune, hn₂, hn₁₂] at ih
        rw [Regex.deriv] at h
        simp [accept, hn₂, hn₁₂]
        simp_rw [←accept_mul_def]
        simp_all
        -- exact ih h
      · simp [prune, hn₂] at ih
        rw [Regex.deriv] at h
        simp [accept, hn₂]
        simp_rw [←accept_mul_def]
        split_ifs at ih
        · simp_all
        · simp_all
        · exact ih h
    | .star r false =>
      intro h
      simp only [prune] at h
      simp at h
      split_ifs at h with hn₂
      · simp [accept] at h
        simp [hn₂]
        rcases h with ⟨h₁, h₂⟩
        rw [accept_deriv_cond] at h₁
        rw [accept] at h₁
        rw [accept_denullify] at h₁
        apply accept_deriv_none at h₂
        rw [accept, accept]
        rw [Option.or_of_isNone]
        simp [h₂, hn₂]
        simp
        nth_rw 2 [←h₁]
        simp
        congr
        funext l'
        split_ifs with hl'
        · rw [accept]
          rw [accept_suffix _ _ none]
          rw [accept_suffix _ (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < v.length + 1 then k l' else none) none]
          congr
          funext l''
          split_ifs with hl''
          · rw [accept_suffix _ _ none]
            rw [accept_suffix _ (fun l' ↦ if l'.2.length < v.length + 1 then k l' else none) none]
            congr
            funext l'''
            split_ifs with hl''' hl''''
            · rfl
            · absurd hl''''
              apply Nat.lt_of_le_of_lt
              exact Nat.le_trans hl''' hl''
              exact hl'
            · rfl
          · rfl
        · rfl
        exact hk
        -- I think we should have that (r₁.denullify.mul r₂).deriv c =
        -- (r₁.denullify.deriv c).mul r₂
        -- NOPE :( -- language acceptance yes, but not equal
      · simp at h
        rw [accept, accept] at h
        rw [accept_deriv_cond] at h
        simp at h
        rcases h with ⟨h₁, h₂⟩
        rw [←prune_not_nullable r₂ hn₂] at h₂
        apply accept_deriv_none at h₂
        simp_rw [accept_mul_def] at h₁
        rw [accept, accept]
        simp [hn₂]
        rw [h₁, h₂]
        simp [hn₂]
        exact hk
        -- simp_rw [←accept_prune r₂ _ k hk] at h₁
        -- rw [h₁, h₂, Option.none_or]
        -- exact hk
    | .star r true =>
      simp
      intro h
      split_ifs at h with hn
      · rw [Regex.deriv] at h
        simp [accept] at h
        apply accept_deriv_none at h
        rw [accept, accept, h, Option.or_of_isSome]
        simp [hn]
        apply hk
        exact hk
      · rw [Regex.deriv, accept, accept] at h
        simp at h
        rcases h with ⟨h₁, h₂⟩
        rw [←prune_not_nullable _ hn] at h₁
        apply accept_deriv_none at h₁
        rw [accept_deriv_cond] at h₂
        simp_rw [accept_mul_def] at h₂
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
    simp only [prune, Regex.deriv, nullable, reduceIte]
    rw [accept]
    simp only [forall_const]
    rw [accept, Option.or_of_isSome]
    apply hk
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

/-- Theorem 18 -/
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
      simp [accept]
      apply accept_deriv r₂
      exact hk
    | char c =>
      simp [accept]
      split_ifs with hc
      · simp [accept, hc]
        simp [accept_prune r₂ _ k hk]
      · simp [accept]
    | plus r₁₁ r₁₂ =>
      have ih₁ := @accept_deriv c (r₁₁.mul r₂) u v k loc hk
      have ih₂ := @accept_deriv c (r₁₂.mul r₂) u v k loc hk
      simp [accept]
      simp_rw [←accept_mul_def]
      split_ifs with hn hn'
      · intro h
        simp [hn, hn'] at ih₁
        exact Or.inl (ih₁ h)
      · intro h
        simp [accept] at h
        simp [hn, hn'] at ih₁ ih₂
        cases h with
        | inl h =>
          exact Or.inl (ih₁ h)
        | inr h =>
          rcases h with ⟨h₁, h₂⟩
          refine Or.inr ⟨?_, ih₂ h₂⟩
          rw [←prune_mul_nullable hn] at h₁
          apply accept_deriv_none at h₁
          simp [hn'] at h₁
          exact h₁
          exact hk
      · intro h
        simp [accept] at h
        simp [hn] at ih₁ ih₂
        cases h with
        | inl h =>
          exact Or.inl (ih₁ h)
        | inr h =>
          rcases h with ⟨h₁, h₂⟩
          refine Or.inr ⟨?_, ih₂ h₂⟩
          rw [←prune_mul_not_nullable hn] at h₁
          apply accept_deriv_none at h₁
          simp [hn] at h₁
          exact h₁
          exact hk
    | mul r₁₁ r₁₂ =>
      simp [prune, accept]
      simp_rw [←accept_mul_def]
      split_ifs with hn₂ hn₁₂
      · rw [Regex.deriv]
        rw [←prune_mul_nullable hn₂]
        rw [←prune_mul_nullable (by simp [hn₁₂, hn₂])]
        exact accept_deriv (r₁₁.mul (r₁₂.mul r₂)) _ _ _ _ hk
      · rw [Regex.deriv]
        rw [←prune_mul_nullable hn₂]
        rw [←prune_mul_not_nullable (by simp [hn₁₂])]
        exact accept_deriv (r₁₁.mul (r₁₂.mul r₂)) _ _ _ _ hk
      · rw [Regex.deriv]
        rw [←prune_mul_not_nullable hn₂]
        rw [←prune_mul_not_nullable (by simp [hn₂])]
        exact accept_deriv (r₁₁.mul (r₁₂.mul r₂)) _ _ _ _ hk
    | .star r false =>
      rw [prune]
      split_ifs with hn
      · rw [prune]
        rw [Regex.deriv]
        rw [accept, accept, accept_deriv_cond]
        intro h
        simp at h
        simp_rw [accept_mul_def] at h
        simp_rw [←accept_prune r₂ _ k hk] at h
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
      · rw [Regex.deriv]
        rw [accept, accept, accept_deriv_cond]
        intro h
        simp at h
        simp_rw [accept_mul_def] at h
        simp_rw [←accept_prune r₂ _ k hk] at h
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
        rw [prune, Regex.deriv] at h
        apply accept_deriv r₂ _ _ k loc hk at h
        rw [accept, accept, h]
        rw [Loc.right, List.length_cons, Option.some_or]
      · rw [Regex.deriv, accept, accept]
        rw [accept_deriv_cond r]
        intro h
        simp_rw [Loc.right, List.length_cons, Option.or_eq_some] at h
        simp_rw [accept_mul_def] at h
        simp_rw [←accept_prune r₂ _ k hk] at h
        rw [accept, accept]
        rw [Loc.right, List.length_cons, Option.or_eq_some]
        cases h with
        | inl h =>
          apply accept_deriv r₂ _ _ k loc hk at h
          exact Or.inl h
        | inr h =>
          rcases h with ⟨h₁, h₂⟩
          apply accept_deriv_none at h₁
          simp [hn] at h₁
          exact Or.inr ⟨h₁, h₂⟩
          exact hk
  | .star r false => by
    rw [prune, Regex.deriv]
    rw [accept, accept_deriv_cond, accept]
    rw [Loc.right, List.length_cons, Option.or_eq_some]
    intro h
    exact Or.inl h
  | .star r true => by
    rw [prune, Regex.deriv, accept]
    simp
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

/-- Theorem 19 -/
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
