import GreedyDeriv.Regex
import Mathlib.Tactic

variable {α σ : Type u} [EffectiveBooleanAlgebra α σ]

open Regex

def Regex.accept : Regex α → Loc σ → (Loc σ → Option (Loc σ)) → Option (Loc σ)
  | epsilon, loc, k => k loc
  | pred _, (_, []), _ => none
  | pred c, (u, d::v), k => if denote c d then k (d::u, v) else none
  | plus r₁ r₂, loc, k => (r₁.accept loc k).or (r₂.accept loc k)
  | mul r₁ r₂, loc, k => r₁.accept loc (fun loc' => r₂.accept loc' k)
  | star r false, loc, k => (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then (r.star false).accept loc' k else none)).or (k loc)
  | star r true, loc, k => (k loc).or (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then (r.star true).accept loc' k else none))
termination_by r loc => (r.size, loc.right.length)

def Regex.accept' : Regex α → Loc σ → (Loc σ → Option (Loc σ)) → Option (Loc σ)
  | epsilon, loc, k => k loc
  | pred _, (_, []), _ => none
  | pred c, (u, d::v), k => if denote c d then k (d::u, v) else none
  | plus r₁ r₂, loc, k => (r₁.accept' loc k).max (r₂.accept' loc k)
  | mul r₁ r₂, loc, k => r₁.accept' loc (fun loc' => r₂.accept' loc' k)
  | star r false, loc, k => (r.accept' loc (fun loc' => if loc'.right.length < loc.right.length then (r.star false).accept' loc' k else none)).max (k loc)
  | star r true, loc, k => (k loc).max (r.accept' loc (fun loc' => if loc'.right.length < loc.right.length then (r.star true).accept' loc' k else none))
termination_by r loc => (r.size, loc.right.length)

def Regex.gmatch : Regex α → List σ → Option (Loc σ)
  | r, s => r.accept ([], s) some

def Regex.llmatch : Regex α → List σ → Option (Loc σ)
  | r, s => r.accept' ([], s) some

theorem accept'_matches (r : Regex α) (l loc : Loc σ) :
  accept' r l some = some loc → Matches r l loc := by
  sorry

theorem matches_accept' (r : Regex α) (l loc : Loc σ)  :
  Matches r l loc → ∃ loc', accept' r l some = some loc' := by
  sorry

theorem accept'_longest (r : Regex α) (l loc : Loc σ) (h : accept' r l some = some loc) :
  (∀ l' : Loc σ, l'.word = l.word → Matches r l l' → l'.pos ≤ loc.pos) :=
  match r with
  | epsilon => by
    intro l' hl hm
    cases hm with
    | epsilon =>
      simp [accept'] at h
      rw [h]
  | pred c => by
    intro l' hl hm
    cases hm with
    | pred _ d u v hd =>
      simp [accept'] at h
      rw [h.right]
  | plus r₁ r₂ => sorry
  | mul r₁ r₂ =>
    match r₁ with
    | epsilon => by
      intro l' hl hm
      cases hm with
      | mul u v s t h₁ h₂ =>
        generalize hw : v ++ s ++ t = w
        generalize hu' : v.reverse ++ u = u'
        rw [hw, hu'] at h₁
        cases h₁ with
        | epsilon =>
          simp at hu'
          simp [accept', hu'] at h
          simp [hu'] at h₂
          have tmp := accept'_longest r₂ (u, s ++ t) loc h (s.reverse ++ u, t) (by simp) h₂
          simp at tmp
          simp [hu']
          exact tmp
    | pred c => by
      intro l' hl hm
      cases hm with
      | mul u v s t h₁ h₂ =>
        generalize hw : v ++ s ++ t = w
        generalize hu' : v.reverse ++ u = u'
        rw [hw, hu'] at h₁
        cases h₁ with
        | pred _ d _ _ hd =>
          simp at hw
          rw [←List.singleton_append, List.append_left_inj] at hw
          rw [hw] at h h₂
          simp [accept'] at h
          simp at h₂
          have tmp := accept'_longest r₂ (d::u, s ++ t) loc h.right (s.reverse ++ d :: u, t) (by simp) h₂
          rw [hw]
          simp at *
          exact tmp
    | plus r₁₁ r₁₂ => by
      intro l' hl hm
      simp [accept'] at h
      apply Matches_distrib at hm
      cases hm with
      | plus_left _ _ hm =>
        rcases (matches_accept' _ _ _ hm) with ⟨loc', h'⟩
        have tmp := accept'_longest (r₁₁.mul r₂) l loc' h' l' hl hm
        sorry
      | plus_right _ _ hm =>
        rcases (matches_accept' _ _ _ hm) with ⟨loc', h'⟩
        have ih := accept'_longest (r₁₂.mul r₂) l loc' h' l' hl hm
        sorry
    | mul r₁₁ r₁₂ => sorry
    | .star r _ => sorry
  | .star r lazy? => by
    intro l' hl hm
    cases hm with
    | star_nil =>
      -- True!
      sorry
    | stars u v s t h₁ h₂ => sorry

theorem accept_mul_def (r₁ r₂ : Regex α) (loc : Loc σ) (k : Loc σ → Option (Loc σ)) :
  (r₁.mul r₂).accept loc k = (r₁.accept loc (fun loc' => r₂.accept loc' k)) := by
  rw [accept]

@[simp]
theorem accept_bot (loc : Loc σ) (k : Loc σ → Option (Loc σ)) :
  (@pred α ⊥).accept loc k = none := by
  match loc with
  | ⟨_, []⟩ => simp [accept]
  | ⟨_, x::xs⟩ => simp [accept]

theorem accept_suffix (r : Regex α) (k : Loc σ → Option (Loc σ)) (x : Option (Loc σ)) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length ≤ s₂.length then k l' else x) :=
  match r with
  | epsilon => by
    simp [accept]
  | pred c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ => by
    simp only [accept, Loc.right]
    rw [accept_suffix r₁, accept_suffix r₂]
    rfl
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp only [accept, Loc.right]
      rw [accept_suffix r₂ _ x]
      rfl
    | pred c =>
      cases s₂ with
      | nil => simp [accept]
      | cons y ys =>
        simp [accept]
        split_ifs with hc
        · rw [accept_suffix r₂ _ x]
          nth_rw 2 [accept_suffix r₂ _ x]
          simp only [Loc.right]
          congr
          funext l
          split_ifs with hl hl'
          · rfl
          · absurd hl'
            apply Nat.le_succ_of_le
            exact hl
          · rfl
        · rfl
    | plus r₁₁ r₁₂ =>
      simp only [accept, Loc.right]
      repeat rw [←accept_mul_def]
      rw [accept_suffix (r₁₁.mul r₂) _ x]
      rw [accept_suffix (r₁₂.mul r₂) _ x]
      rfl
    | mul r₁₁ r₁₂ =>
      simp only [accept, Loc.right]
      simp_rw [←accept_mul_def r₁₂ r₂]
      repeat rw [←accept_mul_def]
      rw [accept_suffix (r₁₁.mul (r₁₂.mul r₂)) _ x]
      rfl
    | .star r true =>
      rw [accept, accept, accept, accept]
      simp only [Loc.right]
      rw [accept_suffix r₂ _ x]
      congr
      funext loc'
      split_ifs with hl
      · rw [accept_suffix (r.star _) _ x]
        nth_rw 2 [accept_suffix (r.star _) _ x]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ x]
          nth_rw 2 [accept_suffix r₂ _ x]
          congr
          funext l'
          split_ifs with h₂ h₃
          · rfl
          · absurd h₃
            apply Nat.le_trans
            exact h₂
            apply Nat.le_trans
            exact h₁
            exact Nat.le_of_lt hl
          · rfl
        · rfl
      · rfl
    | .star r false =>
      rw [accept, accept, accept, accept]
      simp only [Loc.right]
      rw [accept_suffix r₂ _ x]
      congr
      funext loc'
      split_ifs with hl
      · rw [accept_suffix (r.star _) _ x]
        nth_rw 2 [accept_suffix (r.star _) _ x]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ x]
          nth_rw 2 [accept_suffix r₂ _ x]
          congr
          funext l'
          split_ifs with h₂ h₃
          · rfl
          · absurd h₃
            apply Nat.le_trans
            exact h₂
            apply Nat.le_trans
            exact h₁
            exact Nat.le_of_lt hl
          · rfl
        · rfl
      · rfl
  | .star r false => by
    rw [accept, accept]
    simp only [Loc.right, le_refl, ↓reduceIte]
    congr
    funext loc'
    split_ifs with hl
    · rw [accept_suffix (r.star _) _ x]
      nth_rw 2 [accept_suffix (r.star _) _ x]
      simp only [Prod.mk.eta, Loc.right]
      congr
      funext l
      split_ifs with h₁ h₂
      · rfl
      · absurd h₂
        apply Nat.le_trans
        exact h₁
        exact Nat.le_of_lt hl
      · rfl
    · rfl
  | .star r true => by
    rw [accept, accept]
    simp only [Loc.right, le_refl, ↓reduceIte]
    congr
    funext loc'
    split_ifs with hl
    · rw [accept_suffix (r.star _) _ x]
      nth_rw 2 [accept_suffix (r.star _) _ x]
      simp only [Prod.mk.eta, Loc.right]
      congr
      funext l
      split_ifs with h₁ h₂
      · rfl
      · absurd h₂
        apply Nat.le_trans
        exact h₁
        exact Nat.le_of_lt hl
      · rfl
    · rfl
termination_by (s₂.length, r.size, r.left.size)
decreasing_by
  any_goals decreasing_tactic
  · simp only [size, left]
    apply Prod.Lex.right
    omega

theorem accept_nullable (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (hn : r.nullable) (hk : (k (s₁, s₂)).isSome) :
  (r.accept (s₁, s₂) k).isSome := by
  induction r generalizing s₁ s₂ k with
  | epsilon =>
    rw [accept]
    exact hk
  | pred c => simp only [nullable, Bool.false_eq_true] at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    rw [nullable, Bool.or_eq_true] at hn
    cases hn with
    | inl hn =>
      rw [accept, Option.isSome_or, Bool.or_eq_true]
      left
      apply ih₁
      exact hn
      exact hk
    | inr hn =>
      rw [accept, Option.isSome_or, Bool.or_eq_true]
      right
      apply ih₂
      exact hn
      exact hk
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [nullable, Bool.and_eq_true] at hn
    rw [accept]
    apply ih₁
    exact hn.left
    apply ih₂
    exact hn.right
    exact hk
  | star r lazy? _ =>
    cases lazy? with
    | false =>
      rw [accept]
      simp
      exact Or.inr hk
    | true =>
      rw [accept]
      simp
      exact Or.inl hk

theorem accept_not_nullable (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (x : Option (Loc σ)) (hn : ¬r.nullable) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else x) :=
  match r with
  | epsilon => by simp only [nullable, not_true_eq_false] at hn
  | pred c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ => by
    simp at hn
    simp only [accept, Loc.right]
    rw [accept_not_nullable r₁ _ _ _ x]
    rw [accept_not_nullable r₂ _ _ _ x]
    rfl
    simp [hn.right]
    simp [hn.left]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp at hn
      simp only [accept, Loc.right]
      rw [accept_not_nullable r₂ _ _ _ x]
      rfl
      simp [hn]
    | pred c =>
      cases s₂ with
      | nil => simp [accept]
      | cons y ys =>
        simp only [accept, Loc.right, List.length_cons]
        split_ifs with hc
        · simp_rw [Nat.lt_succ]
          rw [accept_suffix _ _ x]
          simp only [Loc.right]
        · rfl
    | plus r₁₁ r₁₂ =>
      simp at hn
      simp only [accept, Loc.right]
      repeat rw [←accept_mul_def]
      rw [accept_not_nullable (r₁₁.mul r₂) _ _ k x]
      rw [accept_not_nullable (r₁₂.mul r₂) _ _ k x]
      rfl
      · simp
        intro h
        apply hn
        exact Or.inr h
      · simp
        intro h
        apply hn
        exact Or.inl h
    | mul r₁₁ r₁₂ =>
      simp only [accept, Loc.right]
      simp_rw [←accept_mul_def]
      apply accept_not_nullable (r₁₁.mul (r₁₂.mul r₂))
      simp at hn
      simp
      exact hn
    | .star r false =>
      simp at hn
      rw [accept, accept, accept, accept]
      simp only [Loc.right]
      rw [accept_not_nullable r₂ _ _ k x]
      congr
      funext loc'
      split_ifs with hl
      · rw [accept_suffix (r.star _) _ x]
        nth_rw 2 [accept_suffix (r.star _) _ x]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ x]
          nth_rw 2 [accept_suffix r₂ _ x]
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
      simp [hn]
    | .star r true =>
      simp at hn
      rw [accept, accept, accept, accept]
      simp only [Loc.right]
      rw [accept_not_nullable r₂ _ _ k x]
      congr
      funext loc'
      split_ifs with hl
      · rw [accept_suffix (r.star _) _ x]
        nth_rw 2 [accept_suffix (r.star _) _ x]
        simp only [Prod.mk.eta, Loc.right]
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ x]
          nth_rw 2 [accept_suffix r₂ _ x]
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
      simp [hn]
  | .star r false => by simp at hn
  | .star r true => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_cont_none (r : Regex α) (s₁ s₂ : List σ) :
  r.accept (s₁, s₂) (fun _ ↦ none) = none :=
  match r with
  | epsilon => by rw [accept]
  | pred c => by
    cases s₂ with
    | nil => rw [accept]
    | cons x xs => rw [accept, ite_self]
  | plus r₁ r₂ => by
    rw [accept, Option.or_eq_none]
    rw [accept_cont_none, accept_cont_none]
    simp only [and_self]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      rw [accept, accept, accept_cont_none]
    | pred c =>
      cases s₂ with
      | nil => rw [accept, accept]
      | cons x xs =>
        rw [accept, accept, accept_cont_none]
        apply ite_self
    | plus r₁₁ r₁₂ =>
      rw [accept, accept]
      rw [←accept_mul_def, ←accept_mul_def]
      rw [accept_cont_none, accept_cont_none]
      exact Option.or_self
    | mul r₁₁ r₁₂ =>
      rw [accept, accept]
      simp_rw [←accept_mul_def]
      rw [accept_cont_none]
    | .star r false =>
      rw [accept, accept_suffix (r.star _) _ none]

      have hr₂_none :
        (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' fun l' ↦ none else none) =
        (fun l' ↦ none) := by
        funext l
        split_ifs with hl
        · rw [accept_cont_none]
        · rfl

      rw [hr₂_none, accept_cont_none]
    | .star r true =>
      rw [accept, accept_suffix (r.star _) _ none]

      have hr₂_none :
        (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' fun l' ↦ none else none) =
        (fun l' ↦ none) := by
        funext l
        split_ifs with hl
        · rw [accept_cont_none]
        · rfl

      rw [hr₂_none, accept_cont_none]
  | .star r false => by
    rw [accept]
    simp only [Loc.right, Option.or_none]

    have star_none :
      (fun loc' ↦ if loc'.2.length < s₂.length then (r.star false).accept loc' fun l' ↦ none else none) =
      (fun loc' ↦ none) := by
      funext l
      split_ifs with hl
      · rw [accept_cont_none]
      · rfl

    rw [star_none, accept_cont_none]
  | .star r true => by
    rw [accept]
    simp only [Loc.right, Option.none_or]

    have lazy_star_none :
      (fun loc' ↦ if loc'.2.length < s₂.length then (r.star true).accept loc' fun l' ↦ none else none) =
      (fun loc' ↦ none) := by
      funext l
      split_ifs with hl
      · rw [accept_cont_none]
      · rfl

    rw [lazy_star_none, accept_cont_none]
termination_by (s₂.length, r.size, r.left.size)
decreasing_by
  any_goals decreasing_tactic
  · apply Prod.Lex.right
    apply Prod.Lex.right' <;> (simp; omega)
  · apply Prod.Lex.right'
    exact hl
    apply Prod.Lex.left
    simp
  · apply Prod.Lex.right'
    exact hl
    apply Prod.Lex.left
    simp

theorem accept_nil_not_nullable {r : Regex α} {s : List σ} {k : Loc σ → Option (Loc σ)} (hr : ¬r.nullable) :
  r.accept (s, []) k = none :=
  match r with
  | epsilon => by simp at hr
  | pred c => by rw [accept]
  | plus r₁ r₂ => by
    simp at hr
    rw [accept, Option.or_eq_none]
    rw [accept_nil_not_nullable, accept_nil_not_nullable]
    simp only [and_self]
    simp [hr.right]
    simp [hr.left]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      rw [accept, accept]
      simp at hr
      rw [accept_nil_not_nullable]
      simp [hr]
    | pred c => rw [accept, accept]
    | plus r₁₁ r₁₂ =>
      rw [accept, accept]
      rw [←accept_mul_def, ←accept_mul_def]
      rw [accept_nil_not_nullable, accept_nil_not_nullable]
      exact Option.or_self
      simp_all
      simp_all
    | mul r₁₁ r₁₂ =>
      rw [accept, accept]
      simp_rw [←accept_mul_def]
      rw [accept_nil_not_nullable]
      simp at *
      tauto
    | .star r false =>
      rw [accept, accept]
      simp at *
      rw [@accept_nil_not_nullable r₂, accept_cont_none]
      simp only [and_self]
      simp [hr]
    | .star r true =>
      rw [accept, accept]
      simp at *
      rw [@accept_nil_not_nullable r₂, accept_cont_none]
      simp only [and_self]
      simp [hr]
  | .star _ _ => by simp at hr
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_nil_nullable {r : Regex α} {s : List σ} {k : Loc σ → Option (Loc σ)} (hr : r.nullable) :
  r.accept (s, []) k = k (s, []) :=
  match r with
  | epsilon => by rw [accept]
  | pred _ => by simp at hr
  | plus r₁ r₂ => by
    simp at hr
    rw [accept]
    cases hr with
    | inl hr =>
      rw [accept_nil_nullable hr]
      by_cases hr₂ : r₂.nullable
      · rw [accept_nil_nullable hr₂]
        exact Option.or_self
      · rw [accept_nil_not_nullable hr₂]
        exact Option.or_none
    | inr hr =>
      rw [accept_nil_nullable hr]
      by_cases hr₁ : r₁.nullable
      · rw [accept_nil_nullable hr₁]
        exact Option.or_self
      · rw [accept_nil_not_nullable hr₁]
        exact Option.none_or
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp at hr
      rw [accept, accept]
      rw [accept_nil_nullable hr]
    | pred c => simp at hr
    | plus r₁₁ r₁₂ =>
      simp at hr
      rw [accept, accept]
      repeat rw [←accept_mul_def]
      rcases hr with ⟨hr₁, hr₂⟩
      cases hr₁ with
      | inl hr₁ =>
        rw [accept_nil_nullable]
        by_cases hr₁₂ : r₁₂.nullable
        · rw [accept_nil_nullable]
          exact Option.or_self
          simp [hr₁₂, hr₂]
        · rw [accept_nil_not_nullable]
          exact Option.or_none
          simp [hr₁₂]
        simp [hr₁, hr₂]
      | inr hr₁ =>
        nth_rw 2 [accept_nil_nullable]
        by_cases hr₁₁ : r₁₁.nullable
        · rw [accept_nil_nullable]
          exact Option.or_self
          simp [hr₁₁, hr₂]
        · rw [accept_nil_not_nullable]
          exact Option.none_or
          simp [hr₁₁]
        simp [hr₁, hr₂]
    | mul r₁₁ r₁₂ =>
      rw [accept, accept]
      simp_rw [←accept_mul_def]
      rw [accept_nil_nullable]
      simp at hr
      simp [hr]
    | .star r false =>
      simp at hr
      rw [accept, accept_nil_nullable, accept_nil_nullable]
      exact hr
      rw [nullable]
    | .star r true =>
      simp at hr
      rw [accept, accept_nil_nullable, accept_nil_nullable]
      exact hr
      rw [nullable]
  | .star r false => by
    rw [accept]
    simp
    rw [accept_cont_none]
    exact Option.none_or
  | .star r true => by
    rw [accept]
    simp
    rw [accept_cont_none]
    exact Option.or_none
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)
