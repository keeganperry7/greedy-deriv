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
  | star r, loc, k => (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then r.star.accept loc' k else none)).or (k loc)
  | lazy_star r, loc, k => (k loc).or (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then r.lazy_star.accept loc' k else none))
termination_by r loc => (r.size, loc.right.length)

def Regex.gmatch : Regex α → List σ → Option (Loc σ)
  | r, s => r.accept ([], s) some

theorem accept_mul_def (r₁ r₂ : Regex α) (loc : Loc σ) (k : Loc σ → Option (Loc σ)) :
  (r₁.mul r₂).accept loc k = (r₁.accept loc (fun loc' => r₂.accept loc' k)) := by
  rw [accept]

theorem accept_star_def (r : Regex α) (loc : Loc σ) (k : Loc σ → Option (Loc σ)) :
  r.star.accept loc k = (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then r.star.accept loc' k else none)).or (k loc) := by
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
    simp [accept]
    rw [accept_suffix r₁, accept_suffix r₂]
    rfl
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
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
          simp
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
      simp [accept]
      repeat rw [←accept_mul_def]
      rw [accept_suffix (r₁₁.mul r₂) _ x]
      rw [accept_suffix (r₁₂.mul r₂) _ x]
      rfl
    | mul r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def r₁₂ r₂]
      repeat rw [←accept_mul_def]
      rw [accept_suffix (r₁₁.mul (r₁₂.mul r₂)) _ x]
      rfl
    | .star r =>
      rw [accept, accept, accept, accept]
      simp
      rw [accept_suffix r₂ _ x]
      simp
      congr
      funext loc'
      split_ifs with hl
      · rw [accept_suffix r.star _ x]
        nth_rw 2 [accept_suffix r.star _ x]
        simp
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
    | lazy_star r =>
      rw [accept, accept, accept, accept]
      simp
      rw [accept_suffix r₂ _ x]
      simp
      congr
      funext loc'
      split_ifs with hl
      · rw [accept_suffix r.lazy_star _ x]
        nth_rw 2 [accept_suffix r.lazy_star _ x]
        simp
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
  | .star r => by
    rw [accept, accept]
    simp
    congr
    funext loc'
    split_ifs with hl
    · rw [accept_suffix r.star _ x]
      nth_rw 2 [accept_suffix r.star _ x]
      simp
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
  | lazy_star r => by
    rw [accept, accept]
    simp
    congr
    funext loc'
    split_ifs with hl
    · rw [accept_suffix r.lazy_star _ x]
      nth_rw 2 [accept_suffix r.lazy_star _ x]
      simp
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
    simp [accept]
    exact hk
  | pred c => simp at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    cases hn with
    | inl hn =>
      simp [accept]
      left
      apply ih₁
      exact hn
      exact hk
    | inr hn =>
      simp [accept]
      right
      apply ih₂
      exact hn
      exact hk
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [accept]
    apply ih₁
    exact hn.left
    apply ih₂
    exact hn.right
    exact hk
  | star r _ =>
    rw [accept]
    simp
    exact Or.inr hk
  | lazy_star r =>
    rw [accept]
    simp
    exact Or.inl hk

theorem accept_not_nullable (r : Regex α) (s₁ s₂ : List σ) (k : Loc σ → Option (Loc σ)) (x : Option (Loc σ)) (hn : ¬r.nullable) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else x) :=
  match r with
  | epsilon => by simp at hn
  | pred c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ => by
    simp at hn
    simp [accept]
    rw [accept_not_nullable r₁ _ _ _ x]
    rw [accept_not_nullable r₂ _ _ _ x]
    rfl
    simp [hn.right]
    simp [hn.left]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp at hn
      simp [accept]
      rw [accept_not_nullable r₂ _ _ _ x]
      rfl
      simp [hn]
    | pred c =>
      cases s₂ with
      | nil => simp [accept]
      | cons y ys =>
        simp [accept]
        split_ifs with hc
        · simp_rw [Nat.lt_succ]
          rw [accept_suffix _ _ x]
          simp
        · rfl
    | plus r₁₁ r₁₂ =>
      simp at hn
      simp [accept]
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
      simp [accept]
      simp_rw [←accept_mul_def]
      apply accept_not_nullable (r₁₁.mul (r₁₂.mul r₂))
      simp at hn
      simp
      exact hn
    | .star r =>
      simp at hn
      rw [accept, accept, accept, accept]
      simp
      rw [accept_not_nullable r₂ _ _ k x]
      simp
      congr
      funext loc'
      split_ifs with hl
      · rw [accept_suffix r.star _ x]
        nth_rw 2 [accept_suffix r.star _ x]
        simp
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ x]
          nth_rw 2 [accept_suffix r₂ _ x]
          simp
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
    | lazy_star r =>
      simp at hn
      rw [accept, accept, accept, accept]
      simp
      rw [accept_not_nullable r₂ _ _ k x]
      simp
      congr
      funext loc'
      split_ifs with hl
      · rw [accept_suffix r.lazy_star _ x]
        nth_rw 2 [accept_suffix r.lazy_star _ x]
        simp
        congr
        funext l
        split_ifs with h₁
        · rw [accept_suffix r₂ _ x]
          nth_rw 2 [accept_suffix r₂ _ x]
          simp
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
  | .star r => by simp at hn
  | lazy_star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_cont_none (r : Regex α) (s₁ s₂ : List σ) :
  r.accept (s₁, s₂) (fun _ ↦ none) = none :=
  match r with
  | epsilon => by simp [accept]
  | pred c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ => by
    simp [accept]
    rw [accept_cont_none, accept_cont_none]
    simp
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      rw [accept_cont_none]
    | pred c =>
      cases s₂ with
      | nil => simp [accept]
      | cons x xs =>
        simp [accept]
        rw [accept_cont_none]
        simp
    | plus r₁₁ r₁₂ =>
      simp [accept]
      rw [←accept_mul_def, ←accept_mul_def]
      rw [accept_cont_none, accept_cont_none]
      simp
    | mul r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def]
      rw [accept_cont_none]
    | .star r =>
      rw [accept, accept_suffix r.star _ none]

      have hr₂_none :
        (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' fun l' ↦ none else none) =
        (fun l' ↦ none) := by
        funext l
        split_ifs with hl
        · rw [accept_cont_none]
        · rfl

      rw [hr₂_none, accept_cont_none]
    | lazy_star r =>
      rw [accept, accept_suffix r.lazy_star _ none]

      have hr₂_none :
        (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' fun l' ↦ none else none) =
        (fun l' ↦ none) := by
        funext l
        split_ifs with hl
        · rw [accept_cont_none]
        · rfl

      rw [hr₂_none, accept_cont_none]
  | .star r => by
    rw [accept]
    simp

    have star_none :
      (fun loc' ↦ if loc'.2.length < s₂.length then r.star.accept loc' fun l' ↦ none else none) =
      (fun loc' ↦ none) := by
      funext l
      split_ifs with hl
      · rw [accept_cont_none]
      · rfl

    rw [star_none, accept_cont_none]
  | lazy_star r => by
    rw [accept]
    simp

    have lazy_star_none :
      (fun loc' ↦ if loc'.2.length < s₂.length then r.lazy_star.accept loc' fun l' ↦ none else none) =
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
  | pred c => by simp [accept]
  | plus r₁ r₂ => by
    simp at hr
    simp [accept]
    rw [accept_nil_not_nullable, accept_nil_not_nullable]
    simp
    simp [hr.right]
    simp [hr.left]
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp [accept]
      simp at hr
      rw [accept_nil_not_nullable]
      simp [hr]
    | pred c => simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      rw [←accept_mul_def, ←accept_mul_def]
      rw [accept_nil_not_nullable, accept_nil_not_nullable]
      simp
      simp_all
      simp_all
    | mul r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def]
      rw [accept_nil_not_nullable]
      simp at *
      tauto
    | .star r =>
      rw [accept, accept]
      simp at *
      rw [@accept_nil_not_nullable r₂, accept_cont_none]
      simp
      simp [hr]
    | lazy_star r =>
      rw [accept, accept]
      simp at *
      rw [@accept_nil_not_nullable r₂, accept_cont_none]
      simp
      simp [hr]
  | .star _ => by simp at hr
  | lazy_star _ => by simp at hr
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_nil_nullable {r : Regex α} {s : List σ} {k : Loc σ → Option (Loc σ)} (hr : r.nullable) :
  r.accept (s, []) k = k (s, []) :=
  match r with
  | epsilon => by simp [accept]
  | pred _ => by simp at hr
  | plus r₁ r₂ => by
    simp at hr
    simp [accept]
    cases hr with
    | inl hr =>
      rw [accept_nil_nullable hr]
      by_cases hr₂ : r₂.nullable
      · rw [accept_nil_nullable hr₂]
        simp
      · rw [accept_nil_not_nullable hr₂]
        simp
    | inr hr =>
      rw [accept_nil_nullable hr]
      by_cases hr₁ : r₁.nullable
      · rw [accept_nil_nullable hr₁]
        simp
      · rw [accept_nil_not_nullable hr₁]
        simp
  | mul r₁ r₂ => by
    match r₁ with
    | epsilon =>
      simp at hr
      simp [accept]
      rw [accept_nil_nullable hr]
    | pred c => simp at hr
    | plus r₁₁ r₁₂ =>
      simp at hr
      simp [accept]
      repeat rw [←accept_mul_def]
      let ⟨hr₁, hr₂⟩ := hr
      clear hr
      cases hr₁ with
      | inl hr₁ =>
        rw [accept_nil_nullable]
        by_cases hr₁₂ : r₁₂.nullable
        · rw [accept_nil_nullable]
          simp
          simp [hr₁₂, hr₂]
        · rw [accept_nil_not_nullable]
          simp
          simp [hr₁₂]
        simp [hr₁, hr₂]
      | inr hr₁ =>
        nth_rw 2 [accept_nil_nullable]
        by_cases hr₁₁ : r₁₁.nullable
        · rw [accept_nil_nullable]
          simp
          simp [hr₁₁, hr₂]
        · rw [accept_nil_not_nullable]
          simp
          simp [hr₁₁]
        simp [hr₁, hr₂]
    | mul r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def]
      rw [accept_nil_nullable]
      simp at hr
      simp [hr]
    | .star r =>
      simp at hr
      rw [accept, accept_nil_nullable, accept_nil_nullable]
      exact hr
      simp
    | lazy_star r =>
      simp at hr
      rw [accept, accept_nil_nullable, accept_nil_nullable]
      exact hr
      simp
  | .star r => by
    rw [accept]
    simp
    rw [accept_cont_none]
    simp
  | lazy_star r => by
    rw [accept]
    simp
    rw [accept_cont_none]
    simp
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)
