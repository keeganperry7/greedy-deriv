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

def Regex.gmatch : Regex α → List σ → Option (Loc σ)
  | r, s => r.accept ([], s) some

theorem accept_mul_def (r₁ r₂ : Regex α) (loc : Loc σ) (k : Loc σ → Option (Loc σ)) :
  (r₁.mul r₂).accept loc k = (r₁.accept loc (fun loc' => r₂.accept loc' k)) := by
  rw [accept]

@[simp]
theorem accept_bot (loc : Loc σ) (k : Loc σ → Option (Loc σ)) :
  (@pred α ⊥).accept loc k = none := by
  match loc with
  | ⟨_, []⟩ => simp [accept]
  | ⟨_, x::xs⟩ => simp [accept]

theorem accept_matches (r : Regex α) (l l' : Loc σ) (k : Loc σ → Option (Loc σ)) :
  r.accept l k = some l' → ∃ p, (r, l) → p ∧ k p = l' :=
  match r with
  | epsilon => by
    intro h
    simp [accept] at h
    exact ⟨l, PartialMatch.epsilon, h⟩
  | pred c => by
    intro h
    match l with
    | ⟨u, []⟩ =>
      simp [accept] at h
    | ⟨u, d::v⟩ =>
      simp [accept] at h
      refine ⟨⟨d::u, v⟩, PartialMatch.pred h.left, h.right⟩
  | plus r₁ r₂ => by
    intro h
    simp [accept] at h
    cases h with
    | inl h =>
      apply accept_matches at h
      rcases h with ⟨p, h, hk⟩
      exact ⟨p, PartialMatch.plus_left h, hk⟩
    | inr h =>
      rcases h with ⟨_, h⟩
      apply accept_matches at h
      rcases h with ⟨p, h, hk⟩
      exact ⟨p, PartialMatch.plus_right h, hk⟩
  | mul r₁ r₂ => by
    intro h
    simp [accept] at h
    apply accept_matches at h
    rcases h with ⟨p, h₁, h₂⟩
    apply accept_matches at h₂
    rcases h₂ with ⟨p', h₂, hk⟩
    exact ⟨p', PartialMatch.mul h₁ h₂, hk⟩
  | .star r false => by
    intro h
    rw [accept] at h
    simp at h
    cases h with
    | inl h =>
      apply accept_matches at h
      rcases h with ⟨p, h₁, h₂⟩
      simp at h₂
      rcases h₂ with ⟨hp, h₂⟩
      apply accept_matches at h₂
      rcases h₂ with ⟨p', h₂, hk⟩
      refine ⟨p', PartialMatch.stars hp h₁ h₂, hk⟩
    | inr h =>
      rcases h with ⟨_, h⟩
      exact ⟨l, PartialMatch.star_nil, h⟩
  | .star r true => by
    intro h
    rw [accept] at h
    simp at h
    cases h with
    | inl h => exact ⟨l, PartialMatch.star_nil, h⟩
    | inr h =>
      rcases h with ⟨_, h⟩
      apply accept_matches at h
      rcases h with ⟨p, h₁, h₂⟩
      simp at h₂
      rcases h₂ with ⟨hp, h₂⟩
      apply accept_matches at h₂
      rcases h₂ with ⟨p', h₂, hk⟩
      exact ⟨p', PartialMatch.stars hp h₁ h₂, hk⟩
termination_by (r.size, l.right.length)

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
    simp [accept]
    rw [accept_suffix r₁ _ x]
    nth_rw 2 [accept_suffix r₁ _ x]
    congr
    funext l
    split_ifs with hl
    · rw [accept_suffix r₂ _ x]
      nth_rw 2 [accept_suffix r₂ _ x]
      congr
      funext l'
      split_ifs with hl' hn
      · rfl
      · absurd hn
        exact Nat.le_trans hl' hl
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
termination_by (r.size, s₂.length)

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

theorem accept_nil {r : Regex α} {s : List σ} {k : Loc σ → Option (Loc σ)} :
  r.accept (s, []) k = if r.nullable then k (s, []) else none := by
  induction r generalizing k with
  | epsilon => simp [accept]
  | pred c => simp [accept]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    split_ifs with hn
    · cases hn with
      | inl hn =>
        rw [hn] at ih₁
        simp at ih₁
        split_ifs at ih₂
        · rw [ih₁, ih₂, Option.or_self]
        · rw [ih₁, ih₂, Option.or_none]
      | inr hn =>
        rw [hn] at ih₂
        simp at ih₂
        split_ifs at ih₁
        · rw [ih₁, ih₂, Option.or_self]
        · rw [ih₁, ih₂, Option.none_or]
    · simp at hn
      rw [hn.left] at ih₁
      rw [hn.right] at ih₂
      simp at ih₁ ih₂
      rw [ih₁, ih₂, Option.or_self]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    split_ifs with hn
    · rw [hn.left] at ih₁
      rw [hn.right] at ih₂
      simp at ih₁ ih₂
      rw [ih₁, ih₂]
    · split_ifs at ih₁ with hn₁
      · rw [ih₁]
        simp [hn₁] at hn
        rw [ih₂, hn]
        rfl
      · rw [ih₁]
  | star r lazy? ih =>
    cases lazy? with
    | false =>
      rw [accept]
      simp
      split_ifs at ih
      · rw [ih, Option.none_or]
      · rw [ih, Option.none_or]
    | true =>
      rw [accept]
      simp
      split_ifs at ih
      · rw [ih, Option.or_none]
      · rw [ih, Option.or_none]
