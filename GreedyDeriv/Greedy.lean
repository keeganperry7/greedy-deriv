import GreedyDeriv.Regex
import Mathlib.Tactic

variable {α : Type} [DecidableEq α]

open Regex

/-- Defintion 4 -/
def Regex.accept : Regex α → Loc α → (Loc α → Option (Loc α)) → Option (Loc α)
  | emptyset, _, _ => none
  | epsilon, loc, k => k loc
  | char _, (_, []), _ => none
  | char c, (u, d::v), k => if c = d then k (d::u, v) else none
  | plus r₁ r₂, loc, k => (r₁.accept loc k).or (r₂.accept loc k)
  | mul r₁ r₂, loc, k => r₁.accept loc (fun loc' => r₂.accept loc' k)
  | star r false, loc, k => (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then (r.star false).accept loc' k else none)).or (k loc)
  | star r true, loc, k => (k loc).or (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then (r.star true).accept loc' k else none))
  | lookahead r, loc, k =>
    if (r.accept loc some).isSome
      then k loc
      else none
termination_by r loc => (r.size, loc.right.length)

/-- Definition 5 -/
def Regex.gmatch : Regex α → Loc α → Option (Loc α)
  | r, l => r.accept l some

theorem accept_mul_def (r₁ r₂ : Regex α) (loc : Loc α) (k : Loc α → Option (Loc α)) :
  (r₁.mul r₂).accept loc k = (r₁.accept loc (fun loc' => r₂.accept loc' k)) := by
  rw [accept]

/-- Theorem 6 -/
theorem accept_matches (r : Regex α) (l l' : Loc α) (k : Loc α → Option (Loc α)) :
  r.accept l k = some l' → ∃ p, (r, l) → p ∧ k p = l' :=
  match r with
  | emptyset => by simp [accept]
  | epsilon => by
    intro h
    simp [accept] at h
    exact ⟨l, PartialMatch.epsilon, h⟩
  | char c => by
    intro h
    match l with
    | ⟨u, []⟩ =>
      simp [accept] at h
    | ⟨u, d::v⟩ =>
      simp [accept] at h
      rw [h.left]
      refine ⟨⟨d::u, v⟩, PartialMatch.char, h.right⟩
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
      refine ⟨p', PartialMatch.stars h₁ h₂, hk⟩
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
      exact ⟨p', PartialMatch.stars h₁ h₂, hk⟩
  | lookahead r => by
    intro h
    simp [accept] at h
    rcases h with ⟨h, hk⟩
    rw [Option.isSome_iff_exists] at h
    rcases h with ⟨p, h⟩
    apply accept_matches at h
    simp at h
    exact ⟨l, PartialMatch.lookahead h, hk⟩
termination_by (r.size, l.right.length)

/-- Corollary 7 -/
theorem gmatch_matches (r : Regex α) (l l' : Loc α) :
  r.gmatch l = some l' → (r, l) → l' := by
  intro h
  rw [gmatch] at h
  apply accept_matches at h
  simp only [Option.some_inj, exists_eq_right] at h
  exact h

/-- Lemma 8 -/
theorem accept_suffix (r : Regex α) {l : Loc α} (k : Loc α → Option (Loc α)) (x : Option (Loc α)) :
  r.accept l k = r.accept l (fun l' => if l'.right.length ≤ l.right.length then k l' else x) :=
  match r with
  | emptyset => by simp [accept]
  | epsilon => by
    simp [accept]
  | char c => by
    match l with
    | ⟨_, []⟩ => simp [accept]
    | ⟨u, d::v⟩ => simp [accept]
  | plus r₁ r₂ => by
    simp only [accept, Loc.right]
    rw [accept_suffix r₁, accept_suffix r₂]
    rfl
  | mul r₁ r₂ => by
    simp only [accept, Loc.right]
    rw [accept_suffix r₁ _ x]
    rw [accept_suffix r₁ (fun loc' ↦ r₂.accept loc' _) x]
    congr
    funext l
    split_ifs with hl
    · rw [accept_suffix r₂ _ x]
      rw [accept_suffix r₂ (fun l' ↦ if l'.2.length ≤ _ then _ else _) x]
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
    simp only [Loc.right, le_refl, reduceIte]
    congr
    funext loc'
    split_ifs with hl
    · rw [accept_suffix (r.star _) _ x]
      rw [accept_suffix (r.star _) (fun l' ↦ if l'.2.length ≤ _ then _ else _) x]
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
    simp only [Loc.right, le_refl, reduceIte]
    congr
    funext loc'
    split_ifs with hl
    · rw [accept_suffix (r.star _) _ x]
      rw [accept_suffix (r.star _) (fun l' ↦ if l'.2.length ≤ _ then _ else _) x]
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
  | lookahead r => by
    simp [accept]
termination_by (r.size, l.right.length)

/-- Lemma 9 -/
theorem accept_nullable (r : Regex α) (l : Loc α) (k : Loc α → Option (Loc α)) (hn : r.nullable l) (hk : (k l).isSome) :
  (r.accept l k).isSome := by
  induction r generalizing k with
  | emptyset => simp at hn
  | epsilon =>
    rw [accept]
    exact hk
  | char c => simp only [nullable, Bool.false_eq_true] at hn
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
  | lookahead r =>
    simp [accept]
    simp [nullable] at hn
    sorry

/-- Theorem 10 -/
theorem accept_nil {r : Regex α} {s : List α} {k : Loc α → Option (Loc α)} :
  r.accept (s, []) k = if r.nullable (s, []) then k (s, []) else none := by
  induction r generalizing k with
  | emptyset => simp [accept]
  | epsilon => simp [accept]
  | char c => simp [accept]
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
  | lookahead r =>
    simp [accept]
    sorry
