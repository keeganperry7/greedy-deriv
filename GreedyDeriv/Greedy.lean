import GreedyDeriv.Regex
import Mathlib.Tactic

variable {α : Type u} [DecidableEq α]

open Regex

def Regex.accept : Regex α → Loc α → (Loc α → Option (Loc α)) → Option (Loc α)
  | zero, _, _ => none
  | one, loc, k => k loc
  | char _, (_, []), _ => none
  | char c, (u, d::v), k => if c = d then k (d::u, v) else none
  | plus r₁ r₂, loc, k => (r₁.accept loc k).or (r₂.accept loc k)
  | mul r₁ r₂, loc, k => r₁.accept loc (fun loc' => r₂.accept loc' k)
  | star r, loc, k => (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then r.star.accept loc' k else none)).or (k loc)
termination_by r loc => (r.size, loc.right.length)

def Regex.gmatch : Regex α → List α → Option (Loc α)
  | r, s => r.accept ([], s) some

theorem accept_mul_def (r₁ r₂ : Regex α) (loc : Loc α) (k : Loc α → Option (Loc α)) :
  (r₁.mul r₂).accept loc k = (r₁.accept loc (fun loc' => r₂.accept loc' k)) := by
  rw [accept]

theorem if_cond {α : Type u} (n m : Nat) (x y : α) :
  (if n ≤ m then if n ≤ m + 1 then x else y else y) = if n ≤ m then x else y := by
  split_ifs with h₁ h₂
  · rfl
  · absurd h₂
    apply Nat.le_succ_of_le
    exact h₁
  · rfl

theorem if_cond' {α : Type u} (x y z : Nat) (a b : α) (h : y < z) :
  (if x ≤ y then if x < z then a else b else b) = if x ≤ y then a else b := by
  split_ifs with h₁ h₂
  · rfl
  · absurd h₂
    rw [Nat.le_iff_lt_or_eq] at h₁
    cases h₁ with
    | inl h₁ =>
      apply Nat.lt_trans
      exact h₁
      exact h
    | inr h₂ =>
      rw [h₂]
      exact h
  · rfl

theorem accept_suffix (r : Regex α) (k : Loc α → Option (Loc α)) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length ≤ s₂.length then k l' else none) := by
  induction r generalizing s₁ s₂ k with
  | zero => simp only [accept]
  | one => simp [accept]
  | char c =>
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    rw [ih₁, ih₂]
    rfl
  | mul r₁ r₂ ih₁ ih₂ =>
    cases r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      rw [ih₂]
      rfl
    | char c =>
      simp [accept]
      cases s₂ with
      | nil => simp [accept]
      | cons x xs =>
        simp [accept]
        split_ifs with hc
        · rw [ih₂]
          nth_rw 2 [ih₂]
          simp
          simp_rw [if_cond _ xs.length _ none]
        · rfl
    | plus r₁' r₂' =>
      simp [accept]
      repeat rw [←accept_mul_def]
      -- Structural induction on r.size
      -- rw [accept_suffix (r₁'.mul r₂)]
      -- rw [accept_suffix (r₂'.mul r₂)]
      -- simp
      sorry
    | mul r₁' r₂' =>
      simp [accept]
      simp_rw [←accept_mul_def r₂' r₂]
      repeat rw [←accept_mul_def]
      -- Structural induction on r.left.size
      -- rw [accept_suffix (r₁'.mul (r₂'.mul r₂))]
      -- simp
      sorry
    | star r => sorry
  | star r ih =>
    -- True because of the restrictions on s₂
    sorry

theorem accept_not_nullable (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hn : ¬r.nullable) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else none) := by
  induction r with
  | zero => simp [accept]
  | one => simp at hn
  | char c =>
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn ih₁ ih₂
    simp [accept]
    rw [ih₁ hn.left, ih₂ hn.right]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    cases r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      simp at hn ih₂
      rw [ih₂]
      exact hn
    | char c =>
      cases s₂ with
      | nil => simp [accept]
      | cons x xs =>
        simp [accept]
        split_ifs with hc
        · simp_rw [Nat.lt_succ]
          rw [accept_suffix]
          simp
        · rfl
    | plus r₁₁ r₁₂ =>
      simp at hn ih₁ ih₂
      simp [accept]
      -- True by structural induction over r.size, since (r₁₁.mul r₂).size < ((r₁₁.plus r₁₂).mul r₂).size
      -- Need to show that ¬(r₁₁.mul r₂).nullable ∧ ¬(r₁₂.mul r₂).nullable
      sorry
    | mul r₁₁ r₁₂ =>
      -- True by structural induction over r.left.size, since (r₁₁.mul (r₁₂.mul r₂)).size < ((r₁₁.mul r₁₂).mul r₂).size
      -- Also have that (r₁₁.mul (r₁₂.mul r₂)).nullable
      sorry
    | star r =>
      -- True because of the restrictions on s₂
      sorry
  | star => simp at hn

theorem accept_nil_none (r : Regex α) (s : List α) (k : Loc α → Option (Loc α)) :
  ¬r.nullable ∨ k (s, []) = none →
  r.accept (s, []) k = none := by
  intro h
  induction r generalizing k with
  | zero => simp [accept]
  | one =>
    simp at h
    simp [accept]
    exact h
  | char => simp [accept]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    simp at ih₁ ih₂ h
    cases h with
    | inl h =>
      constructor
      · apply ih₁
        exact Or.inl h.left
      · apply ih₂
        exact Or.inl h.right
    | inr h =>
      constructor
      · apply ih₁
        exact Or.inr h
      · apply ih₂
        exact Or.inr h
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at h
    simp [accept]
    cases h with
    | inl h =>
      by_cases hr : r₁.nullable
      · apply h at hr
        apply ih₁
        right
        apply ih₂
        simp
        exact Or.inl hr
      · apply ih₁
        exact Or.inl hr
    | inr h =>
      apply ih₁
      right
      apply ih₂
      exact Or.inr h
  | star r ih =>
    simp at h
    simp [accept]
    constructor
    · apply ih
      simp
    · exact h

theorem accept_nil_some (r : Regex α) (s : List α) (k : Loc α → Option (Loc α)) :
  r.nullable ∧ k (s, []) = some (s, []) →
  r.accept (s, []) k = some (s, []) := by
  intro ⟨hr, hk⟩
  induction r generalizing k with
  | zero => simp at hr
  | one =>
    simp [accept]
    exact hk
  | char => simp at hr
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    simp at hr
    cases hr with
    | inl hr => exact Or.inl (ih₁ k hr hk)
    | inr hr =>
      by_cases hr' : r₁.nullable
      · exact Or.inl (ih₁ k hr' hk)
      · refine Or.inr ⟨?_, ih₂ k hr hk⟩
        apply accept_nil_none
        exact Or.inl hr'
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    simp at hr
    apply ih₁
    exact hr.left
    apply ih₂
    exact hr.right
    exact hk
  | star r _ =>
    simp [accept]
    right
    refine ⟨?_, hk⟩
    apply accept_nil_none
    simp

theorem accept_deriv_some (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  r.nullable ∧ (r.prune.deriv x).accept (x::s₁, s₂) k = none ∧ k (s₁, x::s₂) = some (s₁, x::s₂) →
  r.accept (s₁, x::s₂) k = some (s₁, x::s₂) := by
  intro ⟨hr, h, hk⟩
  induction r with
  | zero => simp at hr
  | one =>
    simp [accept]
    exact hk
  | char => simp at hr
  | plus r₁ r₂ ih₁ ih₂ =>
    sorry
  | mul => sorry
  | star => sorry

theorem accept_deriv_none' {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : ¬r.nullable) :
  (r.prune'.deriv x).accept (x::s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = none := by
  sorry

theorem accept_deriv_none (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  ¬r.nullable ∧ (r.prune.deriv x).accept (x::s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = none := by
  intro ⟨hn, h⟩
  induction r with
  | zero => simp [accept]
  | one => simp at hn
  | char c =>
    simp [accept] at *
    intro hc
    simp [hc] at h
    simp [accept] at h
    exact h
  | plus r₁ r₂ ih₁ ih₂ =>
    rw [prune_not_nullable hn] at h
    simp [accept] at h
    let ⟨h₁, h₂⟩ := h
    simp at hn
    rw [prune_not_nullable (by simp [hn.left])] at ih₁
    rw [prune_not_nullable (by simp [hn.right])] at ih₂
    apply ih₁ at h₁
    apply ih₂ at h₂
    simp [accept]
    exact ⟨h₁, h₂⟩
    simp [hn.right]
    simp [hn.left]
  | mul => sorry
  | star => simp at hn

theorem accept_deriv' (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) :
  (r.prune'.deriv x).accept (x::s₁, s₂) k = some loc →
  r.accept (s₁, x::s₂) k = some loc := by
  intro h
  induction r generalizing k with
  | zero => simp [accept] at *
  | one => simp [accept] at *
  | char c =>
    simp [accept] at *
    split_ifs at h with hc
    · simp [hc]
      simp [accept] at h
      exact h
    · simp [accept] at h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    rw [prune'] at h
    split_ifs at h with hn hn'
    · simp [accept] at h
    · apply ih₁ at h
      exact Or.inl h
    · simp [Regex.deriv, accept] at h
      cases h with
      | inl h =>
        apply ih₁ at h
        exact Or.inl h
      | inr h =>
        let ⟨h₁, h₂⟩ := h
        apply ih₂ at h₂
        refine Or.inr ⟨?_, h₂⟩
        apply accept_deriv_none'
        exact hn'
        exact h₁
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [Regex.prune'.eq_def] at h
    simp at h
    split_ifs at h with hn
    · simp [accept] at h
    · cases r₁ with
      | zero =>
        simp [accept] at h
      | one =>
        simp at h
        apply ih₂ at h
        simp [accept]
        exact h
      | char c =>
        simp at h
        split_ifs at h with hc
        · simp [accept] at h
          simp [accept, hc]
          -- TODO: Show r.accept l k = r.prune'.accept l k
          sorry
        · simp [accept] at h
      | plus r₁₁ r₁₂ =>
        simp at h
        split_ifs at h with hn hn'
        · simp [accept] at h
        · simp [accept]
          -- True, by structural induction, since r₁₁.mul r₂ < (r₁₁.plus r₁₂).mul r₂
          -- apply accept_deriv' at h
          -- simp [accept] at h
          -- exact Or.inl h
          sorry
        · simp [Regex.deriv] at h
          simp [accept] at h
          cases h with
          | inl h =>
            simp [accept]
            -- Again, true by structural induction, since r₁₁.mul r₂ < (r₁₁.plus r₁₂).mul r₂
            -- apply accept_deriv' at h
            -- simp [accept] at h
            -- exact Or.inl h
            sorry
          | inr h =>
            let ⟨h₁, h₂⟩ := h
            simp [accept]
            -- True, by structural induction, since r₁₂.mul r₂ < (r₁₁.plus r₁₂).mul r₂
            -- Also have that (r₁₁.mul r₂).accept l k = none by h₁
            -- apply accept_deriv' at h₁
            -- simp [accept] at h₁
            refine Or.inr ⟨?_, ?_⟩
            · have h := accept_deriv_none' (by simp [hn']) h₁
              simp [accept] at h
              exact h
            · -- exact h₁
              sorry
      | mul r₁₁ r₁₂ =>
        simp at h
        simp [accept]
        -- True, by structural induction, since r₁₁.mul (r₁₂.mul r₂) < (r₁₁.mul r₁₂).mul r₂
        -- apply accept_deriv' at h
        -- simp [accept] at h
        -- exact h
        sorry
      | star => sorry
  | star r ih =>
    simp at h
    sorry

-- Maybe need to induct over r and s₂
theorem accept_deriv (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = some loc →
  r.accept (s₁, x::s₂) k = some loc := by
  intro h
  induction r generalizing k with
  | zero => simp [accept] at *
  | one => simp [accept] at *
  | char c =>
    simp [accept] at *
    split_ifs at h with hc
    · simp [hc]
      simp [accept] at h
      exact h
    · simp [accept] at h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    by_cases hr : r₁.highNullable
    · rw [prune_plus_left_highNullable hr] at h
      simp [accept] at h
    · by_cases hr' : (r₁.plus r₂).nullable
      · simp at hr'
        cases hr' with
        | inl hr' =>
          rw [prune_plus_left_nullable hr' hr] at h
          apply ih₁ at h
          exact Or.inl h
        | inr hr' =>
          by_cases hr'' : r₁.nullable
          · rw [prune_plus_left_nullable hr'' hr] at h
            apply ih₁ at h
            exact Or.inl h
          · rw [prune_plus_right_nullable hr'' hr' hr] at h
            simp [accept] at h
            cases h with
            | inl h =>
              apply ih₁ at h
              exact Or.inl h
            | inr h =>
              let ⟨h₁, h₂⟩ := h
              apply ih₂ at h₂
              refine Or.inr ⟨?_, h₂⟩
              apply accept_deriv_none
              exact ⟨hr'', h₁⟩
      · rw [prune_not_nullable hr'] at h
        simp [accept] at h
        simp at hr'
        cases h with
        | inl h =>
          rw [prune_not_nullable] at ih₁
          apply ih₁ at h
          exact Or.inl h
          simp
          exact hr'.left
        | inr h =>
          let ⟨h₁, h₂⟩ := h
          rw [prune_not_nullable (by simp [hr'.right])] at ih₂
          apply ih₂ at h₂
          refine Or.inr ⟨?_, h₂⟩
          apply accept_deriv_none
          rw [prune_not_nullable (by simp [hr'.left])]
          exact ⟨by simp [hr'.left], h₁⟩
  | mul r₁ r₂ ih₁ ih₂ => sorry
  | star r ih =>
    by_cases hr : r.highNullable
    · rw [prune_star_highNullable hr] at h
      simp [accept] at h
    · rw [prune_star_not_highNullable hr] at h
      simp [Regex.deriv] at h
      rw [accept] at h

      by_cases hr' : r.nullable
      · -- Need to do a cases over r
        sorry
      · rw [prune_not_nullable hr'] at ih
        apply ih at h
        rw [accept]
        simp
        left
        -- True since ¬r.nullable, but also true in general
        -- i.e. (r.mul r.star).accept (s₁, s₂) k = some loc → r.star.accept (s₁, s₂) k = some loc
        -- difficulty is showing when r captures some input, since then the condition is satisfied
        rw [accept_not_nullable] at h
        exact h
        exact hr'

theorem zero_accept (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  zero.accept (s₁, s₂) k = none := by
  simp [accept]

theorem one_accept (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  one.accept (s₁, s₂) k = k (s₁, s₂) := by
  simp [accept]

theorem char_nil_accept (c : α) (s : List α) (k : Loc α → Option (Loc α)) :
  (char c).accept (s, []) k = none := by
  simp [accept]

theorem char_accept (c d : α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  (char c).accept (s₁, d::s₂) k = if c = d then k (d::s₁, s₂) else none := by
  simp [accept]

theorem add_accept_none (r₁ r₂ : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  (r₁.plus r₂).accept (s₁, s₂) k = none ↔
  r₁.accept (s₁, s₂) k = none ∧ r₂.accept (s₁, s₂) k = none := by
  simp [accept]

theorem add_accept (r₁ r₂ : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) :
  (r₁.plus r₂).accept (s₁, s₂) k = some loc ↔
  r₁.accept (s₁, s₂) k = some loc ∨ (r₁.accept (s₁, s₂) k = none ∧ (r₂.accept (s₁, s₂) k = some loc)) := by
  simp [accept]

theorem star_accept_none (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  r.star.accept (s₁, s₂) k = none → k (s₁, s₂) = none := by
  intro h
  rw [accept] at h
  simp at h
  exact h.right

theorem star_accept (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) :
  r.star.accept (s₁, s₂) k = some loc →
  (r.mul (r.star)).accept (s₁, s₂) k = some loc ∨ ((r.mul (r.star)).accept (s₁, s₂) k = none ∧ k (s₁, s₂) = some loc) := by
  intro h
  rw [accept] at h
  simp at h
  cases h with
  | inl h =>
    sorry
  | inr h =>
    right
    refine ⟨?_, h.right⟩
    sorry
