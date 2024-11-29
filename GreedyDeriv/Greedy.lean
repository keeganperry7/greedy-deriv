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
  | star r, loc, k => (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then r.star.accept loc' k else k loc)).or (k loc)
termination_by r loc => (r.size, loc.right.length)

def Regex.gmatch : Regex α → List α → Option (Loc α)
  | r, s => r.accept ([], s) some

theorem accept_mul_def (r₁ r₂ : Regex α) (loc : Loc α) (k : Loc α → Option (Loc α)) :
  (r₁.mul r₂).accept loc k = (r₁.accept loc (fun loc' => r₂.accept loc' k)) := by
  rw [accept]

theorem accept_star_def (r : Regex α) (loc : Loc α) (k : Loc α → Option (Loc α)) :
  r.star.accept loc k = (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then r.star.accept loc' k else k loc)).or (k loc) := by
  rw [accept]

theorem if_cond {α : Type u} (n m : Nat) (x y : α) :
  (if n ≤ m then if n ≤ m + 1 then x else y else y) = if n ≤ m then x else y := by
  split_ifs with h₁ h₂
  · rfl
  · absurd h₂
    apply Nat.le_succ_of_le
    exact h₁
  · rfl

theorem if_cond' {α : Type u} (y z : Nat) (a b : α) (h : y < z) :
  (fun x ↦ if x ≤ y then if x ≤ z then a else b else b) = (fun x ↦ if x ≤ y then a else b) := by
  ext x
  split_ifs with h₁ h₂
  · rfl
  · absurd h₂
    rw [Nat.le_iff_lt_or_eq] at h₁
    cases h₁ with
    | inl h₁ =>
      apply Nat.le_of_lt
      apply Nat.lt_trans
      exact h₁
      exact h
    | inr h₂ =>
      rw [h₂]
      apply Nat.le_of_lt
      exact h
  · rfl

theorem if_cond'' {α : Type u} (loc' : Loc α) (s₂ : List α) (k : Loc α → Option (Loc α)) (x : Option (Loc α)) (h : loc'.2.length < s₂.length) :
  (fun l' ↦ if l'.2.length ≤ loc'.2.length then if l'.2.length ≤ s₂.length then k l' else x else x) =
  (fun l' ↦ if l'.2.length ≤ loc'.2.length then k l' else x) := by
  ext l' t
  split_ifs with h₁ h₂
  · rfl
  · absurd h₂
    rw [Nat.le_iff_lt_or_eq] at h₁
    cases h₁ with
    | inl h₁ =>
      apply Nat.le_of_lt
      apply Nat.lt_trans
      exact h₁
      exact h
    | inr h₁ =>
      rw [h₁]
      apply Nat.le_of_lt
      exact h
  · rfl

theorem if_cond''' {α : Type u} (y z : Nat) (a b : Option (Loc α)) (h : y < z) :
  (fun l' : Loc α ↦ if l'.2.length ≤ y then a else b) =
  (fun l' ↦ if l'.2.length ≤ y then if l'.2.length < z then a else b else b) := by
  ext x t
  split_ifs with h₁ h₂
  · rfl
  · absurd h₂
    rw [Nat.le_iff_lt_or_eq] at h₁
    cases h₁ with
    | inl h₁ =>
      apply Nat.lt_trans
      exact h₁
      exact h
    | inr h₁ =>
      rw [h₁]
      exact h
  · rfl

theorem accept_suffix' (r : Regex α) (k : Loc α → Option (Loc α)) (x : Option (Loc α)) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length ≤ s₂.length then k l' else x) :=
  match r with
  | zero => by
    simp only [accept]
  | one => by
    simp [accept]
  | char c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ => by
    simp [accept]
    rw [accept_suffix' r₁, accept_suffix' r₂]
    rfl
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      rw [accept_suffix' r₂ _ x]
      rfl
    | char c =>
      cases s₂ with
      | nil => simp [accept]
      | cons y ys =>
        simp [accept]
        split_ifs with hc
        · rw [accept_suffix' r₂ _ x]
          nth_rw 2 [accept_suffix' r₂ _ x]
          simp
          simp_rw [if_cond _ ys.length _ x]
        · rfl
    | plus r₁₁ r₁₂ =>
      simp [accept]
      repeat rw [←accept_mul_def]
      rw [accept_suffix' (r₁₁.mul r₂) _ x]
      rw [accept_suffix' (r₁₂.mul r₂) _ x]
      rfl
    | mul r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def r₁₂ r₂]
      repeat rw [←accept_mul_def]
      rw [accept_suffix' (r₁₁.mul (r₁₂.mul r₂)) _ x]
      rfl
    | .star r =>
      rw [accept, accept, accept, accept]
      simp
      rw [accept_suffix' r₂ _ x]
      simp
      generalize hr₂ : (r₂.accept (s₁, s₂) fun l' ↦ if l'.2.length ≤ s₂.length then k l' else x) = r₂'

      have tmp :
        (fun l ↦
          if l.2.length < s₂.length then
            r.star.accept l fun l₁ ↦
              r₂.accept l₁ fun l₂ ↦
                if l₂.2.length ≤ s₂.length then
                  k l₂
                else x
          else r₂') =
        (fun l ↦
          if l.2.length < s₂.length then
            r.star.accept l fun l₁ ↦
              if l₁.2.length ≤ l.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ s₂.length then
                    k l₂
                  else x
              else x
          else r₂') := by
        ext l t
        split_ifs with hl
        · rw [accept_suffix' r.star _ x]
          rfl
        · rfl

      have tmp₂ :
        (fun l ↦
          if l.2.length < s₂.length then
            r.star.accept l fun l₁ ↦
              if l₁.2.length ≤ l.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ s₂.length then
                    k l₂
                  else x
              else x
          else r₂') =
        (fun l ↦
          if l.2.length < s₂.length then
            r.star.accept l fun l₁ ↦
              if l₁.2.length ≤ l.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ s₂.length then
                      k l₂
                    else x
                else x
              else x
          else r₂') := by
        ext l t
        split_ifs with hl
        · sorry
        · rfl

      have tmp₃ :
        (fun l ↦
          if l.2.length < s₂.length then
            r.star.accept l fun l₁ ↦
              if l₁.2.length ≤ l.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ s₂.length then
                      k l₂
                    else x
                else x
              else x
          else r₂') =
        (fun l ↦
          if l.2.length < s₂.length then
            r.star.accept l fun l₁ ↦
              if l₁.2.length ≤ l.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      if l₂.2.length ≤ s₂.length then
                        k l₂
                      else x
                    else x
                else x
              else x
          else r₂') := by
        ext l t
        split_ifs with hl
        · sorry
        · rfl

      have tmp₄ :
        (fun l ↦
          if l.2.length < s₂.length then
            r.star.accept l fun l₁ ↦
              if l₁.2.length ≤ l.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      if l₂.2.length ≤ s₂.length then
                        k l₂
                      else x
                    else x
                else x
              else x
          else r₂') =
        (fun l ↦
          if l.2.length < s₂.length then
            r.star.accept l fun l₁ ↦
              if l₁.2.length ≤ l.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x
              else x
          else r₂') := by
        sorry

      rw [tmp, tmp₂, tmp₃, tmp₄]

      sorry
  | .star r => by
    rw [accept, accept]
    simp

    have tmp :
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' fun l' ↦
            if l'.2.length ≤ s₂.length then
              k l'
            else x
        else k (s₁, s₂)) =
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' fun l' ↦
          if l'.2.length ≤ loc'.2.length then
            if l'.2.length ≤ s₂.length then
              k l'
            else x
          else x
        else k (s₁, s₂)) := by
      ext loc' t
      split_ifs with hl
      · rw [accept_suffix' r.star _ x]
        simp
      · rfl

    have tmp₂ :
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' fun l' ↦
          if l'.2.length ≤ loc'.2.length then
            if l'.2.length ≤ s₂.length then
              k l'
            else x
          else x
        else k (s₁, s₂)) =
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' fun l' ↦
          if l'.2.length ≤ loc'.2.length then
              k l'
          else x
        else k (s₁, s₂)) := by
      ext loc' t
      split_ifs with hl
      · rw [if_cond'']
        exact hl
      · rfl

    have tmp₃ :
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' k
        else k (s₁, s₂)) =
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' (fun l' =>
            if l'.2.length ≤ loc'.2.length then
              k l'
            else x)

        else k (s₁, s₂)) := by
      ext loc' t
      split_ifs with hl
      · rw [accept_suffix' r.star _ x]
        rfl
      · rfl

    rw [tmp, tmp₂, tmp₃]
termination_by (s₂.length, r.size, r.left.size)
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · simp
    apply Prod.Lex.right
    omega
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

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

theorem accept_highNullable {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (loc : Loc α) (hn : r.highNullable) :
  k (s₁, s₂) = some loc →
  r.accept (s₁, s₂) k = some loc := by
  induction r generalizing k with
  | zero => simp at hn
  | one => simp [accept]
  | char => simp at hn
  | plus r₁ r₂ ih₁ _ =>
    intro hk
    simp [accept]
    simp at hn
    rw [ih₁]
    simp
    exact hn
    exact hk
  | mul r₁ r₂ ih₁ ih₂ =>
    intro hk
    simp at hn
    simp [accept]
    rw [ih₁]
    exact hn.left
    rw [ih₂]
    exact hn.right
    exact hk
  | star r ih =>
    intro hk
    simp at hn
    rw [accept, ih]
    simp
    exact hn
    simp
    exact hk

theorem accept_nullable' (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hn : r.nullable) (hk : (k (s₁, s₂)).isSome) :
  (r.accept (s₁, s₂) k).isSome := by
  induction r generalizing s₁ s₂ k with
  | zero => simp at hn
  | one =>
    simp [accept]
    exact hk
  | char c => simp at hn
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

theorem accept_none (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  r.accept (s₁, s₂) k = none →
  ∀ k', r.accept (s₁, s₂) k' = none := by
  intro h k'
  induction r generalizing k s₁ s₂ with
  | zero => simp [accept]
  | one =>
    simp [accept] at h
    absurd hk
    simp
    use s₁, s₂
  | char c =>
    cases s₂ with
    | nil => simp [accept]
    | cons x xs =>
      simp [accept]
      intro hc
      simp [accept, hc] at h
      absurd hk
      simp
      use (x::s₁), xs
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept] at h
    simp [accept]
    constructor
    · apply ih₁ _ _ k
      exact hk
      exact h.left
    · apply ih₂ _ _ k
      exact hk
      exact h.right
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [accept] at *
    cases r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept] at *
      apply ih₂ _ _ k
      exact hk
      exact h
    | char c =>
      cases s₂ with
      | nil => simp [accept]
      | cons x xs =>
        simp [accept]
        intro hc
        simp [accept, hc] at h
        apply ih₂ _ _ k
        exact hk
        exact h
    | plus r₁₁ r₁₂ =>
      simp [accept] at *
      let ⟨h₁, h₂⟩ := h
      rw [←accept_mul_def] at h₁ h₂
      constructor
      · rw [←accept_mul_def]
        -- apply accept_none at h₁
        -- apply h₁
        -- exact hk
        sorry
      · rw [←accept_mul_def]
        -- apply accept_none at h₂
        -- apply h₂
        -- exact hk
        sorry
    | mul r₁₁ r₁₂ =>
      -- True by structural induction
      -- simp [accept] at *
      -- simp_rw [←accept_mul_def r₁₂ r₂, ←accept_mul_def] at h
      -- apply accept_none at h
      -- simp [accept] at h
      -- apply h
      -- exact hk
      sorry
    | star r =>
      rw [accept] at h
      simp at h
      let ⟨h₁, h₂⟩ := h
      rw [accept]
      simp
      constructor
      · rw [h₂] at h₁
        apply ih₂ at h₂
        rw [h₂]
        sorry
        exact hk
      · apply ih₂ _ _ k
        exact hk
        exact h₂
  | star r ih =>
    rw [accept] at h
    simp at h
    let ⟨_, h⟩ := h
    absurd hk
    simp
    use s₁, s₂

theorem accept_star_null (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
 r.star.accept (s₁, s₂) k = r.star.accept (s₁, s₂) fun l' ↦ if l'.right.length < s₂.length then k l' else k (s₁, s₂) := by
  rw [accept]
  simp
  nth_rw 1 [accept]
  simp

  have tmp :
    (fun loc' ↦
      if loc'.2.length < s₂.length then
        r.star.accept loc' fun l' ↦
          if l'.2.length < s₂.length then
            k l'
          else k (s₁, s₂)
      else k (s₁, s₂)) =
    (fun loc' ↦
      if loc'.2.length < s₂.length then
        r.star.accept loc' fun l' ↦ k l'
      else k (s₁, s₂)) := by
    ext loc' t
    split_ifs with hl
    · rw [accept_suffix' r.star _ none]
      simp

      have tmp₁ :
        (fun l' ↦
          if l'.2.length ≤ loc'.2.length then
            if l'.2.length < s₂.length then
              k l'
            else k (s₁, s₂)
          else none) =
        (fun l' ↦
          if l'.2.length ≤ loc'.2.length then
              k l'
          else none) := by
        ext l' u
        split_ifs with h₁ h₂
        · rfl
        · absurd h₂
          rw [Nat.le_iff_lt_or_eq] at h₁
          cases h₁ with
          | inl h₁ =>
            apply Nat.lt_trans
            exact h₁
            exact hl
          | inr h₁ =>
            rw [h₁]
            exact hl
        · rfl

      rw [tmp₁]
      nth_rw 2 [accept_suffix' r.star _ none]
      simp
    · rfl

  rw [tmp]

theorem accept_nullable''' (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else k (s₁, s₂)) ∨
  r.accept (s₁, s₂) k = k (s₁, s₂) := by
  induction r with
  | zero => simp [accept]
  | one => simp [accept]
  | char c =>
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    cases ih₁ with
    | inl ih₁ =>
      rw [ih₁]
      cases ih₂ with
      | inl ih₂ =>
        rw [ih₂]
        simp
      | inr ih₂ =>
        rw [ih₂]
        simp
        cases (r₁.accept (s₁, s₂) fun l' ↦ if l'.2.length < s₂.length then k l' else k (s₁, s₂)) with
        | none => simp
        | some v => simp
    | inr ih₁ =>
      rw [ih₁]
      cases ih₂ with
      | inl ih₂ =>
        rw [ih₂]
        simp
        cases h : (k (s₁, s₂)) with
        | none =>
          -- Contradiction if we assume ∀ s₃ s₄, (k (s₃, s₄)).isSome
          sorry
        | some => simp
      | inr ih₂ =>
        rw [ih₂]
        simp
  | mul r₁ r₂ ih₁ ih₂ =>
    cases r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      exact ih₂
    | char c => sorry
    | plus r₁₁ r₁₂ => sorry
    | mul r₁₁ r₁₂ => sorry
    | star r => sorry
  | star r ih =>
    rw [accept_star_null]
    simp

theorem accept_nullable'' (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else k (s₁, s₂)) := by
  induction r generalizing s₁ s₂ k with
  | zero => simp [accept]
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
      cases s₂ with
      | nil => simp [accept]
      | cons x xs =>
        simp [accept]
        split_ifs with hc
        · simp_rw [Nat.lt_succ]
          rw [accept_suffix' r₂ _ (k (s₁, x::xs))]
          rfl
        · simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      repeat rw [←accept_mul_def]
      -- rw [accept_nullable'' (r₁₁.mul r₂)]
      -- rw [accept_nullable'' (r₁₂.mul r₂)]
      -- rfl
      sorry
    | mul => sorry
    | star => sorry
  | star r ih =>
    rw [accept]
    simp
    nth_rw 1 [accept]
    simp

    have tmp :
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' fun l' ↦
            if l'.2.length < s₂.length then
              k l'
            else k (s₁, s₂)
        else k (s₁, s₂)) =
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' fun l' ↦ k l'
        else k (s₁, s₂)) := by
      ext loc' t
      split_ifs with hl
      · rw [accept_suffix' r.star _ none]
        simp

        have tmp₁ :
          (fun l' ↦
            if l'.2.length ≤ loc'.2.length then
              if l'.2.length < s₂.length then
                k l'
              else k (s₁, s₂)
            else none) =
          (fun l' ↦
            if l'.2.length ≤ loc'.2.length then
                k l'
            else none) := by
          ext l' u
          split_ifs with h₁ h₂
          · rfl
          · absurd h₂
            rw [Nat.le_iff_lt_or_eq] at h₁
            cases h₁ with
            | inl h₁ =>
              apply Nat.lt_trans
              exact h₁
              exact hl
            | inr h₁ =>
              rw [h₁]
              exact hl
          · rfl

        rw [tmp₁]
        nth_rw 2 [accept_suffix' r.star _ none]
        simp
      · rfl

    rw [tmp]

-- Maybe change k' (s₁, s₂) to x : Option (Loc α)
theorem accept_nullable (r : Regex α) (s₁ s₂ : List α) (k k' : Loc α → Option (Loc α)) (loc : Loc α) :
  r.accept (s₁, s₂) k = some loc →
  r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else k' (s₁, s₂)) = some loc ∨ k (s₁, s₂) = some loc := by
  intro h
  induction r generalizing s₁ s₂ k with
  | zero => simp [accept] at h
  | one =>
    simp [accept] at h
    exact Or.inr h
  | char c =>
    cases s₂ with
    | nil => simp [accept] at h
    | cons x xs =>
      simp [accept]
      simp [accept] at h
      exact Or.inl h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    simp [accept] at h
    cases h with
    | inl h =>
      apply ih₁ at h
      cases h with
      | inl h => exact Or.inl (Or.inl h)
      | inr h => exact Or.inr h
    | inr h =>
      let ⟨h₁, h₂⟩ := h
      apply ih₂ at h₂
      cases h₂ with
      | inl h =>
        left
        right
        refine ⟨?_, h⟩
        -- Should be true since r₁.accept (s₁, s₂) k = none
        apply accept_none at h₁
        apply h₁
        -- TODO: Add hk constraint
        sorry
      | inr h => exact Or.inr h
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [accept] at h
    apply ih₁ at h
    cases h with
    | inl h =>
      simp [accept]
      left
      sorry
    | inr h =>
      apply ih₂ at h
      cases h with
      | inl h =>
        sorry
      | inr h => exact Or.inr h
  | star r ih =>
    rw [accept] at h
    simp at h
    cases h with
    | inl h =>
      apply ih at h
      cases h with
      | inl h =>
        simp at h
        sorry
      | inr h =>
        simp at h
        exact Or.inr h
    | inr h =>
      exact Or.inr h.right

theorem accept_not_nullable' (r : Regex α) (s₁ s₂ : List α) (k k' : Loc α → Option (Loc α)) (hn : ¬r.nullable) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else k' (s₁, s₂)) :=
  match r with
  | zero => by simp [accept]
  | one => by simp at hn
  | char c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ => by
    simp at hn
    simp [accept]
    rw [accept_not_nullable' r₁ _ _ _ k']
    rw [accept_not_nullable' r₂ _ _ _ k']
    rfl
    simp [hn.right]
    simp [hn.left]
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp at hn
      simp [accept]
      rw [accept_not_nullable' r₂ _ _ _ k']
      rfl
      simp [hn]
    | char c =>
      cases s₂ with
      | nil => simp [accept]
      | cons x xs =>
        simp [accept]
        split_ifs with hc
        · simp_rw [Nat.lt_succ]
          rw [accept_suffix' _ _ (k' (s₁, x::xs))]
          simp
        · rfl
    | plus r₁₁ r₁₂ =>
      simp at hn
      simp [accept]
      repeat rw [←accept_mul_def]
      rw [accept_not_nullable' (r₁₁.mul r₂) _ _ k k']
      rw [accept_not_nullable' (r₁₂.mul r₂) _ _ k k']
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
      apply accept_not_nullable'
      simp at hn
      simp
      exact hn
    | .star r =>
      simp at hn
      -- Must be true because of the star condition
      rw [accept, accept, accept, accept]
      simp
      rw [accept_not_nullable' r₂ _ _ k k']
      simp
      sorry
      simp [hn]
  | .star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · simp
    omega
  · decreasing_tactic

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
      exact Or.inr h
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
  | star r ih =>
    simp [accept]
    by_cases hn : r.nullable
    · left
      apply ih
      exact hn
      exact hk
    · right
      refine ⟨?_, hk⟩
      apply accept_nil_none
      exact Or.inl hn

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
    simp at hr
    simp at h
    split_ifs at h with hn hn'
    · rw [prune_highNullable hn] at ih₁
      simp [accept]
      left
      apply ih₁
      exact highNullable_nullable hn
      exact h
    · simp [accept]
      left
      apply ih₁
      exact hn'
      exact h
    · simp [accept] at h
      let ⟨h₁, h₂⟩ := h
      simp [accept]
      right
      simp_all
      -- use accept_deriv_none on h₁
      sorry
  | mul => sorry
  | star r ih =>
    simp at h
    split_ifs at h with hn
    · rw [prune_highNullable hn] at ih
      rw [accept]
      simp
      sorry
    · sorry

theorem accept_deriv_none {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : ¬r.nullable) :
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
    simp [hn.left]
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
        exact h
      | char c =>
        simp at h
        split_ifs at h with hc
        · simp [accept, hc]
          simp [accept] at h
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
          simp_all
      | mul r₁₁ r₁₂ =>
        simp at h
        apply @accept_deriv_none _ (r₁₁.mul (r₁₂.mul r₂)) at h
        simp [accept]
        simp [accept] at h
        exact h
        simp_all
      | .star _ => sorry
  | .star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · simp
    omega

theorem accept_prune' (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  r.accept (s₁, s₂) k = r.prune.accept (s₁, s₂) k :=
  match r with
  | zero => by simp only [prune]
  | one => by simp only [prune]
  | char c => by simp only [prune]
  | plus r₁ r₂ => by
    simp only [prune]
    split_ifs with hn hn'
    · simp [accept]
      rw [accept_prune' r₁, prune_highNullable hn]
      simp [accept]
      apply Option.or_of_isSome
      apply hk
      exact hk
    · simp [accept]
      rw [←accept_prune' r₁]
      apply Option.or_of_isSome
      apply accept_nullable'
      exact hn'
      apply hk
      exact hk
    · simp [accept]
      rw [accept_prune' r₁, accept_prune' r₂]
      exact hk
      exact hk
  | mul r₁ r₂ => by
    rw [prune.eq_def]
    simp
    split_ifs with hn
    · simp [accept]
      rw [accept_prune' r₁, prune_highNullable hn.left, accept]
      rw [accept_prune' r₂, prune_highNullable hn.right, accept]
      exact hk
      intro s₃ s₄
      apply accept_nullable'
      exact highNullable_nullable hn.right
      apply hk
    · match r₁ with
      | zero => simp [accept]
      | one =>
        simp [accept]
        rw [accept_prune' r₂]
        exact hk
      | char c => simp [accept]
      | plus r₁₁ r₁₂ =>
        simp
        split_ifs with hn₁ hn₂
        · absurd hn
          simp
          exact hn₁
        · simp [accept]
          rw [←accept_mul_def, ←accept_prune' (r₁₁.mul r₂)]
          apply Option.or_of_isSome
          apply accept_nullable'
          simp
          exact hn₂
          apply hk
          exact hk
        · simp [accept]
          rw [←accept_mul_def, ←accept_mul_def]
          rw [accept_prune' (r₁₁.mul r₂), accept_prune' (r₁₂.mul r₂)]
          exact hk
          exact hk
      | mul r₁₁ r₁₂ =>
        simp
        rw [←accept_prune' (r₁₁.mul (r₁₂.mul r₂))]
        simp [accept]
        exact hk
      | .star _ => sorry
  | .star r => by
    rw [accept]
    simp
    split_ifs with hn
    · rw [accept_prune' r]
      rw [prune_highNullable hn]
      rw [accept, accept]
      simp
      simp
      intro s₃ s₄
      split_ifs
      · apply accept_nullable'
        simp
        apply hk
      · apply hk
    · rw [accept, accept_prune' r]
      simp

      have : (fun loc' ↦ if loc'.2.length < s₂.length then r.star.accept loc' k else k (s₁, s₂)) =
        (fun loc' ↦ if loc'.2.length < s₂.length then r.prune.star.accept loc' k else k (s₁, s₂)) := by
        ext l x
        simp
        split_ifs
        · rw [accept_prune' r.star]
          simp [hn]
          exact hk
        · rfl

      rw [this]
      simp
      intro s₃ s₄
      split_ifs
      · apply accept_nullable'
        simp
        apply hk
      · apply hk
termination_by (s₂.length, r.size, r.left.size)
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · simp
    apply Prod.Lex.right
    apply Prod.Lex.right'
    omega
    omega
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

theorem accept_prune (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) :
  r.accept (s₁, s₂) k = r.prune.accept (s₁, s₂) k := by
  induction r generalizing s₁ s₂ k with
  | zero => simp only [prune]
  | one => simp only [prune]
  | char c => simp only [prune]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [prune]
    split_ifs with hn hn'
    · simp [accept]
      rw [prune_highNullable hn] at ih₁
      rw [ih₁]
      simp [accept]
      -- TODO: restrict k (s₁, s₂)
      sorry
    · simp [accept]
      rw [←ih₁]
      apply Option.or_of_isSome
      apply accept_nullable'
      exact hn'
      -- TODO: restrict k (s₁, s₂)
      sorry
    · simp [accept]
      rw [ih₁, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [prune.eq_def]
    simp
    split_ifs with hn
    · rw [prune_highNullable hn.left] at ih₁
      rw [prune_highNullable hn.right] at ih₂
      rw [accept, accept, ih₁, accept, ih₂, accept]
    · cases r₁ with
      | zero => simp [accept]
      | one => simp [accept, ih₂]
      | char c => simp [accept]
      | plus r₁₁ r₁₂ =>
        simp
        split_ifs with hn₁ hn₂
        · absurd hn
          simp
          exact hn₁
        · simp_all
          split_ifs at ih₁
          · simp [accept]
            -- rw [accept, ih₁]
            -- simp [accept]
            sorry
          · rw [accept, ih₁]
            simp_all
            sorry
        · simp [accept]
          -- True by structural induction
          -- rw [←accept_mul_def, ←accept_mul_def]
          sorry
      | mul r₁₁ r₁₂ =>
        simp
        -- True by structural induction
        -- rw [←accept_prune]
        -- simp [accept]
        sorry
      | star => sorry
  | star r ih =>
    rw [accept]
    simp
    split_ifs with hn
    · rw [prune_highNullable hn] at ih
      rw [ih, accept, accept]
      simp
    · rw [accept]
      rw [ih]
      simp
      -- Structural induction on loc, since loc'.2.length < s₂
      -- simp_rw [accept_prune r.star]
      -- simp [hn]
      sorry

theorem accept_deriv' (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
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
    · apply accept_deriv' r₁ at h
      exact Or.inl h
      exact hk
    · simp [Regex.deriv, accept] at h
      cases h with
      | inl h =>
        apply accept_deriv' r₁ at h
        exact Or.inl h
        exact hk
      | inr h =>
        let ⟨h₁, h₂⟩ := h
        apply accept_deriv' r₂ at h₂
        refine Or.inr ⟨?_, h₂⟩
        apply accept_deriv_none
        exact hn'
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
        apply accept_deriv' r₂
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
          apply accept_deriv' (r₁₁.mul r₂) at h
          simp [accept] at h
          exact Or.inl h
          exact hk
        · simp [Regex.deriv] at h
          simp [accept] at h
          cases h with
          | inl h =>
            simp [accept]
            apply accept_deriv' (r₁₁.mul r₂) at h
            simp [accept] at h
            exact Or.inl h
            exact hk
          | inr h =>
            let ⟨h₁, h₂⟩ := h
            simp [accept]
            apply accept_deriv' (r₁₂.mul r₂) at h₂
            simp [accept] at h₂
            refine Or.inr ⟨?_, ?_⟩
            · have h := accept_deriv_none (by simp [hn']) h₁
              simp [accept] at h
              exact h
            · exact h₂
            exact hk
      | mul r₁₁ r₁₂ =>
        simp [accept]
        intro h
        apply accept_deriv' (r₁₁.mul (r₁₂.mul r₂)) at h
        simp [accept] at h
        exact h
        exact hk
      | .star _ => sorry
  | .star r => by
    simp
    split_ifs with hn
    · rw [Regex.deriv, accept]
      simp
    · intro h
      rw [Regex.deriv, accept] at h
      rw [←prune_star_not_highNullable hn] at h

      have : (fun loc' ↦ r.star.prune.accept loc' k) = (fun loc' ↦ r.star.accept loc' k) := by
        ext l x
        rw [←accept_prune']
        exact hk

      rw [this] at h
      apply accept_deriv' r at h

      rw [←accept_mul_def] at h
      -- Need to show that (r.mul r.star).accept l k = some loc → r.star.accept l k = some loc
      rw [accept] at h
      apply accept_nullable _ _ _ _ k at h
      cases h with
      | inl h =>
        rw [accept]
        simp
        exact Or.inl h
      | inr h => exact h
      intro s₃ s₄
      apply accept_nullable'
      simp
      apply hk
termination_by (r.size, r.left.size)
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · simp
    omega
  · decreasing_tactic

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
    rw [prune] at h
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
        apply accept_deriv_none
        exact hn'
        exact h₁
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [Regex.prune.eq_def] at h
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
          exact h
        · simp [accept] at h
      | plus r₁₁ r₁₂ =>
        simp at h
        split_ifs at h with hn hn'
        · simp [accept] at h
        · simp [accept]
          -- True, by structural induction, since r₁₁.mul r₂ < (r₁₁.plus r₁₂).mul r₂
          -- apply accept_deriv at h
          -- simp [accept] at h
          -- exact Or.inl h
          sorry
        · simp [Regex.deriv] at h
          simp [accept] at h
          cases h with
          | inl h =>
            simp [accept]
            -- Again, true by structural induction, since r₁₁.mul r₂ < (r₁₁.plus r₁₂).mul r₂
            -- apply accept_deriv at h
            -- simp [accept] at h
            -- exact Or.inl h
            sorry
          | inr h =>
            let ⟨h₁, h₂⟩ := h
            simp [accept]
            -- True, by structural induction, since r₁₂.mul r₂ < (r₁₁.plus r₁₂).mul r₂
            -- Also have that (r₁₁.mul r₂).accept l k = none by h₁
            apply accept_deriv at h₂
            simp [accept] at h₂
            refine Or.inr ⟨?_, ?_⟩
            · have h := accept_deriv_none (by simp [hn']) h₁
              simp [accept] at h
              exact h
            · -- exact h₂
              sorry
      | mul r₁₁ r₁₂ =>
        simp at h
        simp [accept]
        -- True, by structural induction, since r₁₁.mul (r₁₂.mul r₂) < (r₁₁.mul r₁₂).mul r₂
        -- apply accept_deriv at h
        -- simp [accept] at h
        -- exact h
        sorry
      | star =>
        sorry
  | star r ih =>
    simp [Regex.deriv] at h
    split_ifs at h with hn
    · simp [Regex.deriv, accept] at h
    · simp [Regex.deriv] at h
      rw [accept] at h
      apply ih at h
      rw [accept_prune, ←accept] at h
      rw [accept_prune, prune]
      simp [hn]
      -- Need to show (r.mul r.star).accept l k = some loc → r.star.accept l k = some loc
      rw [accept] at h
      apply accept_nullable _ _ _ _ k at h
      cases h with
      | inl h =>
        simp at h
        rw [accept]
        simp
        left
        -- We always have that the inner if condition is true, since h equals some loc
        -- Meaning we can safely replace none with k l' - although challenging to show
        exact h
      | inr h => exact h

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
