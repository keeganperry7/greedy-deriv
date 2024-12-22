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

theorem accept_some_suffix (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) (hk : ∀ s₃ s₄ l, k (s₃, s₄) = some l → l.2.length ≤ s₄.length) :
  r.accept (s₁, s₂) k = some loc →
  loc.right.length ≤ s₂.length :=
  match r with
  | zero => by simp [accept]
  | one => by
    simp [accept]
    apply hk
  | char c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs =>
      simp [accept]
      intro hc h
      apply hk at h
      exact Nat.le_succ_of_le h
  | plus r₁ r₂ => by
    simp [accept]
    intro h
    cases h with
    | inl h =>
      apply accept_some_suffix at h
      exact h
      exact hk
    | inr h =>
      let ⟨_, h⟩ := h
      apply accept_some_suffix at h
      exact h
      exact hk
  | mul r₁ r₂ => by
    simp [accept]
    intro h
    apply accept_some_suffix at h
    exact h
    intro s₃ s₄ l h'
    apply accept_some_suffix at h'
    exact h'
    exact hk
  | .star r => by
    rw [accept]
    simp
    intro h
    cases h with
    | inl h =>
      apply accept_some_suffix at h
      exact h
      intro s₃ s₄ l
      intro h'
      simp at h'
      split_ifs at h' with hl
      · apply accept_some_suffix at h'
        exact h'
        exact hk
      · apply hk at h'
        simp at hl
        apply Nat.le_trans
        exact h'
        exact hl
    | inr h =>
      let ⟨_, h⟩ := h
      apply hk at h
      exact h
termination_by (r.size, s₂.length)

theorem accept_same_nullable (r : Regex α) (s₁ s₂ : List α) (hk : ∀ s₃ s₄ l, k (s₃, s₄) = some l → l.2.length ≤ s₄.length) :
  r.accept (s₁, s₂) k = some (s₁, s₂) →
  k (s₁, s₂) = some (s₁, s₂) ∧ r.nullable :=
  match r with
  | zero => by simp [accept]
  | one => by simp [accept]
  | char c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs =>
      simp [accept]
      intro hc h
      apply hk at h
      simp at h
  | plus r₁ r₂ => by
    simp [accept]
    intro h
    match h with
    | Or.inl h =>
      apply accept_same_nullable at h
      exact ⟨h.left, Or.inl h.right⟩
      exact hk
    | Or.inr ⟨_, h⟩ =>
      apply accept_same_nullable at h
      exact ⟨h.left, Or.inr h.right⟩
      exact hk
  | mul r₁ r₂ => by
    simp [accept]
    intro h
    apply accept_same_nullable at h
    let ⟨h, hn⟩ := h
    apply accept_same_nullable at h
    exact ⟨h.left, hn, h.right⟩
    exact hk
    intro s₃ s₄ l h'
    apply accept_some_suffix at h'
    exact h'
    exact hk
  | .star r => by
    rw [accept]
    simp
    intro h
    match h with
    | Or.inl h =>
      apply accept_same_nullable at h
      simp at h
      exact h.left
      intro s₃ s₄ l h'
      split_ifs at h' with hl
      · simp at hl
        apply accept_some_suffix at h'
        exact h'
        exact hk
      · simp at hl
        apply hk at h'
        apply Nat.le_trans
        exact h'
        exact hl
    | Or.inr h => exact h.right

theorem accept_suffix (r : Regex α) (k : Loc α → Option (Loc α)) (x : Option (Loc α)) :
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
    rw [accept_suffix r₁, accept_suffix r₂]
    rfl
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      rw [accept_suffix r₂ _ x]
      rfl
    | char c =>
      cases s₂ with
      | nil => simp [accept]
      | cons y ys =>
        simp [accept]
        split_ifs with hc
        · rw [accept_suffix r₂ _ x]
          nth_rw 2 [accept_suffix r₂ _ x]
          simp
          simp_rw [if_cond _ ys.length _ x]
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

      generalize hr₂ : (r₂.accept (s₁, s₂) fun l' ↦ if l'.2.length ≤ s₂.length then k l' else x) = r₂'

      have tmp :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦ r₂.accept l₁ fun l₂ ↦
              if l₂.2.length ≤ s₂.length then
                k l₂
              else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              r₂.accept l₁ fun l₂ ↦
                if l₂.2.length ≤ s₂.length then
                  k l₂
                else x
              else x
          else r₂') := by
        ext loc' t
        split_ifs with hl
        · rw [accept_suffix r.star _ x]
          rfl
        · rfl

      have tmp₂ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              r₂.accept l₁ fun l₂ ↦
                if l₂.2.length ≤ s₂.length then
                  k l₂
                else x
              else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              if l₁.2.length < s₂.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ s₂.length then
                    k l₂
                  else x
                else x
              else x
          else r₂') := by
        ext loc' t
        split_ifs with hl
        have tmp₂₁ :
          (fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              r₂.accept l₁ fun l₂ ↦
                if l₂.2.length ≤ s₂.length then
                  k l₂
                else x
            else x) =
          (fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              if l₁.2.length < s₂.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ s₂.length then
                    k l₂
                  else x
              else x
            else x) := by

          ext l₁ t₁
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
        rw [tmp₂₁]
        rfl

      have tmp₃ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              if l₁.2.length < s₂.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ s₂.length then
                    k l₂
                  else x
                else x
              else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
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
        ext loc' t
        split_ifs with hl
        ·
          have tmp₃₁ :
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ s₂.length then
                      k l₂
                    else x
                else x
              else x) =
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      if l₂.2.length ≤ s₂.length then
                        k l₂
                      else x
                    else x
                else x
              else x)  := by
            ext l₁ u
            split_ifs with h₁ h₂
            · rw [accept_suffix r₂ _ x]
              rfl
            · rfl
            · rfl
          rw [tmp₃₁]
        · rfl

      have tmp₄ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
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
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              if l₁.2.length < s₂.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x
                else x
              else x
          else r₂') := by

        ext loc' t
        split_ifs with hl
        ·
          have tmp₄₁ :
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      if l₂.2.length ≤ s₂.length then
                        k l₂
                      else x
                    else x
                  else x
                else x) =
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      k l₂
                    else x
                  else x
                else x) := by
            ext l₁ u
            split_ifs with h₁ h₂
            ·
              have tmp₄₂ :
                (fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    if l₂.2.length ≤ s₂.length then
                      k l₂
                    else x
                  else x) =
                (fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x) := by
                ext l₂ v
                split_ifs with h₃ h₄
                · rfl
                · absurd h₄
                  apply Nat.le_trans
                  exact h₃
                  apply Nat.le_of_lt
                  exact h₂
                · rfl
              rw [tmp₄₂]
            · rfl
            · rfl
          rw [tmp₄₁]
        · rfl

      have tmp₅ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              if l₁.2.length < s₂.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x
                else x
              else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              if l₁.2.length < s₂.length then
                r₂.accept l₁ fun l₂ ↦
                  k l₂
              else x
            else x
          else r₂') := by
        ext loc' t
        split_ifs with hl
        ·
          have tmp₅₁ :
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      k l₂
                    else x
                else x
              else x) =
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦
                    k l₂
                else x
              else x) := by
            ext l₁ u
            split_ifs with h₁ h₂
            · nth_rw 2 [accept_suffix r₂ _ x]
              rfl
            · rfl
            · rfl

          rw [tmp₅₁]
        · rfl

      have tmp₆ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              if l₁.2.length < s₂.length then
                r₂.accept l₁ fun l₂ ↦
                  k l₂
              else x
            else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              r₂.accept l₁ fun l₂ ↦
                k l₂
            else x
          else r₂') := by
        ext loc' t
        split_ifs with hl
        ·
          have tmp₆₁ :
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                if l₁.2.length < s₂.length then
                  r₂.accept l₁ fun l₂ ↦ k l₂
                else x
              else x) =
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦ k l₂
              else x) := by
            ext l₁ u
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
          rw [tmp₆₁]
        · rfl

      have tmp₇ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              r₂.accept l₁ fun l₂ ↦
                k l₂
            else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              r₂.accept l₁ fun l₂ ↦ k l₂
          else r₂') := by
        ext loc' t
        split_ifs with hl
        · nth_rw 2 [accept_suffix r.star _ x]
          rfl
        · rfl

      rw [tmp, tmp₂, tmp₃, tmp₄, tmp₅, tmp₆, tmp₇]
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
      · rw [accept_suffix r.star _ x]
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
      · rw [accept_suffix r.star _ x]
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
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

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

theorem accept_highNullable' {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : r.highNullable) (hk : (k (s₁, s₂)).isSome) :
  r.accept (s₁, s₂) k = k (s₁, s₂) := by
  induction r generalizing k with
  | zero => simp at hn
  | one => simp [accept]
  | char => simp at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    simp at hn
    rw [ih₁, Option.or_of_isSome]
    exact hk
    exact hn
    exact hk
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [accept]
    rw [ih₁, ih₂]
    exact hn.right
    exact hk
    exact hn.left
    apply accept_nullable'
    apply highNullable_nullable
    exact hn.right
    exact hk
  | star r ih =>
    simp at hn
    rw [accept, ih]
    simp
    exact hn
    simp
    exact hk

theorem accept_highNullable_eq {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : r.highNullable) :
  r.accept (s₁, s₂) k = (k (s₁, s₂)).or (r.accept (s₁, s₂) k) := by
  induction r generalizing k with
  | zero => simp at hn
  | one => simp [accept]
  | char c => simp at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [accept]
    nth_rw 1 [ih₁]
    rw [Option.or_assoc]
    exact hn
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [accept]
    nth_rw 1 [ih₁ hn.left]
    nth_rw 1 [ih₂ hn.right]
    nth_rw 2 [ih₁ hn.left]
    rw [Option.or_assoc]
  | star r ih =>
    simp at hn
    rw [accept]
    nth_rw 1 [ih hn]
    simp
    rw [Option.or_assoc]

theorem accept_nullable_eq {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : r.nullable) :
  r.accept (s₁, s₂) k = (r.accept (s₁, s₂) k).or (k (s₁, s₂)) := by
  induction r generalizing k with
  | zero => simp at hn
  | one => simp [accept]
  | char c => simp at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    cases hn with
    | inl hn =>
      simp [accept]
      rw [ih₁ hn]
      cases (k (s₁, s₂)) with
      | none => simp
      | some l => repeat rw [Option.or_assoc, Option.or_some]
    | inr hn =>
      simp only [accept]
      rw [ih₂ hn, Option.or_assoc, Option.or_assoc, Option.or_self]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [accept]
    nth_rw 1 [ih₁ hn.left, ih₂ hn.right]
    nth_rw 2 [ih₁ hn.left]
    rw [Option.or_assoc]
  | star r ih => rw [accept, Option.or_assoc, Option.or_self]

theorem accept_not_nullable (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (x : Option (Loc α)) (hn : ¬r.nullable) :
  r.accept (s₁, s₂) k = r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else x) :=
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
    rw [accept_not_nullable r₁ _ _ _ x]
    rw [accept_not_nullable r₂ _ _ _ x]
    rfl
    simp [hn.right]
    simp [hn.left]
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp at hn
      simp [accept]
      rw [accept_not_nullable r₂ _ _ _ x]
      rfl
      simp [hn]
    | char c =>
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

      generalize hr₂ : (r₂.accept (s₁, s₂) fun l' ↦ if l'.2.length < s₂.length then k l' else x) = r₂'

      have tmp :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              r₂.accept l₁ fun l₂ ↦
                if l₂.2.length < s₂.length then
                  k l₂
                else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length < s₂.length then
                    k l₂
                  else x
              else x
          else r₂') := by
        ext loc' t
        split_ifs with hl
        · rw [accept_suffix r.star _ x]
          rfl
        · rfl

      have tmp₁ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length < s₂.length then
                    k l₂
                  else x
              else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    if l₂.2.length < s₂.length then
                      k l₂
                    else x
                  else x
              else x
          else r₂') := by
        simp_rw [accept_suffix r₂ (fun l₂ ↦ if l₂.2.length < s₂.length then k l₂ else x) x]
        simp

      have tmp₂ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    if l₂.2.length < s₂.length then
                      k l₂
                    else x
                  else x
              else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x
              else x
          else r₂') := by
        ext loc' t
        split_ifs with hl
        ·
          have tmp₂₁ :
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    if l₂.2.length < s₂.length then
                      k l₂
                    else x
                  else x
              else x) =
            (fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x
              else x) := by
            ext l₁ u
            split_ifs with h₁
            ·
              have tmp₂₂ :
                (fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    if l₂.2.length < s₂.length then
                      k l₂
                    else x
                  else x) =
                (fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x) := by
                ext l₂ v
                split_ifs with h₂ h₃
                · rfl
                · absurd h₃
                  rw [Nat.le_iff_lt_or_eq] at h₂
                  cases h₂ with
                  | inl h₂ =>
                    apply Nat.lt_trans
                    exact h₂
                    rw [Nat.le_iff_lt_or_eq] at h₁
                    cases h₁ with
                    | inl h₁ =>
                      apply Nat.lt_trans
                      exact h₁
                      exact hl
                    | inr h₁ =>
                      rw [h₁]
                      exact hl
                  | inr h₂ =>
                    rw [h₂]
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
              rw [tmp₂₂]
            · rfl
          rw [tmp₂₁]
        · rfl

      have tmp₃ :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x
              else x
          else r₂') =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              r₂.accept l₁ fun l₂ ↦ k l₂
          else r₂') := by
        simp_rw [accept_suffix r.star (fun l₁ ↦ r₂.accept l₁ (fun l₂ ↦ k l₂)) x]
        simp_rw [accept_suffix r₂ (fun l₂ ↦ k l₂) x]
        simp

      rw [tmp, tmp₁, tmp₂, tmp₃]
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

theorem accept_deriv_cond (r : Regex α) (s₁ s₂ : List α) (x : α) (k : Loc α → Option (Loc α)) :
  (r.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) (fun l' ↦ if l'.right.length < (x::s₂).length then k l' else none) := by
  induction r generalizing k with
  | zero => simp [accept]
  | one => simp [accept]
  | char c =>
    simp [accept]
    split_ifs
    · simp [accept]
    · simp [accept]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    rw [ih₁, ih₂]
    simp
  | mul r₁ r₂ ih₁ ih₂ => sorry
  | star r ih =>
    simp
    rw [accept]
    rw [ih]
    simp
    rw [accept]
    simp
    sorry

theorem accept_nullable (r : Regex α) (s₁ s₂ : List α) (x : Option (Loc α)) (k : Loc α → Option (Loc α)) (hn : r.nullable)
  (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) (hx : x.isSome) :
  r.accept (s₁, s₂) k = (r.accept (s₁, s₂) (fun l' => if l'.right.length < s₂.length then k l' else x)) ∨
  r.accept (s₁, s₂) k = k (s₁, s₂) :=
  match r with
  | zero => by
    simp at hn
  | one => by
    simp [accept]
  | char c => by
    simp at hn
  | plus r₁ r₂ => by
    simp at hn
    cases hn with
    | inl hn =>
      simp [accept]
      cases (accept_nullable r₁ s₁ s₂ x k hn hk hx) with
      | inl h =>
        left
        rw [h, Option.or_of_isSome, Option.or_of_isSome]
        rfl
        apply accept_nullable'
        exact hn
        split_ifs
        · apply hk
        · exact hx
        apply accept_nullable'
        exact hn
        split_ifs
        · apply hk
        · exact hx
      | inr h =>
        rw [h]
        right
        rw [Option.or_of_isSome]
        apply hk
    | inr hn =>
      simp [accept]
      by_cases hn₁ : r₁.nullable
      · cases (accept_nullable r₁ s₁ s₂ x k hn₁ hk hx) with
        | inl h =>
          left
          rw [h, Option.or_of_isSome, Option.or_of_isSome]
          rfl
          apply accept_nullable'
          exact hn₁
          simp [hx]
          apply accept_nullable'
          exact hn₁
          simp [hx]
        | inr h =>
          rw [h]
          right
          rw [Option.or_of_isSome]
          apply hk
      · rw [accept_not_nullable r₁ _ _ _ x hn₁]
        simp
        by_cases hr₁ : (r₁.accept (s₁, s₂) fun l' ↦ if l'.2.length < s₂.length then k l' else x).isSome
        · left
          rw [Option.or_of_isSome, Option.or_of_isSome]
          exact hr₁
          exact hr₁
        · simp at hr₁
          rw [hr₁]
          simp
          cases (accept_nullable r₂ s₁ s₂ x k hn hk hx) with
          | inl h =>
            rw [h]
            simp
          | inr h =>
            rw [h]
            simp
  | mul r₁ r₂ => by
    cases r₁ with
    | zero => simp at hn
    | one =>
      simp at hn
      simp [accept]
      apply accept_nullable
      exact hn
      exact hk
      exact hx
    | char c => simp at hn
    | plus r₁₁ r₁₂ =>
      simp [accept]
      repeat rw [←accept_mul_def]
      simp at hn
      let ⟨hn₁, hn₂⟩ := hn
      cases hn₁ with
      | inl hn₁ =>
        cases (accept_nullable (r₁₁.mul r₂) s₁ s₂ x k (by simp [hn₁, hn₂]) hk hx) with
        | inl h =>
          rw [h]
          left
          rw [Option.or_of_isSome, Option.or_of_isSome]
          rfl
          apply accept_nullable'
          simp [hn₁, hn₂]
          simp [hx]
          apply accept_nullable'
          simp [hn₁, hn₂]
          simp [hx]
        | inr h =>
          rw [h]
          right
          rw [Option.or_of_isSome]
          apply hk
      | inr hn₁ =>
        by_cases hn₃ : r₁₁.nullable
        · cases (accept_nullable (r₁₁.mul r₂) s₁ s₂ x k (by simp [hn₃, hn₂]) hk hx) with
          | inl h =>
            rw [h]
            left
            rw [Option.or_of_isSome, Option.or_of_isSome]
            rfl
            apply accept_nullable'
            simp [hn₃, hn₂]
            simp [hx]
            apply accept_nullable'
            simp [hn₃, hn₂]
            simp [hx]
          | inr h =>
            rw [h]
            right
            rw [Option.or_of_isSome]
            apply hk
        · rw [accept_not_nullable (r₁₁.mul r₂) _ _ _ x (by simp [hn₃])]
          simp
          by_cases hr₁ : ((r₁₁.mul r₂).accept (s₁, s₂) fun l' ↦ if l'.2.length < s₂.length then k l' else x).isSome
          · left
            rw [Option.or_of_isSome, Option.or_of_isSome]
            exact hr₁
            exact hr₁
          · simp at hr₁
            rw [hr₁]
            simp
            cases (accept_nullable (r₁₂.mul r₂) s₁ s₂ x k (by simp [hn₁, hn₂]) hk hx) with
            | inl h =>
              rw [h]
              simp
            | inr h =>
              rw [h]
              simp
    | mul r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def]
      apply accept_nullable (r₁₁.mul (r₁₂.mul r₂))
      simp at hn
      simp [hn]
      exact hk
      exact hx
    | star r =>
      rw [accept, accept, accept]
      simp

      by_cases hr : ((r.accept (s₁, s₂) fun loc' ↦
          if loc'.2.length < s₂.length then r.star.accept loc' fun loc' ↦ r₂.accept loc' k else r₂.accept (s₁, s₂) k)).isSome
      · rw [Option.or_of_isSome]
        rw [accept]
        simp
        generalize hr₂ : (r₂.accept (s₁, s₂) fun l' ↦ if l'.2.length < s₂.length then k l' else x) = r₂'

        have tmp :
          (fun loc' ↦
              if loc'.2.length < s₂.length then
                r.star.accept loc' fun l₁ ↦
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length < s₂.length then
                      k l₂
                    else x
              else r₂') =
          (fun loc' ↦
              if loc'.2.length < s₂.length then
                r.star.accept loc' fun l₁ ↦
                  r₂.accept l₁ fun l₂ ↦
                    k l₂
              else r₂') := by
          simp_rw [accept_suffix r.star (fun l₁ ↦ r₂.accept l₁ fun l₂ ↦ if l₂.2.length < s₂.length then k l₂ else x) x]
          simp_rw [accept_suffix r₂ (fun l₂ ↦ if l₂.2.length < s₂.length then k l₂ else x) x]
          simp
          ext loc' t
          split_ifs with hl
          · have tmp₁ :
              (fun l₁ ↦
                if l₁.2.length ≤ loc'.2.length then
                  r₂.accept l₁ fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      if l₂.2.length < s₂.length then
                        k l₂
                      else x
                    else x
                else x) =
              (fun l₁ ↦
                if l₁.2.length ≤ loc'.2.length then
                  r₂.accept l₁ fun l₂ ↦
                      k l₂
                else x) := by
              ext l₁ u
              split_ifs with h₁
              · have tmp₂ :
                  (fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      if l₂.2.length < s₂.length then
                        k l₂
                      else x
                    else x) =
                  (fun l₂ ↦
                    if l₂.2.length ≤ l₁.2.length then
                      k l₂
                    else x) := by
                  ext l₂ v
                  split_ifs with h₂ h₃
                  · rfl
                  · absurd h₃
                    apply Nat.lt_of_le_of_lt
                    apply Nat.le_trans
                    exact h₂
                    exact h₁
                    exact hl
                  · rfl
                rw [tmp₂, accept_suffix r₂ (fun l₂ ↦ k l₂) x]
                simp
              · rfl
            rw [tmp₁, accept_suffix r.star (fun l₁ ↦ r₂.accept l₁ fun l₂ ↦ k l₂) x]
            simp
          · rfl

        rw [tmp]
        clear tmp
        by_cases hn₁ : r.nullable
        ·
          have hk₁ :
            ∀ (s₃ s₄ : List α), (if (s₃, s₄).2.length < s₂.length then r.star.accept (s₃, s₄) fun loc' ↦ r₂.accept loc' k else r₂.accept (s₁, s₂) k).isSome = true := by
            intro s₃ s₄
            split_ifs
            · apply accept_nullable'
              simp
              apply accept_nullable'
              simp at hn
              exact hn
              apply hk
            · apply accept_nullable'
              simp at hn
              exact hn
              apply hk

          have hn₂ : r₂'.isSome = true := by
            rw [←hr₂]
            apply accept_nullable'
            simp at hn
            exact hn
            simp
            exact hx

          cases (accept_nullable r s₁ s₂ r₂' (fun loc' ↦ if loc'.2.length < s₂.length then r.star.accept loc' fun loc' ↦ r₂.accept loc' k else r₂.accept (s₁, s₂) k)) hn₁ hk₁ hn₂ with
          | inl h =>
            rw [h]
            rw [h] at hr
            have tmp :
              (fun l' ↦
                if l'.right.length < s₂.length then
                  if l'.2.length < s₂.length then
                    r.star.accept l' fun loc' ↦
                      r₂.accept loc' k
                  else r₂.accept (s₁, s₂) k
                else r₂') =
              (fun l' ↦
                if l'.right.length < s₂.length then
                  r.star.accept l' fun loc' ↦
                    r₂.accept loc' k
                else r₂') := by
              ext l' t
              split_ifs with h₁ h₂
              · rfl
              · absurd h₂
                exact h₁
              · rfl

            rw [tmp]
            rw [tmp] at hr
            clear tmp
            left
            rw [Option.or_of_isSome]
            rfl
            exact hr
          | inr h =>
            simp at h
            rw [h]
            rw [h] at hr
            simp at hn
            cases (accept_nullable r₂ s₁ s₂ x k hn hk hx) with
            | inl h₁ =>
              left
              simp at h₁
              rw [hr₂] at h₁
              rw [h₁] at h
              rw [h, h₁]
              simp
            | inr h₁ =>
              rw [h₁]
              simp
        · rw [accept_not_nullable r _ _ _ r₂' hn₁]
          rw [accept_not_nullable r _ _ _ r₂' hn₁] at hr

          have tmp :
            (fun l' ↦
              if l'.right.length < s₂.length then
                if l'.2.length < s₂.length then
                  r.star.accept l' fun loc' ↦
                    r₂.accept loc' k
                else r₂.accept (s₁, s₂) k
              else r₂') =
            (fun l' ↦
              if l'.right.length < s₂.length then
                r.star.accept l' fun loc' ↦
                  r₂.accept loc' k
              else r₂') := by
            ext l' t
            split_ifs with h₁ h₂
            · rfl
            · absurd h₂
              exact h₁
            · rfl

          rw [tmp]
          rw [tmp] at hr
          clear tmp
          left
          rw [Option.or_of_isSome]
          rfl
          exact hr

        exact hr
      · simp at hr
        rw [hr]
        simp
        rw [accept]
        simp

        simp at hn
        cases (accept_nullable r₂) s₁ s₂ x k (by simp [hn]) hk hx with
        | inl h =>
          rw [Option.or_of_isNone]
          rw [h]
          simp
          -- True since l'.2.length < s₂.length is always true
          simp at h
          rw [←h]
          simp_rw [accept_suffix r₂ (fun l' ↦ if l'.2.length < s₂.length then k l' else x) x]
          simp

          generalize hr₂ : r₂.accept (s₁, s₂) k = r₂'
          rw [hr₂] at hr

          simp_rw [accept_suffix r.star (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length ≤ loc'.2.length then if l'.2.length < s₂.length then k l' else x else x) x]

          have tmp :
            (fun loc' ↦
              if loc'.2.length < s₂.length then
                r.star.accept loc' fun l₁ ↦
                  if l₁.2.length ≤ loc'.2.length then
                    r₂.accept l₁ fun l₂ ↦
                      if l₂.2.length ≤ l₁.2.length then
                        if l₂.2.length < s₂.length then
                          k l₂
                        else x
                      else x
                  else x
              else r₂') =
            (fun loc' ↦
              if loc'.2.length < s₂.length then
                r.star.accept loc' fun l₁ ↦
                  r₂.accept l₁ fun l₂ ↦
                    k l₂
              else r₂') := by
            ext loc' t
            split_ifs with hl
            ·
              have tmp₁ :
                (fun l₁ ↦
                  if l₁.2.length ≤ loc'.2.length then
                    r₂.accept l₁ fun l₂ ↦
                      if l₂.2.length ≤ l₁.2.length then
                        if l₂.2.length < s₂.length then
                          k l₂
                        else x
                      else x
                  else x) =
                (fun l₁ ↦
                  if l₁.2.length ≤ loc'.2.length then
                    r₂.accept l₁ fun l₂ ↦
                        k l₂
                  else x) := by
                ext l₁ u
                split_ifs with h₁
                · have tmp₂ :
                    (fun l₂ ↦
                      if l₂.2.length ≤ l₁.2.length then
                        if l₂.2.length < s₂.length then
                          k l₂
                        else x
                      else x) =
                    (fun l₂ ↦
                      if l₂.2.length ≤ l₁.2.length then
                        k l₂
                      else x) := by
                    ext l₂ v
                    split_ifs with h₂ h₃
                    · rfl
                    · absurd h₃
                      apply Nat.lt_of_le_of_lt
                      apply Nat.le_trans
                      exact h₂
                      exact h₁
                      exact hl
                    · rfl
                  rw [tmp₂, accept_suffix r₂ (fun l₂ ↦ k l₂) x]
                  simp
                · rfl
              rw [tmp₁, accept_suffix r.star (fun l₁ ↦ r₂.accept l₁ fun l₂ ↦ k l₂) x]
              simp
            · rfl
          simp
          rw [tmp]
          exact hr
        | inr h =>
          rw [h]
          simp
  | .star r => by
    rw [accept]
    simp
    by_cases hr : ((r.accept (s₁, s₂) fun loc' ↦ if loc'.2.length < s₂.length then r.star.accept loc' k else k (s₁, s₂))).isSome
    · rw [Option.or_of_isSome, accept]
      simp
      simp_rw [accept_suffix r.star (fun l' ↦ if l'.2.length < s₂.length then k l' else x) x]
      simp

      have tmp :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l' ↦
              if l'.2.length ≤ loc'.2.length then
                if l'.2.length < s₂.length then
                  k l'
                else x
              else x
          else x) =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l' ↦
              k l'
          else x) := by
        ext loc' t
        split_ifs with hl
        ·
          have tmp₁ :
            (fun l' ↦
              if l'.2.length ≤ loc'.2.length then
                if l'.2.length < s₂.length then
                  k l'
                else x
              else x) =
            (fun l' ↦
              if l'.2.length ≤ loc'.2.length then
                k l'
              else x) := by
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
            . rfl
          rw [tmp₁]
          rw [accept_suffix r.star (fun l' ↦ k l') x]
          simp
        · rfl

      rw [tmp]
      clear tmp
      by_cases hn₁ : r.nullable
      ·
        have hk' : (∀ s₃ s₄, ((fun loc' ↦ if loc'.2.length < s₂.length then r.star.accept loc' k else k (s₁, s₂)) (s₃, s₄)).isSome) := by
          intro s₃ s₄
          simp
          split_ifs
          · apply accept_nullable'
            simp
            apply hk
          · apply hk

        cases (accept_nullable r s₁ s₂ x (fun loc' ↦ if loc'.2.length < s₂.length then r.star.accept loc' k else k (s₁, s₂)) hn₁ hk' hx) with
        | inl h =>
          rw [h]
          rw [h] at hr
          have tmp :
            (fun l' ↦
              if l'.right.length < s₂.length then
                if l'.2.length < s₂.length then
                  r.star.accept l' k
                else k (s₁, s₂)
              else x) =
            (fun l' ↦
              if l'.right.length < s₂.length then
                r.star.accept l' k
              else x) := by
            ext l' t
            split_ifs with h₁ h₂
            · rfl
            · absurd h₂
              exact h₁
            · rfl
          rw [tmp]
          rw [tmp] at hr
          clear tmp
          rw [Option.or_of_isSome]
          left
          rfl
          exact hr
        | inr h =>
          simp at h
          rw [h]
          right
          rfl
      · rw [accept_not_nullable r _ _ _ x hn₁]
        rw [accept_not_nullable r _ _ _ x hn₁] at hr
        have tmp :
          (fun l' ↦
            if l'.right.length < s₂.length then
              if l'.2.length < s₂.length then
                r.star.accept l' k
              else k (s₁, s₂)
            else x) =
          (fun l' ↦
            if l'.right.length < s₂.length then
              r.star.accept l' k
            else x) := by
          ext l' t
          split_ifs with h₁ h₂
          · rfl
          · absurd h₂
            exact h₁
          · rfl
        rw [tmp]
        rw [tmp] at hr
        clear tmp
        rw [Option.or_of_isSome]
        left
        rfl
        exact hr
      exact hr
    · simp at hr
      rw [hr]
      simp
termination_by (r.size, r.left.size)
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · rename_i h
    rw [h]
    simp
    omega
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

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

theorem accept_deriv_none'' (r : Regex α) {s₁ s₂ : List α} (k : Loc α → Option (Loc α)) (y : Option (Loc α)) (hn : r.nullable) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = none →
  (r.accept (s₁, x::s₂) (fun l' => if l'.right.length < (x :: s₂).length then k l' else y)) = y :=
  match r with
  | zero => by simp at hn
  | one => by
    simp [accept]
  | char _ => by simp at hn
  | plus r₁ r₂ => by
    intro h
    simp at hn
    simp [accept] at h
    split_ifs at h with hn₁ hn₂
    · rw [accept_highNullable']
      simp
      simp
      exact hn₁
      simp
      -- Add condition to y
      sorry
    · apply accept_deriv_none'' _ _ y at h
      rw [accept, h, Option.or_of_isSome]
      -- Add condition to y
      sorry
      exact hn₂
    · simp [accept] at h
      let ⟨h₁, h₂⟩ := h
      clear h
      apply accept_deriv_none at h₁
      apply accept_deriv_none'' _ _ y at h₂
      rw [accept]
      rw [←accept_not_nullable]
      rw [h₁, h₂]
      simp
      exact hn₂
      exact Or.resolve_left hn hn₂
      exact hn₂
  | mul r₁ r₂ =>
    match r₁ with
    | zero => by simp at hn
    | one => by
      simp [accept]
      simp at hn
      intro h
      split_ifs at h with hr
      · rw [accept_highNullable']
        simp
        exact hr
        simp
        -- Add condition to y
        sorry
      · apply accept_deriv_none'' _ _ y at h
        simp at h
        exact h
        exact hn
    | char c => by simp at hn
    | plus r₁₁ r₁₂ => by
      intro h
      simp [accept] at h
      split_ifs at h with hn₁ hn₂
      · rw [accept_highNullable']
        simp
        simp
        exact hn₁
        simp
        -- Add condition to y
        sorry
      · apply accept_deriv_none'' _ _ y at h
        rw [accept, accept, ←accept_mul_def, h]
        -- Add condition to y
        sorry
        simp
        exact hn₂
      · simp at hn hn₂
        simp [hn] at hn₂
        simp [hn₂] at hn
        simp [accept] at h
        let ⟨h₁, h₂⟩ := h
        clear h
        apply accept_deriv_none at h₁
        apply accept_deriv_none'' _ _ y at h₂
        rw [accept, accept, ←accept_mul_def, ←accept_mul_def]
        rw [←accept_not_nullable, h₁, h₂]
        simp
        simp [hn₂]
        simp
        exact hn
        simp [hn₂]
    | mul r₁₁ r₁₂ => by
      -- intro h
      -- simp at h
      -- split_ifs at h with hr
      -- · rw [accept_highNullable']
      --   simp
      --   simp
      --   exact hr
      --   simp
      --   -- Add condition to y
      --   sorry
      -- · apply accept_deriv_none'' _ _ y at h
      --   rw [accept, accept]
      --   simp_rw [←accept_mul_def]
      --   exact h
      --   simp at hn
      --   simp [hn]
      sorry
    | .star r => by
      intro h
      simp at h hn
      split_ifs at h with hn₁ hn₂
      · rw [accept_highNullable']
        simp
        simp
        exact hn₁
        simp
        -- Add condition to y
        sorry
      · simp [hn] at h
        apply accept_deriv_none'' _ _ y at h
        rw [accept, accept_highNullable']
        exact h
        simp
        exact hn₂
        apply accept_nullable'
        exact hn
        simp
        -- Add condition to y
        sorry
        exact hn
      · simp [hn] at h
        rw [prune_highNullable_highNullable] at h
        simp [hn₂] at h
        rw [accept] at h
        simp at h
        let ⟨h₁, h₂⟩ := h
        clear h
        rw [accept, accept] at h₁
        apply accept_deriv_none'' _ _ y at h₂
        by_cases hr : r.nullable
        · apply accept_deriv_none'' _ _ y at h₁
          rw [accept, accept, h₂]
          -- Rewrite r.prune.star.accept to r.star.accept
          -- Always true because of condition on r
          sorry
          exact hr
        · apply accept_deriv_none at h₁
          rw [accept, accept, h₂]
          rw [accept_not_nullable _ _ _ _ y] at h₁
          -- Rewrite r.prune.star.accept to r.star.accept
          -- Always true because of condition on r
          rw [Option.or_of_isNone]
          rw [Option.isNone_iff_eq_none]
          sorry
          exact hr
          exact hr
        exact hn
  | .star r => by
    intro h
    simp at h
    split_ifs at h with hr
    · rw [accept_highNullable']
      simp
      simp
      exact hr
      simp
      -- Add condition to y
      sorry
    · rw [Regex.deriv, accept] at h
      by_cases hr' : r.nullable
      · apply accept_deriv_none'' _ _ y at h
        rw [accept]
        simp
        simp at h
        -- Rewrite r.prune.star.accept to r.star.accept
        -- Always true because of condition on r
        sorry
        exact hr'
      · apply accept_deriv_none at h
        rw [accept]
        simp
        rw [accept_not_nullable _ _ _ _ y] at h
        -- Rewrite r.prune.star.accept to r.star.accept
        -- Always true because of condition on r
        rw [Option.or_of_isNone]
        sorry
        exact hr'
        exact hr'

theorem accept_deriv_none_nullable {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = k (s₁, x::s₂) := by
  intro h
  apply accept_deriv_none'' _ _ (k (s₁, x::s₂)) at h

  cases (accept_nullable r s₁ (x::s₂) (k (s₁, x::s₂)) k hn hk (hk s₁ (x::s₂))) with
  | inl h' =>
    rw [h']
    exact h
  | inr h' => exact h'
  exact hn

theorem accept_prune (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  r.accept (s₁, s₂) k = r.prune.accept (s₁, s₂) k :=
  match r with
  | zero => by simp only [prune]
  | one => by simp only [prune]
  | char c => by simp only [prune]
  | plus r₁ r₂ => by
    simp only [prune]
    split_ifs with hn hn'
    · simp [accept]
      rw [accept_prune r₁, prune_highNullable hn]
      simp [accept]
      apply Option.or_of_isSome
      apply hk
      exact hk
    · simp [accept]
      rw [←accept_prune r₁]
      apply Option.or_of_isSome
      apply accept_nullable'
      exact hn'
      apply hk
      exact hk
    · simp [accept]
      rw [accept_prune r₁, accept_prune r₂]
      exact hk
      exact hk
  | mul r₁ r₂ => by
    rw [prune.eq_def]
    simp
    split_ifs with hn
    · simp [accept]
      rw [accept_prune r₁, prune_highNullable hn.left, accept]
      rw [accept_prune r₂, prune_highNullable hn.right, accept]
      exact hk
      intro s₃ s₄
      apply accept_nullable'
      exact highNullable_nullable hn.right
      apply hk
    · match r₁ with
      | zero => simp [accept]
      | one =>
        simp [accept]
        rw [accept_prune r₂]
        exact hk
      | char c => simp [accept]
      | plus r₁₁ r₁₂ =>
        simp
        split_ifs with hn₁ hn₂
        · absurd hn
          simp
          exact hn₁
        · simp [accept]
          rw [←accept_mul_def, ←accept_prune (r₁₁.mul r₂)]
          apply Option.or_of_isSome
          apply accept_nullable'
          simp
          exact hn₂
          apply hk
          exact hk
        · simp [accept]
          rw [←accept_mul_def, ←accept_mul_def]
          rw [accept_prune (r₁₁.mul r₂), accept_prune (r₁₂.mul r₂)]
          exact hk
          exact hk
      | mul r₁₁ r₁₂ =>
        simp
        rw [←accept_prune (r₁₁.mul (r₁₂.mul r₂))]
        simp [accept]
        exact hk
      | .star r =>
        simp
        by_cases hr : r₂.nullable
        · simp [hr]
          split_ifs with hn₁
          · rw [accept]
            have h :
              (r.star.accept (s₁, s₂) fun loc' ↦ r₂.accept loc' k).isSome := by
              apply accept_nullable'
              simp
              apply accept_nullable'
              exact hr
              apply hk

            simp at h
            rw [accept_highNullable']
            rw [accept_prune]
            exact hk
            simp
            exact hn₁
            apply accept_nullable'
            exact hr
            apply hk
          · rw [accept]
            rw [accept_prune r.star]
            rw [accept_suffix r.star.prune _ (k (s₁, s₂))]
            have tmp :
              (fun l' ↦
                if l'.right.length ≤ s₂.length then
                  r₂.accept l' k
                else k (s₁, s₂)) =
              (fun l' ↦
                if l'.right.length ≤ s₂.length then
                  r₂.prune.accept l' k
                else k (s₁, s₂)) := by
              ext loc' t
              split_ifs with hl
              · rw [accept_prune]
                intro s₃ s₄
                apply hk
              · rfl
            rw [tmp, accept]
            simp [hn₁]
            rw [accept_suffix r.prune.star (fun loc' ↦ r₂.prune.accept loc' k) (k (s₁, s₂))]
            simp
            intro s₃ s₄
            apply accept_nullable'
            exact hr
            apply hk
        · simp [hr]
  | .star r => by
    rw [accept]
    simp
    split_ifs with hn
    · rw [accept_prune r]
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
    · rw [accept, accept_prune r]
      simp

      have : (fun loc' ↦ if loc'.2.length < s₂.length then r.star.accept loc' k else k (s₁, s₂)) =
        (fun loc' ↦ if loc'.2.length < s₂.length then r.prune.star.accept loc' k else k (s₁, s₂)) := by
        ext l x
        simp
        split_ifs
        · rw [accept_prune r.star]
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
  · apply Prod.Lex.right'
    exact hl
    apply Prod.Lex.left
    simp
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

theorem accept_deriv_none' (r : Regex α) (s₁ s₂ : List α) (x : α) (k : Loc α → Option (Loc α)) :
  (r.deriv x).accept (x::s₁, s₂) k = none →
  (r.nullable ∧ r.accept (s₁, x::s₂) k = k (s₁, x::s₂)) ∨ (¬r.nullable ∧ r.accept (s₁, x::s₂) k = none) := by
  induction r generalizing k with
  | zero => simp [accept]
  | one => simp [accept]
  | char c =>
    simp [accept]
    split_ifs with hc
    · simp [accept]
      intro h hc
      exact h
    · simp [accept]
      intro hc'
      absurd hc
      exact hc'
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    intro h₁ h₂
    apply ih₁ at h₁
    apply ih₂ at h₂
    cases h₁ with
    | inl h₁ =>
      rw [h₁.right]
      cases h₂ with
      | inl h₂ =>
        rw [h₂.right]
        simp [h₁.left]
      | inr h₂ =>
        rw [h₂.right]
        simp [h₁.left]
    | inr h₁ =>
      rw [h₁.right]
      cases h₂ with
      | inl h₂ =>
        rw [h₂.right]
        simp [h₂.left]
      | inr h₂ =>
        rw [h₂.right]
        simp [h₁.left, h₂.left]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [accept]
    intro h
    split_ifs at h with hn₁ hn₂
    · simp [accept] at h
      let ⟨h₂, h₁⟩ := h
      clear h
      apply ih₁ at h₁
      apply ih₂ at h₂
      cases h₁ with
      | inl h₁ =>
        rw [h₁.right]
        cases h₂ with
        | inl h₂ =>
          rw [h₂.right]
          simp [h₁.left, h₂.left]
        | inr h₂ =>
          rw [h₂.right]
          simp [h₁.left, h₂.left]
      | inr h₁ =>
        rw [h₁.right]
        cases h₂ with
        | inl h₂ =>
          absurd h₁.left
          exact highNullable_nullable hn₁
        | inr h₂ =>
          absurd h₁.left
          exact highNullable_nullable hn₁
    · simp [accept] at h
      let ⟨h₁, h₂⟩ := h
      clear h
      apply ih₁ at h₁
      apply ih₂ at h₂
      cases h₁ with
      | inl h₁ =>
        rw [h₁.right]
        cases h₂ with
        | inl h₂ =>
          rw [h₂.right]
          simp [h₁.left, h₂.left]
        | inr h₂ =>
          rw [h₂.right]
          simp [h₁.left, h₂.left]
      | inr h₁ =>
        rw [h₁.right]
        cases h₂ with
        | inl h₂ =>
          absurd h₁.left
          exact hn₂
        | inr h₂ =>
          absurd h₁.left
          exact hn₂
    · simp [accept] at h
      apply ih₁ at h
      cases h with
      | inl h =>
        rw [h.right]
        absurd hn₂
        exact h.left
      | inr h =>
        rw [h.right]
        simp [hn₂]
  | star r ih =>
    simp
    rw [accept]
    intro h
    apply ih at h
    cases h with
    | inl h =>
      let ⟨hn, hr⟩ := h
      clear h
      sorry
    | inr h =>
      rw [accept]
      let ⟨hn, hr⟩ := h
      clear h
      rw [accept_not_nullable _ _ _ _ (k (s₁, x::s₂))] at hr
      simp at hr
      simp
      rw [hr]
      simp
      exact hn

theorem accept_deriv (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (loc : Loc α) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
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
    · apply accept_deriv r₁ at h
      exact Or.inl h
      exact hk
    · simp [Regex.deriv, accept] at h
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
        apply accept_deriv r₂
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
          apply accept_deriv (r₁₁.mul r₂) at h
          simp [accept] at h
          exact Or.inl h
          exact hk
        · simp [Regex.deriv] at h
          simp [accept] at h
          cases h with
          | inl h =>
            simp [accept]
            apply accept_deriv (r₁₁.mul r₂) at h
            simp [accept] at h
            exact Or.inl h
            exact hk
          | inr h =>
            let ⟨h₁, h₂⟩ := h
            simp [accept]
            apply accept_deriv (r₁₂.mul r₂) at h₂
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
        apply accept_deriv (r₁₁.mul (r₁₂.mul r₂)) at h
        simp [accept] at h
        exact h
        exact hk
      | .star r =>
        by_cases hn₂ : r₂.nullable
        · simp [hn₂]
          split_ifs with hr
          · intro h
            rw [accept, accept_highNullable']
            apply accept_deriv
            exact hk
            exact h
            simp
            exact hr
            apply accept_nullable'
            exact hn₂
            apply hk
          · intro h
            rw [Regex.deriv] at h
            split_ifs at h with hr₁
            · simp at hr₁
              rw [prune_highNullable_highNullable] at hr₁
              absurd hr
              exact hr₁
            · rw [accept] at h
              simp only [Option.or_eq_some] at h
              cases h with
              | inl h =>
                rw [←prune_star_not_highNullable hr] at h
                rw [accept] at h
                apply accept_deriv at h
                rw [accept]
                have tmp :
                  (fun loc' ↦ r₂.prune.accept loc' k) =
                  (fun loc' ↦ r₂.accept loc' k) := by
                  ext loc' t
                  rw [←accept_prune]
                  exact hk
                rw [tmp] at h
                exact h
                intro s₃ s₄
                rw [←accept_prune]
                apply accept_nullable'
                exact hn₂
                apply hk
                exact hk
              | inr h =>
                let ⟨h₁, h₂⟩ := h
                rw [←prune_star_not_highNullable hr, accept] at h₁

                -- apply accept_deriv_none'' _ _ (r₂.prune.accept (s₁, x::s₂) k) at h₁
                -- rw [accept, accept]



                apply accept_deriv_none_nullable at h₁
                apply accept_deriv r₂ at h₂
                rw [←accept_prune] at h₁

                have tmp :
                  (fun loc' ↦ r₂.prune.accept loc' k) =
                  (fun loc' ↦ r₂.accept loc' k) := by
                  ext loc' t
                  rw [←accept_prune]
                  exact hk

                rw [tmp] at h₁
                rw [accept, h₁]
                exact h₂
                exact hk
                exact hk
                simp
                intro s₃ s₄
                rw [←accept_prune]
                apply accept_nullable'
                exact hn₂
                apply hk
                exact hk


                -- rw [accept, accept]
                -- simp
                -- refine Or.inr ⟨?_, ?_⟩
                -- simp at hn
                -- simp_all
                -- sorry
                -- exact h₂
                -- exact hk
            · simp at *
        · simp only [hn₂, highNullable, nullable, ↓reduceIte]
          intro h
          sorry
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
        rw [←accept_prune]
        exact hk

      rw [this] at h
      apply accept_deriv r at h

      rw [←accept_mul_def] at h
      -- Need to show that (r.mul r.star).accept l k = some loc → r.star.accept l k = some loc
      rw [accept] at h
      by_cases hn₁ : r.nullable
      · have hstar : ∀ s₃ s₄, (r.star.accept (s₃, s₄) k).isSome := by
          intro s₃ s₄
          apply accept_nullable'
          simp
          apply hk
        have h' := accept_nullable r s₁ (x::s₂) (k (s₁, x::s₂)) (fun loc' ↦ r.star.accept loc' k)  hn₁ hstar (hk s₁ (x::s₂))
        cases h' with
        | inl h' =>
          rw [accept]
          simp
          left
          rw [h'] at h
          simp at h
          exact h
        | inr h' =>
          rw [h'] at h
          exact h
      · rw [accept]
        simp
        left
        rw [accept_not_nullable _ _ _ _ (k (s₁, x::s₂))] at h
        simp at h
        exact h
        exact hn₁
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
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

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
