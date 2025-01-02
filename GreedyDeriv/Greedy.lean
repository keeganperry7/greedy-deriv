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

theorem accept_star_def (r : Regex α) (loc : Loc α) (k : Loc α → Option (Loc α)) :
  r.star.accept loc k = (r.accept loc (fun loc' => if loc'.right.length < loc.right.length then r.star.accept loc' k else none)).or (k loc) := by
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

      have tmp :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦ r₂.accept l₁ fun l₂ ↦
              if l₂.2.length ≤ s₂.length then
                k l₂
              else x
          else none) =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              r₂.accept l₁ fun l₂ ↦
                if l₂.2.length ≤ s₂.length then
                  k l₂
                else x
              else x
          else none) := by
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
          else none) =
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
          else none) := by
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
          else none) =
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
          else none) := by
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
          else none) =
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
          else none) := by

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
          else none) =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              if l₁.2.length < s₂.length then
                r₂.accept l₁ fun l₂ ↦
                  k l₂
              else x
            else x
          else none) := by
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
          else none) =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
            if l₁.2.length ≤ loc'.2.length then
              r₂.accept l₁ fun l₂ ↦
                k l₂
            else x
          else none) := by
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
          else none) =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              r₂.accept l₁ fun l₂ ↦ k l₂
          else none) := by
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
        else none) =
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' fun l' ↦
          if l'.2.length ≤ loc'.2.length then
            if l'.2.length ≤ s₂.length then
              k l'
            else x
          else x
        else none) := by
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
        else none) =
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' fun l' ↦
          if l'.2.length ≤ loc'.2.length then
              k l'
          else x
        else none) := by
      ext loc' t
      split_ifs with hl
      · rw [if_cond'']
        exact hl
      · rfl

    have tmp₃ :
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' k
        else none) =
      (fun loc' ↦
        if loc'.2.length < s₂.length then
          r.star.accept loc' (fun l' =>
            if l'.2.length ≤ loc'.2.length then
              k l'
            else x)
        else none) := by
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

theorem accept_nullable (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hn : r.nullable) (hk : (k (s₁, s₂)).isSome) :
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

theorem accept_highNullable {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : r.highNullable) (hk : (k (s₁, s₂)).isSome) :
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
    apply accept_nullable
    apply highNullable_nullable
    exact hn.right
    exact hk
  | star r ih => simp at hn

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

      have tmp :
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              r₂.accept l₁ fun l₂ ↦
                if l₂.2.length < s₂.length then
                  k l₂
                else x
          else none) =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length < s₂.length then
                    k l₂
                  else x
              else x
          else none) := by
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
          else none) =
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
          else none) := by
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
          else none) =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              if l₁.2.length ≤ loc'.2.length then
                r₂.accept l₁ fun l₂ ↦
                  if l₂.2.length ≤ l₁.2.length then
                    k l₂
                  else x
              else x
          else none) := by
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
          else none) =
        (fun loc' ↦
          if loc'.2.length < s₂.length then
            r.star.accept loc' fun l₁ ↦
              r₂.accept l₁ fun l₂ ↦ k l₂
          else none) := by
        simp_rw [accept_suffix r.star (fun l₁ ↦ r₂.accept l₁ (fun l₂ ↦ k l₂)) x]
        simp_rw [accept_suffix r₂ (fun l₂ ↦ k l₂) x]
        simp

      rw [tmp, tmp₁, tmp₂, tmp₃]
      simp [hn]
  | .star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_cond (r : Regex α) (s₁ s₂ : List α) (x : α) (k : Loc α → Option (Loc α)) :
  (r.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) (fun l' ↦ if l'.right.length < (x::s₂).length then k l' else none) :=
  match r with
  | zero => by simp [accept]
  | one => by simp [accept]
  | char c => by
    simp [accept]
    split_ifs
    · simp [accept]
    · simp [accept]
  | plus r₁ r₂ => by
    simp [accept]
    rw [accept_deriv_cond, accept_deriv_cond]
    simp
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      rw [accept_deriv_cond]
      simp
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
      simp
      simp_rw [accept_suffix r.star (fun loc' ↦ r₂.accept loc' fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
      simp

      have tmp :
        (fun loc ↦
          if loc.2.length < s₂.length + 1 then
            r.star.accept loc fun l ↦
              if l.2.length ≤ loc.2.length then
                r₂.accept l fun l' ↦
                  if l'.2.length < s₂.length + 1 then
                    k l'
                  else none
              else none
          else none) =
        (fun loc' ↦
          if loc'.2.length < s₂.length + 1 then
            r.star.accept loc' fun l' ↦ r₂.accept l' k
          else none) := by
        simp_rw [accept_suffix r₂ (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
        simp
        ext loc t
        split_ifs with hl
        · have tmp₁ :
            (fun l ↦
              if l.2.length ≤ loc.2.length then
                r₂.accept l fun l' ↦
                  if l'.2.length ≤ l.2.length then
                    if l'.2.length < s₂.length + 1 then
                      k l'
                    else none
                  else none
              else none) =
            (fun l ↦
              if l.2.length ≤ loc.2.length then
                r₂.accept l fun l' ↦
                  if l'.2.length ≤ l.2.length then
                      k l'
                  else none
              else none) := by
            ext l u
            split_ifs with h₁
            · have tmp₂ :
                (fun l' ↦
                  if l'.2.length ≤ l.2.length then
                    if l'.2.length < s₂.length + 1 then
                      k l'
                    else none
                  else none) =
                (fun l' ↦
                  if l'.2.length ≤ l.2.length then
                      k l'
                  else none) := by
                ext l' v
                split_ifs with h₂ h₃
                · rfl
                · absurd h₃
                  apply Nat.lt_of_le_of_lt
                  exact h₂
                  apply Nat.lt_of_le_of_lt
                  exact h₁
                  exact hl
                · rfl
              rw [tmp₂]
            · rfl
          rw [tmp₁]
          nth_rw 2 [accept_suffix r.star _ none]
          simp_rw [accept_suffix r₂ k none]
          simp
        · rfl

      rw [tmp]
      simp_rw [accept_mul_def]
  | .star r => by
    simp
    rw [accept, accept_deriv_cond r]
    simp
    rw [accept]
    simp_rw [accept_suffix r.star (fun l' ↦ if l'.2.length < s₂.length + 1 then k l' else none) none]
    simp

    have tmp :
      (fun loc ↦
        if loc.2.length < s₂.length + 1 then
          r.star.accept loc fun l ↦
            if l.2.length ≤ loc.2.length then
              if l.2.length < s₂.length + 1 then
                k l
              else none
            else none
        else none) =
      (fun loc ↦
        if loc.2.length < s₂.length + 1 then
          r.star.accept loc k
        else none) := by
      ext loc t
      split_ifs with hl
      · have tmp₁ :
          (fun l ↦
            if l.2.length ≤ loc.2.length then
              if l.2.length < s₂.length + 1 then
                k l
              else none
            else none) =
          (fun l ↦ if l.2.length ≤ loc.2.length then k l else none) := by
          ext l u
          split_ifs with h₁ h₂
          · rfl
          · absurd h₂
            apply Nat.lt_of_le_of_lt
            exact h₁
            exact hl
          · rfl
        rw [tmp₁, accept_suffix r.star k none]
        rfl
      · rfl
    rw [tmp]
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_cont_none (r : Regex α) (s₁ s₂ : List α) :
  r.accept (s₁, s₂) (fun _ ↦ none) = none :=
  match r with
  | zero => by simp [accept]
  | one => by simp [accept]
  | char c => by
    cases s₂ with
    | nil => simp [accept]
    | cons x xs => simp [accept]
  | plus r₁ r₂ => by
    simp [accept]
    rw [accept_cont_none, accept_cont_none]
    simp
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      rw [accept_cont_none]
    | char c =>
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
        ext l t
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
      ext l t
      split_ifs with hl
      · rw [accept_cont_none]
      · rfl

    rw [star_none, accept_cont_none]
termination_by (s₂.length, r.size, r.left.size)
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · apply Prod.Lex.right
    apply Prod.Lex.right' <;> (simp; omega)
  · apply Prod.Lex.right'
    exact hl
    apply Prod.Lex.left
    simp
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

theorem accept_nil_not_nullable_iff {r : Regex α} {s : List α} {k : Loc α → Option (Loc α)} (hk : (k (s, [])).isSome) :
  r.accept (s, []) k = none ↔ ¬r.nullable :=
  match r with
  | zero => by
    simp [accept]
  | one => by
    simp [accept]
    rw [←ne_eq, Option.ne_none_iff_isSome]
    exact hk
  | char c => by simp [accept]
  | plus r₁ r₂ => by
    simp [accept]
    rw [accept_nil_not_nullable_iff hk, accept_nil_not_nullable_iff hk]
    simp
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      rw [accept_nil_not_nullable_iff hk]
      simp
    | char c => simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def]
      rw [accept_nil_not_nullable_iff hk, accept_nil_not_nullable_iff hk]
      simp
      tauto
    | mul r₁₁ r₁₂ =>
      simp [accept]
      simp_rw [←accept_mul_def]
      rw [accept_nil_not_nullable_iff hk]
      simp
    | .star r =>
      rw [accept, accept]
      simp
      rw [accept_cont_none, accept_nil_not_nullable_iff hk]
      simp
  | .star r => by
    simp
    rw [←ne_eq, Option.ne_none_iff_isSome]
    apply accept_nullable
    simp only [nullable]
    exact hk
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_nil_not_nullable {r : Regex α} {s : List α} {k : Loc α → Option (Loc α)} (hr : ¬r.nullable) :
  r.accept (s, []) k = none :=
  match r with
  | zero => by simp [accept]
  | one => by simp at hr
  | char c => by simp [accept]
  | plus r₁ r₂ => by
    simp at hr
    simp [accept]
    rw [accept_nil_not_nullable, accept_nil_not_nullable]
    simp
    simp [hr.right]
    simp [hr.left]
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp [accept]
      simp at hr
      rw [accept_nil_not_nullable]
      simp [hr]
    | char c => simp [accept]
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
  | .star _ => by simp at hr
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_nil_nullable {r : Regex α} {s : List α} {k : Loc α → Option (Loc α)} (hr : r.nullable) :
  r.accept (s, []) k = k (s, []) :=
  match r with
  | zero => by simp at hr
  | one => by simp [accept]
  | char _ => by simp at hr
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
    | zero => simp at hr
    | one =>
      simp at hr
      simp [accept]
      rw [accept_nil_nullable hr]
    | char c => simp at hr
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
  | .star r => by
    rw [accept]
    simp
    rw [accept_cont_none]
    simp
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

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
      apply accept_nullable
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
      apply accept_nullable
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
          apply accept_nullable
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
        rw [accept, accept]
        rw [accept_suffix r.star _ none]
        nth_rw 2 [accept_suffix r.star _ none]

        have hr₂_prune :
          (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.prune.accept l' k else none) =
          (fun l' ↦ if l'.right.length ≤ s₂.length then r₂.accept l' k else none) := by
          ext l t
          split_ifs with hl
          · rw [accept_prune r₂ _ _ k hk]
          · rfl

        rw [hr₂_prune]
  | .star r => by
    simp
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
  · apply Prod.Lex.right'
    exact hl
    apply Prod.Lex.left
    simp

theorem accept_deriv_none {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : ¬r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
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
    exact hk
    simp [hn.left]
    exact hk
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
        exact hk
        exact h
      | char c =>
        simp at h
        split_ifs at h with hc
        · simp [accept, hc]
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
          exact hk
          simp_all
          exact hk
      | mul r₁₁ r₁₂ =>
        simp at h
        apply @accept_deriv_none _ (r₁₁.mul (r₁₂.mul r₂)) at h
        simp [accept]
        simp [accept] at h
        exact h
        simp_all
        exact hk
      | .star r =>
        simp at h hn
        rw [accept, accept] at h
        rw [accept_deriv_cond] at h
        simp at h
        let ⟨h₁, h₂⟩ := h
        clear h
        apply @accept_deriv_none _ r₂ at h₂
        simp_rw [accept_mul_def] at h₁
        rw [accept, accept]
        simp
        refine ⟨?_, h₂⟩
        simp_rw [←accept_prune r₂ _ _ k hk] at h₁
        exact h₁
        simp [hn]
        exact hk
  | .star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_none_nullable {r : Regex α} {s₁ s₂ : List α} {k : Loc α → Option (Loc α)} (hn : r.nullable) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) :
  (r.prune.deriv x).accept (x :: s₁, s₂) k = none →
  r.accept (s₁, x::s₂) k = k (s₁, x::s₂) :=
  match r with
  | zero => by simp at hn
  | one => by simp [accept]
  | char c => by simp at hn
  | plus r₁ r₂ => by
    simp at hn
    simp [accept]
    intro h
    split_ifs at h with hr₁ hr₂
    · rw [accept_highNullable]
      rw [Option.or_of_isSome]
      apply hk
      exact hr₁
      apply hk
    · apply accept_deriv_none_nullable hr₂ hk at h
      rw [h]
      rw [Option.or_of_isSome]
      apply hk
    · simp [accept] at h
      let ⟨h₁, h₂⟩ := h
      clear h
      apply accept_deriv_none at h₁
      apply accept_deriv_none_nullable at h₂
      rw [h₁, h₂]
      simp
      exact Or.resolve_left hn hr₂
      exact hk
      exact hr₂
      exact hk
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp at hn
    | one =>
      simp [accept]
      simp at hn
      split_ifs with hr
      · simp [accept]
        rw [accept_highNullable]
        exact hr
        apply hk
      · intro h
        apply accept_deriv_none_nullable at h
        exact h
        exact hn
        exact hk
    | char c => simp at hn
    | plus r₁₁ r₁₂ =>
      simp [accept]
      simp at hn
      split_ifs with hr₁ hr₂
      · simp [accept]
        rw [accept_highNullable hr₁.left, accept_highNullable hr₁.right]
        rw [Option.or_of_isSome]
        apply hk
        apply hk
        apply accept_nullable
        exact hn.right
        apply hk
      · intro h
        apply accept_deriv_none_nullable (by simp [hr₂]) hk at h
        simp [accept] at h
        rw [h, Option.or_of_isSome]
        apply hk
      · simp_all
        simp [accept]
        intro h₁ h₂
        apply accept_deriv_none (by simp [hr₂]) hk at h₁
        apply accept_deriv_none_nullable (by simp [hn]) hk at h₂
        simp [accept] at h₁ h₂
        rw [h₁, h₂]
        simp
    | mul r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hr
      · simp [accept]
        rw [accept_highNullable hr.left.left, accept_highNullable hr.left.right, accept_highNullable hr.right]
        apply hk
        apply accept_nullable
        exact highNullable_nullable hr.right
        apply hk
        apply accept_nullable
        exact highNullable_nullable hr.left.right
        apply accept_nullable
        exact highNullable_nullable hr.right
        apply hk
      · intro h
        apply accept_deriv_none_nullable at h
        simp [accept] at h
        exact h
        simp at hn
        simp [hn]
        exact hk
    | .star r =>
      simp
      rw [accept, accept]
      simp
      rw [accept_deriv_cond, accept, accept]
      simp
      intro h₁ h₂
      simp_rw [accept_mul_def, ←accept_prune r₂ _ _ k hk] at h₁
      simp at hn
      apply accept_deriv_none_nullable hn hk at h₂
      rw [h₁, h₂]
      simp
  | .star r => by
    simp
    rw [accept, accept_deriv_cond, accept]
    simp
    intro h
    rw [h]
    simp
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

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
        exact hk
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
            · have h := accept_deriv_none (by simp [hn']) hk h₁
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
        simp
        rw [accept, accept, accept_deriv_cond]
        intro h
        simp at h
        simp_rw [accept_mul_def] at h
        simp_rw [←accept_prune r₂ _ _ k hk] at h
        cases h with
        | inl h =>
          rw [accept, accept]
          simp
          exact Or.inl h
        | inr h =>
          let ⟨h₁, h₂⟩ := h
          clear h
          apply accept_deriv r₂ _ _ k loc hk at h₂
          rw [accept, accept]
          simp
          exact Or.inr ⟨h₁, h₂⟩
  | .star r => by
    simp
    rw [accept, accept_deriv_cond, accept]
    simp
    intro h
    exact Or.inl h
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)

theorem accept_deriv_not_nullable (r : Regex α) (s₁ s₂ : List α) (k : Loc α → Option (Loc α)) (hk : ∀ s₃ s₄, (k (s₃, s₄)).isSome) (hn : ¬r.nullable) :
  (r.prune.deriv x).accept (x::s₁, s₂) k = r.accept (s₁, x::s₂) k :=
  match r with
  | zero => by simp [accept]
  | one => by simp at hn
  | char c => by
    simp [accept]
    split_ifs with hc
    · simp [accept]
    · simp [accept]
  | plus r₁ r₂ => by
    simp at hn
    simp [accept]
    split_ifs with hr₁ hr₂
    · absurd (highNullable_nullable hr₁)
      simp [hn]
    · absurd hr₂
      simp [hn]
    · simp [accept]
      rw [accept_deriv_not_nullable, accept_deriv_not_nullable]
      exact hk
      simp [hn]
      exact hk
      simp [hn]
  | mul r₁ r₂ => by
    match r₁ with
    | zero => simp [accept]
    | one =>
      simp at hn
      simp [accept]
      split_ifs with hr
      · absurd (highNullable_nullable hr)
        simp [hn]
      · rw [accept_deriv_not_nullable]
        exact hk
        simp [hn]
    | char c =>
      simp [accept]
      split_ifs
      · rfl
      · simp [accept]
    | plus r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hr₁ hr₂
      · simp at hn
        have hr₁₁ := highNullable_nullable hr₁.left
        simp [hr₁₁] at hn
        absurd (highNullable_nullable hr₁.right)
        simp [hn]
      · simp_all
      · simp [accept]
        rw [accept_deriv_not_nullable, accept_deriv_not_nullable]
        simp [accept]
        exact hk
        simp_all
        exact hk
        simp_all
    | mul r₁₁ r₁₂ =>
      simp [accept]
      split_ifs with hr
      · absurd hn
        simp
        exact ⟨⟨highNullable_nullable hr.left.left, highNullable_nullable hr.left.right⟩, highNullable_nullable hr.right⟩
      · rw [accept_deriv_not_nullable]
        simp [accept]
        exact hk
        simp at *
        tauto
    | .star r =>
      simp at hn
      simp
      rw [accept, accept, accept_deriv_not_nullable r₂]
      rw [accept_deriv_cond, accept, accept]
      simp_rw [accept_mul_def, ←accept_prune r₂ _ _ k hk]
      simp
      exact hk
      simp [hn]
  | .star r => by simp at hn
termination_by (r.size, r.left.size)
decreasing_by all_goals (simp only [left, size]; omega)
