import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

theorem matchEnd_accept_none (r : Regex α) (s₁ s₂ : List α) :
  r.matchEnd (s₁, s₂) = none → r.accept (s₁, s₂) some = none := by
  induction s₂ generalizing r s₁ with
  | nil =>
    intro h
    simp [Regex.matchEnd] at h
    rw [accept_nil_not_nullable_iff]
    simp [h]
    simp
  | cons x xs ih =>
    intro h
    simp [Regex.matchEnd] at h
    cases k : ((r.prune.deriv x).matchEnd (x :: s₁, xs)) with
    | none =>
      rw [k] at h
      simp at h
      apply ih at k
      rw [accept_deriv_not_nullable] at k
      exact k
      simp
      simp [h]
    | some =>
      rw [k] at h
      simp at h

theorem matchEnd_accept_some (r : Regex α) (s₁ s₂ : List α) (loc : Loc α) :
  r.matchEnd (s₁, s₂) = some loc → r.accept (s₁, s₂) some = some loc := by
  induction s₂ generalizing r s₁ with
  | nil =>
    intro h
    simp [Regex.matchEnd] at h
    rw [←h.right, accept_nil_nullable h.left]
  | cons x xs ih =>
    intro h
    simp [Regex.matchEnd] at h
    cases k : (r.prune.deriv x).matchEnd (x :: s₁, xs) with
    | none =>
      rw [k] at h
      simp at h
      apply matchEnd_accept_none at k
      rw [←h.right]
      apply accept_deriv_none_nullable at k
      exact k
      exact h.left
      simp
    | some v =>
      rw [k] at h
      simp at h
      rw [h] at k
      apply ih at k
      apply accept_deriv
      simp
      exact k

theorem rmatch_gmatch (r : Regex α) (s : List α) (v : Option (Loc α)) :
  r.rmatch s = v → r.gmatch s = v := by
  intro h
  rw [Regex.rmatch] at h
  cases v with
  | none =>
    apply matchEnd_accept_none
    exact h
  | some l =>
    apply matchEnd_accept_some
    exact h
