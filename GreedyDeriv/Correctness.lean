import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

theorem matchEnd_accept (r : Regex α) (s₁ s₂ : List α) :
  r.matchEnd (s₁, s₂) = r.accept (s₁, s₂) some := by
  induction s₂ generalizing r s₁ with
  | nil =>
    simp [Regex.matchEnd]
    split_ifs with hn
    · rw [accept_nil_nullable hn]
    · rw [accept_nil_not_nullable]
      exact hn
  | cons x xs ih =>
    simp [Regex.matchEnd]
    cases k : ((r.prune.deriv x).matchEnd (x :: s₁, xs)) with
    | none =>
      simp
      rw [ih] at k
      split_ifs with hn
      · apply accept_deriv_none_nullable at k
        rw [k]
        exact hn
        simp
      · apply accept_deriv_none at k
        rw [k]
        exact hn
        simp
    | some v =>
      simp
      rw [ih] at k
      apply accept_deriv at k
      rw [k]
      simp

theorem rmatch_gmatch (r : Regex α) (s : List α) :
  r.rmatch s = r.gmatch s := by
  rw [Regex.rmatch, Regex.gmatch]
  apply matchEnd_accept
