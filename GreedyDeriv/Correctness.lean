import GreedyDeriv.Regex
import GreedyDeriv.Greedy

variable {α : Type u} [DecidableEq α]

theorem zero_rmatch (s : List α) :
  Regex.zero.rmatch s = none := by
  induction s with
  | nil => simp [Regex.rmatch, Regex.matchEnd]
  | cons x xs ih =>
    simp [Regex.rmatch, Regex.matchEnd]
    sorry

-- Main correctness theorem
theorem rmatch_greedy (r : Regex α) (s : List α) (loc : Loc α) :
  r.rmatch s = some loc → Greedy r loc := by
  intro h
  induction r with
  | zero => sorry
  | one => sorry
  | char => sorry
  | plus => sorry
  | mul => sorry
  | star => sorry
