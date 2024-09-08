import GreedyDeriv.Regex
import GreedyDeriv.Greedy

-- a + ab
def r := (Regex.char 'a').plus ((Regex.char 'a').mul (Regex.char 'b'))
#eval r.rmatch "ab".toList

example : Greedy r ⟨['a'], ['b']⟩ := by
  apply Greedy.plus_left _ _ ['a'] ['b']
  apply Greedy.char

-- (a + ab)*
def r2 := ((Regex.char 'a').plus ((Regex.char 'a').mul (Regex.char 'b'))).star
#eval r2.rmatch "aab".toList

example : Greedy r2 ⟨['a', 'a'], ['b']⟩ := by
  apply Greedy.star _ ['a'] ['a'] ['b']
  apply Greedy.plus_left
  apply Greedy.char
  apply Greedy.star _ ['a'] [] ['b']
  apply Greedy.plus_left
  apply Greedy.char
  apply Greedy.star_nil

-- c + ab
def r3 := (Regex.char 'c').plus ((Regex.char 'a').mul (Regex.char 'b'))
#eval r3.rmatch "ab".toList

example : Greedy r3 ⟨['b', 'a'], []⟩ := by
  apply Greedy.plus_right _ _ ['a', 'b']
  intro ⟨s₁, s₂, hs, h⟩
  cases h
  simp at hs
  apply Greedy.mul _ _ ['a'] ['b']
  apply Greedy.char
  apply Greedy.char

-- (a + aa)a
def r4 := ((Regex.char 'a').plus ((Regex.char 'a').mul (Regex.char 'a'))).mul (Regex.char 'a')
#eval r4.rmatch "aaa".toList

example : Greedy r4 ⟨['a', 'a'], ['a']⟩ := by
  apply Greedy.mul _ _ ['a'] ['a'] ['a']
  apply Greedy.plus_left
  apply Greedy.char
  apply Greedy.char
