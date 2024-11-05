import GreedyDeriv.Regex
import GreedyDeriv.Greedy

-- a + ab
def r := (Regex.char 'a').plus ((Regex.char 'a').mul (Regex.char 'b'))
#eval r.rmatch "ab".toList

example : Greedy r ⟨['a'], ['b']⟩ := by
  apply Greedy.plus_left _ _ (['a'], ['b'])
  apply Greedy.char

theorem List.append_eq_singleton {α : Type u} {p q : List α} {x : α} :
  p ++ q = [x] → (p = [x] ∧ q = []) ∨ (p = [] ∧ q = [x]) := by
  intro h
  cases p with
  | nil => simp_all
  | cons x xs => simp_all

-- (a + ab)*
def r2 := ((Regex.char 'a').plus ((Regex.char 'a').mul (Regex.char 'b'))).star
#eval r2.rmatch "aab".toList

example : Greedy r2 ⟨['a', 'a'], ['b']⟩ := by
  apply Greedy.star
  apply Greedy.plus_left
  apply Greedy.mul _ _ ['a'] ['a']
  apply Greedy.plus_left
  apply Greedy.char
  apply Greedy.star
  apply Greedy.plus_left
  apply Greedy.mul _ _ ['a'] []
  apply Greedy.plus_left
  apply Greedy.char
  apply Greedy.star
  apply Greedy.plus_right
  intro h
  let ⟨s₃, s₄, hs, h⟩ := h
  simp at hs
  apply List.append_eq_singleton at hs
  cases hs with
  | inl hs' =>
    rw [hs'.left] at h
    cases h with
    | mul h₁ h₂ hs =>
      cases h₁ with
      | plus_left h =>
        cases h
        simp at hs
      | plus_right h =>
        cases h with
        | mul h₁ h₂ hs' =>
          cases h₁
          rw [←hs'] at hs
          simp at hs
  | inr hs =>
    rw [hs.left] at h
    cases h with
    | mul h₁ h₂ hs =>
      cases h₁ with
      | plus_left h =>
        cases h
        simp at hs
      | plus_right h =>
        cases h with
        | mul h₁ h₂ hs' =>
          cases h₁
          rw [←hs'] at hs
          simp at hs
  apply Greedy.one


-- c + ab
def r3 := (Regex.char 'c').plus ((Regex.char 'a').mul (Regex.char 'b'))
#eval r3.rmatch "ab".toList

example : Greedy r3 ⟨['b', 'a'], []⟩ := by
  apply Greedy.plus_right _ _ (['b', 'a'], [])
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

-- a*a
def r5 := (Regex.char 'a').star.mul (Regex.char 'a')
#eval r5.rmatch "aa".toList
#eval r5.gmatch "aa".toList

example : ¬Greedy r5 ⟨['a', 'a'], []⟩ := by
  generalize hs : ['a', 'a'] = s
  intro h
  cases h with
  | mul _ _ s₁ s₂ _  h₁ h₂ =>
    generalize hs₁ : s₁.reverse = s₁'
    generalize hs₂ : s₂.reverse = s₂'
    rw [hs₁] at h₁
    rw [hs₂] at h₂
    cases h₂
    cases h₁ with
    | star _ _ h' =>
      cases h' with
      | plus_left _ _ _ h =>
        cases h with
        | mul _ _ s₁' s₂' _ h₁ h₂ =>
          generalize hs₁' : s₁'.reverse = s₁''
          rw [hs₁'] at h₁
          cases h₁
          simp [hs₂] at hs
          simp [hs₁', hs] at hs₁
          simp [hs₁] at h₂
          cases h₂ with
          | star _ _ h' =>
            cases h' with
            | plus_left _ _ _ h =>
              generalize hs₁'' : [] = s₁''
              rw [hs₁''] at h
              cases h with
              | mul _ _ _ _ _ h₁ =>
                simp at hs₁''
                rw [hs₁''.right] at h₁
                cases h₁
            | plus_right _ _ _ h =>
              simp at hs₂
              rw [hs₂] at h
              absurd h
              use ['a']
              simp
              apply Regex.matches'.mul
              apply Regex.matches'.char
              apply Regex.matches'.star_nil
              simp
      | plus_right _ _ _ _ h' =>
        simp [hs₁, hs₂] at hs
        rw [←hs] at h'
        cases h'
