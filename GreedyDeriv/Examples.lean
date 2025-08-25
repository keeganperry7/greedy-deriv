import GreedyDeriv.Regex
import GreedyDeriv.Greedy

open Regex

/-- Implicit coercion to convert strings to regexes -/
instance : Coe String (Regex Char) where
  coe s := s.toList |>.map char |>.foldr Regex.mul epsilon

/-- Implicit coercion to convert characters to regexes -/
instance : Coe Char (Regex Char) where
  coe := char

/-- Implicit coercion to convert strings to initial locations -/
instance : Coe String (Loc Char) where
  coe := ([], String.toList ·)

-- a + ab
def r : Regex (Char) := plus 'a' "ab"
#guard r.matchEnd "ab" = some ⟨['a'], ['b']⟩
#guard r.matchEnd "ab" = r.gmatch "ab"

-- (a + ab)*
def r2 : Regex (Char) := (plus 'a' "ab").star false
#guard r2.matchEnd "aab" = some ⟨['a', 'a'], ['b']⟩
#guard r2.matchEnd "aab" = r2.gmatch "aab"

-- c + ab
def r3 : Regex (Char) := plus 'c' (mul 'a' 'b')
#guard r3.matchEnd "ab" = some ⟨['b', 'a'], []⟩
#guard r3.matchEnd "ab" = r3.gmatch "ab"

-- (a + aa)a
def r4 : Regex (Char) := (plus 'a' "aa").mul 'a'
#guard r4.matchEnd "aaa" = some ⟨['a', 'a'], ['a']⟩
#guard r4.matchEnd "aaa" = r4.gmatch "aaa"

-- a*a
def r5 : Regex (Char) := (star 'a' false).mul 'a'
#guard r5.matchEnd "aa" = some ⟨['a', 'a'], []⟩
#guard r5.matchEnd "aa" = r5.gmatch "aa"

-- (ε + b)*
def r6 : Regex (Char) := (epsilon.plus 'b').star false
#guard r6.matchEnd "bb" = some ⟨['b', 'b'], []⟩
#guard r6.matchEnd "bb" = r6.gmatch "bb"

-- (ε + b)(ε + b)*
def r6' : Regex (Char) := (epsilon.plus 'b').mul ((epsilon.plus 'b').star false)
#guard r6'.matchEnd "bb" = some ⟨['b', 'b'], []⟩
#guard r6'.matchEnd "bb" = r6'.gmatch "bb"

-- (a + ε + b)*
def r7 : Regex (Char) := (plus 'a' (epsilon.plus 'b')).star false
#guard r7.matchEnd "aaaabbb" = some ⟨['b', 'b', 'b', 'a', 'a', 'a', 'a'], []⟩
#guard r7.matchEnd "aaaabbb" = r7.gmatch "aaaabbb"

-- (ε + a)b
def r8 : Regex (Char) := (epsilon.plus 'a').mul 'b'
#guard r8.matchEnd "ab" = some ⟨['b', 'a'], []⟩
#guard r8.matchEnd "ab" = r8.gmatch "ab"

-- ((a + ε + b) + b)
def r9 : Regex (Char) := Regex.plus ((plus 'a' epsilon).plus 'b') 'b'
#guard r9.matchEnd "b" = some ⟨[], ['b']⟩
#guard r9.gmatch "b" = r9.matchEnd "b"

-- (ε + a)*b
def r10 : Regex (Char) := ((Regex.plus epsilon 'a').star false).mul 'b'
#guard r10.matchEnd "ab" = some ⟨['b', 'a'], []⟩
#guard r10.gmatch "ab" = r10.matchEnd "ab"

-- (a + ε)*(ε + b)
def r11 : Regex (Char) := ((Regex.plus 'a' epsilon).star false).mul (Regex.plus (epsilon) 'b')
#guard r11.matchEnd "ab" = some ⟨['a'], ['b']⟩
#guard r11.gmatch "ab" = r11.matchEnd "ab"

-- (ε + a)*(ε + b)
def r12 : Regex (Char) := ((Regex.plus epsilon 'a').star false).mul (Regex.plus (epsilon) 'b')
#guard r12.matchEnd "ab" = some ⟨['a'], ['b']⟩
#guard r12.gmatch "ab" = r12.matchEnd "ab"

-- (a + ε + b)*b
def r13 : Regex (Char) := ((Regex.plus 'a' (Regex.plus epsilon 'b')).star false).mul 'b'
#guard r13.matchEnd "bb" = some ⟨['b', 'b'], []⟩
#guard r13.gmatch "bb" = r13.matchEnd "bb"

-- a*?a
def r14 : Regex (Char) := (star 'a' true).mul 'a'
#guard r14.matchEnd "aaa" = some ⟨['a'], ['a', 'a']⟩
#guard r14.matchEnd "aaa" = r14.gmatch "aaa"

-- a*?b
def r15 : Regex (Char) := (star 'a' true).mul 'b'
#guard r15.matchEnd "aab" = some ⟨['b', 'a', 'a'], []⟩
#guard r15.matchEnd "aab" = r15.gmatch "aab"

-- (a + ε + b)*?b
def r16 : Regex (Char) := (star (plus 'a' (plus epsilon 'b')) true).mul 'b'
#guard r16.matchEnd "aabb" = some ⟨['b', 'a', 'a'], ['b']⟩
#guard r16.matchEnd "aabb" = r16.gmatch "aabb"

-- (aa + aaa)*
def r17 : Regex (Char) := (star (plus "aa" "aaa") false)
#guard r17.matchEnd "aaa" = some ⟨['a', 'a'], ['a']⟩
#guard r17.matchEnd "aaa" = r17.gmatch "aaa"

-- (a + b*?)*
def r18 : Regex Char := (star (plus 'a' (star 'b' true)) false)
#guard r18.matchEnd "aaabbb" = some ⟨['b', 'b', 'b', 'a', 'a', 'a'], []⟩
#guard r18.matchEnd "aaabbb" = r18.gmatch "aaabbb"
