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
#eval r.matchEnd "ab"
#eval r.gmatch "ab"

-- (a + ab)*
def r2 : Regex (Char) := (plus 'a' "ab").star false
#eval r2.matchEnd "aab"
#eval r2.gmatch "aab"

-- c + ab
def r3 : Regex (Char) := plus 'c' (mul 'a' 'b')
#eval r3.matchEnd "ab"
#eval r3.gmatch "ab"

-- (a + aa)a
def r4 : Regex (Char) := (plus 'a' "aa").mul 'a'
#eval r4.matchEnd "aaa"
#eval r4.gmatch "aaa"

-- a*a
def r5 : Regex (Char) := (star 'a' false).mul 'a'
#eval r5.matchEnd "aa"
#eval r5.gmatch "aa"

-- (ε + b)*
def r6 : Regex (Char) := (epsilon.plus 'b').star false
#eval r6.matchEnd "bb"
#eval r6.gmatch "bb"

-- (ε + b)(ε + b)*
def r6' : Regex (Char) := (epsilon.plus 'b').mul ((epsilon.plus 'b').star false)
#eval r6'.matchEnd "bb"
#eval r6'.gmatch "bb"

-- (a + ε + b)*
def r7 : Regex (Char) := (plus 'a' (epsilon.plus 'b')).star false
#eval r7.matchEnd "aaaabbb"
#eval r7.gmatch "aaaabbb"

-- (ε + a)b
def r8 : Regex (Char) := (epsilon.plus 'a').mul 'b'
#eval r8.matchEnd "ab"
#eval r8.gmatch "ab"

-- ((a + ε + b) + b)
def r9 : Regex (Char) := Regex.plus ((plus 'a' epsilon).plus 'b') 'b'
#eval r9.gmatch "b"
#eval r9.matchEnd "b"

-- (ε + a)*b
def r10 : Regex (Char) := ((Regex.plus epsilon 'a').star false).mul 'b'
#eval r10.gmatch "ab"
#eval r10.matchEnd "ab"

-- (a + ε)*(ε + b)
def r11 : Regex (Char) := ((Regex.plus 'a' epsilon).star false).mul (Regex.plus (epsilon) 'b')
#eval r11.gmatch "ab"
#eval r11.matchEnd "ab"

-- (ε + a)*(ε + b)
def r12 : Regex (Char) := ((Regex.plus epsilon 'a').star false).mul (Regex.plus (epsilon) 'b')
#eval r12.gmatch "ab"
#eval r12.matchEnd "ab"

-- (a + ε + b)*b
def r13 : Regex (Char) := ((Regex.plus 'a' (Regex.plus epsilon 'b')).star false).mul 'b'
#eval r13.gmatch "bb"
#eval r13.matchEnd "bb"

-- a*?a
def r14 : Regex (Char) := (star 'a' true).mul 'a'
#eval r14.matchEnd "aaa"
#eval r14.gmatch "aaa"

-- a*?b
def r15 : Regex (Char) := (star 'a' true).mul 'b'
#eval r15.matchEnd "aab"
#eval r15.gmatch "aab"

-- (a + ε + b)*?b
def r16 : Regex (Char) := (star (plus 'a' (plus epsilon 'b')) true).mul 'b'
#eval r16.matchEnd "aabb"
#eval r16.gmatch "aabb"

-- (aa + aaa)*
def r17 : Regex (Char) := (star (plus "aa" "aaa") false)
#eval r17.matchEnd "aaa"
#eval r17.gmatch "aaa"

-- (a + b*?)*
def r18 : Regex Char := (star (plus 'a' (star 'b' true)) false)
#eval r18.matchEnd "aaabbb"
#eval r18.gmatch "aaabbb"
