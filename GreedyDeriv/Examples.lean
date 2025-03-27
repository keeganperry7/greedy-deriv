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
#eval r.matchEnd "ab" = r.gmatch "ab"

-- (a + ab)*
def r2 : Regex (Char) := (plus 'a' "ab").star
#eval r2.matchEnd "aab" = r2.gmatch "aab"

-- c + ab
def r3 : Regex (Char) := plus 'c' (mul 'a' 'b')
#eval r3.matchEnd "ab" = r3.gmatch "ab"

-- (a + aa)a
def r4 : Regex (Char) := (plus 'a' "aa").mul 'a'
#eval r4.matchEnd "aaa" = r4.gmatch "aaa"

-- a*a
def r5 : Regex (Char) := (star 'a').mul 'a'
#eval r5.matchEnd "aa" = r5.gmatch "aa"

-- (ε + b)*
def r6 : Regex (Char) := (epsilon.plus 'b').star
#eval r6.matchEnd "bb" = r6.gmatch "bb"

-- (ε + b)(ε + b)*
def r6' : Regex (Char) := (epsilon.plus 'b').mul ((epsilon.plus 'b').star)
#eval r6'.matchEnd "bb" = r6'.gmatch "bb"

-- (a + ε + b)*
def r7 : Regex (Char) := (plus 'a' (epsilon.plus 'b')).star
#eval r7.matchEnd "aaaabbb" = r7.gmatch "aaaabbb"

-- (ε + a)b
def r8 : Regex (Char) := (epsilon.plus 'a').mul 'b'
#eval r8.matchEnd "ab" = r8.gmatch "ab"

-- ((a + ε + b) + b)
def r9 : Regex (Char) := Regex.plus ((plus 'a' epsilon).plus 'b') 'b'
#eval r9.matchEnd "b" = r9.gmatch "b"

-- (ε + a)*b
def r10 : Regex (Char) := ((Regex.plus epsilon 'a').star).mul 'b'
#eval r10.matchEnd "ab" = r10.gmatch "ab"

-- (a + ε)*(ε + b)
def r11 : Regex (Char) := ((Regex.plus 'a' epsilon).star).mul (Regex.plus (epsilon) 'b')
#eval r11.matchEnd "ab" = r11.gmatch "ab"

-- (ε + a)*(ε + b)
def r12 : Regex (Char) := ((Regex.plus epsilon 'a').star).mul (Regex.plus (epsilon) 'b')
#eval r12.matchEnd "ab" = r12.gmatch "ab"

-- (ε + a)*ε
def r12' : Regex (Char) := ((Regex.plus epsilon 'a').star).mul epsilon
#eval r12'.gmatch "ab" = r12'.matchEnd "ab"

-- (a + ε + b)*b
def r13 : Regex (Char) := ((Regex.plus 'a' (Regex.plus epsilon 'b')).star).mul 'b'
#eval r13.matchEnd "bb" = r13.gmatch "bb"

-- (a + ε + b)*a
def r13' : Regex (Char) := ((Regex.plus 'a' (Regex.plus epsilon 'b')).star).mul 'a'
#eval r13'.matchEnd "aba" = r13'.gmatch "aba"

-- (aa + ε + a)*a
def r13'' : Regex (Char) := ((Regex.plus "aa" (Regex.plus epsilon 'a')).star).mul 'a'
#eval r13''.gmatch "aa" = r13''.matchEnd "aa"

-- (aa + aaa)*
def r17 : Regex (Char) := (star (plus "aa" "aaa"))
#eval r17.matchEnd "aaa" = r17.gmatch "aaa"

-- (a + c* + b)*b
def r19 : Regex Char := (mul (star (plus 'a' (plus (star 'c') 'b'))) 'b')
#eval r19.gmatch "bb" = r19.matchEnd "bb"
