import GreedyDeriv.Regex
import GreedyDeriv.Greedy

open Regex

/-- Helper function to convert strings into regexes (string as a sequence of characters) -/
def String.toRegex (s : String) : Regex Char :=
  s.toList |>.map char |>.foldr Regex.mul epsilon

/-- Implicit coercion to convert strings to regexes to make them more readable. -/
instance : Coe String (Regex Char) where
  coe := String.toRegex

/-- Implicit coercion to convert characters to regexes to make them more readable -/
instance : Coe Char (Regex Char) where
  coe := char

-- a + ab
def r : Regex (Char) := plus 'a' "ab"
#eval r.rmatch "ab".toList
#eval r.gmatch "ab".toList

-- (a + ab)*
def r2 : Regex (Char) := (plus 'a' "ab").star false
#eval r2.rmatch "aab".toList
#eval r2.gmatch "aab".toList

-- c + ab
def r3 : Regex (Char) := plus 'c' (mul 'a' 'b')
#eval r3.rmatch "ab".toList
#eval r3.gmatch "ab".toList

-- (a + aa)a
def r4 : Regex (Char) := (plus 'a' "aa").mul 'a'
#eval r4.rmatch "aaa".toList
#eval r4.gmatch "aaa".toList

-- a*a
def r5 : Regex (Char) := (star 'a' false).mul 'a'
#eval r5.rmatch "aa".toList
#eval r5.gmatch "aa".toList

-- (ε|b)*
def r6 : Regex (Char) := (epsilon.plus 'b').star false
#eval r6.rmatch "bb".toList
#eval r6.gmatch "bb".toList

-- (ε|b)(ε|b)*
def r6' : Regex (Char) := (epsilon.plus 'b').mul ((epsilon.plus 'b').star false)
#eval r6'.rmatch "bb".toList
#eval r6'.gmatch "bb".toList

-- (a|ε|b)*
def r7 : Regex (Char) := (plus 'a' (epsilon.plus 'b')).star false
#eval r7.rmatch "aaaabbb".toList
#eval r7.gmatch "aaaabbb".toList

-- (ε|a)b
def r8 : Regex (Char) := (epsilon.plus 'a').mul 'b'
#eval r8.rmatch "ab".toList
#eval r8.gmatch "ab".toList

-- ((a|ε|b)|b)
def r9 : Regex (Char) := Regex.plus ((plus 'a' epsilon).plus 'b') 'b'
#eval r9.gmatch "b".toList
#eval r9.rmatch "b".toList

-- (ε|a)*b
def r10 : Regex (Char) := ((Regex.plus epsilon 'a').star false).mul 'b'
#eval r10.gmatch "ab".toList
#eval r10.rmatch "ab".toList

-- (a|ε)*(ε|b)
def r11 : Regex (Char) := ((Regex.plus 'a' epsilon).star false).mul (Regex.plus (epsilon) 'b')
#eval r11.gmatch "ab".toList
#eval r11.rmatch "ab".toList

-- (ε|a)*(ε|b)
def r12 : Regex (Char) := ((Regex.plus epsilon 'a').star false).mul (Regex.plus (epsilon) 'b')
#eval r12.gmatch "ab".toList
#eval r12.rmatch "ab".toList

-- (a|ε|b)*b
def r13 : Regex (Char) := ((Regex.plus 'a' (Regex.plus epsilon 'b')).star false).mul 'b'
#eval r13.gmatch "bb".toList
#eval r13.rmatch "bb".toList

-- a*?a
def r14 : Regex (Char) := (star 'a' true).mul 'a'
#eval r14.rmatch "aaa".toList
#eval r14.gmatch "aaa".toList

-- a*?b
def r15 : Regex (Char) := (star 'a' true).mul 'b'
#eval r15.rmatch "aab".toList
#eval r15.gmatch "aab".toList

-- (a|ε|b)*?b
def r16 : Regex (Char) := (star (plus 'a' (plus epsilon 'b')) true).mul 'b'
#eval r16.rmatch "aabb".toList
#eval r16.gmatch "aabb".toList

def r17 : Regex (Char) := (star (plus "aa" "aaa") false)
#eval r17.rmatch "aaa".toList
#eval r17.gmatch "aaa".toList
