import GreedyDeriv.Regex
import GreedyDeriv.Greedy

open Regex

/-- Helper function to convert strings into regexes (string as a sequence of characters) -/
def String.toRegex (s : String) : Regex (BA Char) :=
  s.toList |>.map (Regex.pred ∘ BA.atom) |>.foldr Regex.mul epsilon

/-- Implicit coercion to convert strings to regexes to make them more readable. -/
instance : Coe String (Regex (BA Char)) where
  coe := String.toRegex

/-- Helper function to convert characters into regexes -/
def Char.toRegex (c : Char) : Regex (BA Char) := Regex.pred (BA.atom c)

/-- Implicit coercion to convert characters to regexes to make them more readable -/
instance : Coe Char (Regex (BA Char)) where
  coe := Char.toRegex

/-- Helper function to obtain a string as character class. -/
def String.characterClass (s : String) : BA Char :=
  s.toList |>.map .atom |>.foldr .or .bot

-- a + ab
def r : Regex (BA Char) := plus 'a' "ab"
#eval r.rmatch "ab".toList
#eval r.gmatch "ab".toList

-- (a + ab)*
def r2 : Regex (BA Char) := (plus 'a' "ab").star
#eval r2.rmatch "aab".toList
#eval r2.gmatch "aab".toList

-- c + ab
def r3 : Regex (BA Char) := plus 'c' "ab"
#eval r3.rmatch "ab".toList
#eval r3.gmatch "ab".toList

-- (a + aa)a
def r4 : Regex (BA Char) := (plus 'a' "aa").mul 'a'
#eval r4.rmatch "aaa".toList
#eval r4.gmatch "aaa".toList

-- a*a
def r5 : Regex (BA Char) := (star 'a').mul 'a'
#eval r5.rmatch "aa".toList
#eval r5.gmatch "aa".toList

-- (ε|b)*
def r6 : Regex (BA Char) := (epsilon.plus 'b').star
#eval r6.rmatch "bb".toList
#eval r6.gmatch "bb".toList

-- (ε|b)(ε|b)*
def r6' : Regex (BA Char) := (epsilon.plus 'b').mul ((epsilon.plus 'b').star)
#eval r6'.rmatch "bb".toList
#eval r6'.gmatch "bb".toList

-- (a|ε|b)*
def r7 : Regex (BA Char) := (plus 'a' (epsilon.plus 'b')).star
#eval r7.rmatch "aaaabbb".toList
#eval r7.gmatch "aaaabbb".toList

-- (ε|a)b
def r8 : Regex (BA Char) := (epsilon.plus 'a').mul 'b'
#eval r8.rmatch "ab".toList
#eval r8.gmatch "ab".toList

-- ((a|ε|b)|b)
def r9 : Regex (BA Char) := Regex.plus ((plus 'a' epsilon).plus 'b') 'b'
#eval r9.gmatch "b".toList
#eval r9.rmatch "b".toList

-- (ε|a)*b
def r10 : Regex (BA Char) := (Regex.plus epsilon 'a').star.mul 'b'
#eval r10.gmatch "ab".toList
#eval r10.rmatch "ab".toList

-- (a|ε)*(ε|b)
def r11 : Regex (BA Char) := (Regex.plus 'a' epsilon).star.mul (Regex.plus (epsilon) 'b')
#eval r11.gmatch "ab".toList
#eval r11.rmatch "ab".toList

-- (ε|a)*(ε|b)
def r12 : Regex (BA Char) := (Regex.plus epsilon 'a').star.mul (Regex.plus (epsilon) 'b')
#eval r12.gmatch "ab".toList
#eval r12.rmatch "ab".toList

-- (a|ε|b)*b
def r13 : Regex (BA Char) := (Regex.plus 'a' (Regex.plus epsilon 'b')).star.mul 'b'
#eval r13.gmatch "bb".toList
#eval r13.rmatch "bb".toList

-- a*?a
def r14 : Regex (BA Char) := (lazy_star 'a').mul 'a'
#eval r14.rmatch "aaa".toList
#eval r14.gmatch "aaa".toList

-- a*?b
def r15 : Regex (BA Char) := (lazy_star 'a').mul 'b'
#eval r15.rmatch "aab".toList
#eval r15.gmatch "aab".toList

-- (a|b|ab)*bc
def r16 : Regex (BA Char) := (plus (plus 'a' 'b') "ab").star.mul "bc"
def s := (List.replicate 5 ['a', 'b']).flatten ++ ['a', 'c']
#eval r16.rmatch s
#eval r16.gmatch s
