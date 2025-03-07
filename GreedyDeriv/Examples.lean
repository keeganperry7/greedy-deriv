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
#eval r.llmatch "ab".toList

-- (a + ab)*
def r2 : Regex (BA Char) := (plus 'a' "ab").star false
#eval r2.rmatch "aab".toList
#eval r2.gmatch "aab".toList
#eval r2.llmatch "aab".toList

-- c + ab
def r3 : Regex (BA Char) := plus 'c' (mul 'a' 'b')
#eval r3.rmatch "ab".toList
#eval r3.gmatch "ab".toList
#eval r3.llmatch "ab".toList

-- (a + aa)a
def r4 : Regex (BA Char) := (plus 'a' "aa").mul 'a'
#eval r4.rmatch "aaa".toList
#eval r4.gmatch "aaa".toList
#eval r4.llmatch "aaa".toList

-- a*a
def r5 : Regex (BA Char) := (star 'a' false).mul 'a'
#eval r5.rmatch "aa".toList
#eval r5.gmatch "aa".toList
#eval r5.llmatch "aa".toList

-- (ε|b)*
def r6 : Regex (BA Char) := (epsilon.plus 'b').star false
#eval r6.rmatch "bb".toList
#eval r6.gmatch "bb".toList
#eval r6.llmatch "bb".toList

-- (ε|b)(ε|b)*
def r6' : Regex (BA Char) := (epsilon.plus 'b').mul ((epsilon.plus 'b').star false)
#eval r6'.rmatch "bb".toList
#eval r6'.gmatch "bb".toList

-- (a|ε|b)*
def r7 : Regex (BA Char) := (plus 'a' (epsilon.plus 'b')).star false
#eval r7.rmatch "aaaabbb".toList
#eval r7.gmatch "aaaabbb".toList
#eval r7.llmatch "aaaabbb".toList

-- (ε|a)b
def r8 : Regex (BA Char) := (epsilon.plus 'a').mul 'b'
#eval r8.rmatch "ab".toList
#eval r8.gmatch "ab".toList
#eval r8.llmatch "ab".toList

-- ((a|ε|b)|b)
def r9 : Regex (BA Char) := Regex.plus ((plus 'a' epsilon).plus 'b') 'b'
#eval r9.gmatch "b".toList
#eval r9.rmatch "b".toList
#eval r9.llmatch "b".toList

-- (ε|a)*b
def r10 : Regex (BA Char) := ((Regex.plus epsilon 'a').star false).mul 'b'
#eval r10.gmatch "ab".toList
#eval r10.rmatch "ab".toList
#eval r10.llmatch "ab".toList

-- (a|ε)*(ε|b)
def r11 : Regex (BA Char) := ((Regex.plus 'a' epsilon).star false).mul (Regex.plus (epsilon) 'b')
#eval r11.gmatch "ab".toList
#eval r11.rmatch "ab".toList
#eval r11.llmatch "ab".toList

-- (ε|a)*(ε|b)
def r12 : Regex (BA Char) := ((Regex.plus epsilon 'a').star false).mul (Regex.plus (epsilon) 'b')
#eval r12.gmatch "ab".toList
#eval r12.rmatch "ab".toList
#eval r12.llmatch "ab".toList

-- (a|ε|b)*b
def r13 : Regex (BA Char) := ((Regex.plus 'a' (Regex.plus epsilon 'b')).star false).mul 'b'
#eval r13.gmatch "bb".toList
#eval r13.rmatch "bb".toList
#eval r13.llmatch "bb".toList

-- a*?a
def r14 : Regex (BA Char) := (star 'a' true).mul 'a'
#eval r14.rmatch "aaa".toList
#eval r14.gmatch "aaa".toList
#eval r14.llmatch "aaa".toList

-- a*?b
def r15 : Regex (BA Char) := (star 'a' true).mul 'b'
#eval r15.rmatch "aab".toList
#eval r15.gmatch "aab".toList
#eval r15.llmatch "aab".toList

-- a + aa
def r16 : Regex (BA Char) := (plus 'a' "aa").star false
#eval r16.rmatch "aa".toList
#eval r16.gmatch "aa".toList
#eval r16.llmatch "aa".toList

-- (a + aa)b
def r17 : Regex (BA Char) := (plus 'a' "ab").mul 'b'
#eval r17.rmatch "abb".toList
#eval r17.gmatch "abb".toList
#eval r17.llmatch "abb".toList

-- (a + aa)aa
def r18 : Regex (BA Char) := (plus 'a' "aa").mul "aa"
#eval r18.rmatch "aaa".toList
#eval r18.gmatch "aaa".toList
#eval r18.llmatch "aaa".toList

-- (ε + b)*
def r19 : Regex (BA Char) := (plus epsilon 'b').star false
#eval r19.gmatch "bbb".toList
#eval r19.rmatch "bbb".toList
