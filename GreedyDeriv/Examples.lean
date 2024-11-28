import GreedyDeriv.Regex
import GreedyDeriv.Greedy

-- a + ab
def r := (Regex.char 'a').plus ((Regex.char 'a').mul (Regex.char 'b'))
#eval r.rmatch "ab".toList
#eval r.gmatch "ab".toList

-- (a + ab)*
def r2 := ((Regex.char 'a').plus ((Regex.char 'a').mul (Regex.char 'b'))).star
#eval r2.rmatch "aab".toList
#eval r2.gmatch "aab".toList

-- c + ab
def r3 := (Regex.char 'c').plus ((Regex.char 'a').mul (Regex.char 'b'))
#eval r3.rmatch "ab".toList
#eval r3.gmatch "ab".toList

-- (a + aa)a
def r4 := ((Regex.char 'a').plus ((Regex.char 'a').mul (Regex.char 'a'))).mul (Regex.char 'a')
#eval r4.rmatch "aaa".toList
#eval r4.gmatch "aaa".toList

-- a*a
def r5 := (Regex.char 'a').star.mul (Regex.char 'a')
#eval r5.rmatch "aa".toList
#eval r5.gmatch "aa".toList

-- (ε|b)*
def r6 : Regex Char := (Regex.one.plus (Regex.char 'b')).star

#eval r6.rmatch "bb".toList
#eval r6.gmatch "bb".toList

-- (ε|b)(ε|b)*
def r6' : Regex Char := (Regex.one.plus (Regex.char 'b')).mul ((Regex.one.plus (Regex.char 'b')).star)

#eval r6'.rmatch "bb".toList
#eval r6'.gmatch "bb".toList

-- (a|ε|b)*
def r7 : Regex Char := ((Regex.char 'a').plus (Regex.one.plus (Regex.char 'b'))).star
#eval r7.rmatch "aaaabbb".toList
#eval r7.gmatch "aaaabbb".toList

-- (ε|a)b
def r8 : Regex Char := (Regex.one.plus (Regex.char 'a')).mul (Regex.char 'b')
#eval r8.rmatch "ab".toList
#eval r8.gmatch "ab".toList

-- ((a|ε|b)|b)
def r9 : Regex Char := Regex.plus (((Regex.char 'a').plus (Regex.char 'a').star).plus (Regex.char 'b')) (Regex.char 'b')
#eval r9.gmatch "b".toList
