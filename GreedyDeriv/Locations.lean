
abbrev Loc (α : Type u) := List α × List α

@[simp]
def Loc.left (loc : Loc α) : List α := loc.1

@[simp]
def Loc.pos (loc : Loc α) : Nat := loc.1.length

@[simp]
def Loc.right (loc : Loc α) : List α := loc.2

@[simp]
def Loc.word (loc : Loc α) : List α := loc.left.reverse ++ loc.right
