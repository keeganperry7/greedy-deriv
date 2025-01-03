
abbrev Loc (α : Type u) := List α × List α

@[simp]
def Loc.left (loc : Loc α) : List α := loc.1

@[simp]
def Loc.pos (loc : Loc α) : Nat := loc.1.length

@[simp]
def Loc.right (loc : Loc α) : List α := loc.2

@[simp]
def Loc.word (loc : Loc α) : List α := loc.left.reverse ++ loc.right

@[simp]
def Loc.reverse (loc : Loc α) : Loc α :=
  match loc with
  | ⟨u, v⟩ => ⟨v, u⟩

abbrev Span (σ : Type u) := List σ × List σ × List σ

@[simp]
def Span.left (s : Span σ) : List σ := s.1

@[simp]
def Span.match (s : Span σ) : List σ := s.2.1

@[simp]
def Span.right (s : Span σ) : List σ := s.2.1

@[simp]
def Span.reverse (s : Span σ) : Span σ :=
  match s with
  | ⟨s, u, v⟩ => ⟨v, u.reverse, s⟩

def merge_start_end (start_loc end_loc : Loc σ) : Span σ :=
  match start_loc, end_loc with
  | ⟨s, _⟩, ⟨u, v⟩ => ⟨s, u.reverse.drop s.length, v⟩
