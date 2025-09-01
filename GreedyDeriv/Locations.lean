
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

abbrev Span (α : Type u) := List α × List α × List α

def Loc.toSpan (l₁ l₂ : Loc α) : Span α :=
  (l₁.left, l₁.right.take (l₂.pos - l₁.pos), l₂.right)

def Span.start : Span α → Loc α
  | ⟨s, u, v⟩ => ⟨s, u ++ v⟩

def Span.end : Span α → Loc α
  | ⟨s, u, v⟩ => ⟨u.reverse ++ s, v⟩

def Span.match : Span α → List α
  | ⟨_, u, _⟩ => u

theorem toSpan_correct (l₁ l₂ : Loc α) (hw : l₁.word = l₂.word) (hl : l₁.pos ≤ l₂.pos) :
  (Loc.toSpan l₁ l₂).start = l₁ ∧ (Loc.toSpan l₁ l₂).end = l₂ := by
  rw [Loc.toSpan, Span.start, Span.end]
  rcases l₁ with ⟨u, v⟩
  simp at *
  induction u generalizing v with
  | nil =>
    subst hw
    simp
  | cons x xs ih =>
    simp at *
    rw [Nat.succ_le] at hl
    have ih := ih (x::v) hw (Nat.le_of_lt hl)
    rw [List.take_cons (Nat.sub_pos_of_lt hl), Nat.sub_sub] at ih
    simp at ih
    exact ih
