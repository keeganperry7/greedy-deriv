import GreedyDeriv.Regex

variable {α : Type u}

inductive Greedy : Regex α → Loc α → Prop
  | one (s : List α) :
    Greedy .one ⟨[], s⟩
  | char (c : α) (s : List α) :
    Greedy (.char c) ⟨[c], s⟩
  | plus_left (r₁ r₂ : Regex α) (loc : Loc α) :
    Greedy r₁ loc →
    Greedy (r₁.plus r₂) loc
  | plus_right (r₁ r₂ : Regex α) (loc : Loc α) :
    ¬(∃ s₃ s₄, s₃ ++ s₄ = loc.word ∧ r₁.matches' s₃) →
    Greedy r₂ loc →
    Greedy (r₁.plus r₂) loc
  | mul (r₁ r₂ : Regex α) (s₁ s₂ s₃ : List α) :
    Greedy r₁ ⟨s₁.reverse, s₂ ++ s₃⟩ →
    Greedy r₂ ⟨s₂.reverse, s₃⟩ →
    Greedy (r₁.mul r₂) ⟨s₂.reverse ++ s₁.reverse, s₃⟩
  | star_nil (r : Regex α) (s : List α) :
    Greedy r.star ⟨[], s⟩
  | star (r : Regex α) (s₁ s₂ s₃ : List α) :
    Greedy r ⟨s₁.reverse, s₂ ++ s₃⟩ →
    Greedy r.star ⟨s₂.reverse, s₃⟩ →
    Greedy r.star ⟨s₂.reverse ++ s₁.reverse, s₃⟩
