import GreedyDeriv.Regex

variable {α : Type u}

inductive Greedy : Regex α → Loc α → Prop
  | one (s : List α) :
    Greedy .one ⟨[], s⟩
  | char (c : α) (s : List α) :
    Greedy (.char c) ⟨[c], s⟩
  | plus_left (r₁ r₂ : Regex α) (s₁ s₂ : List α) :
    Greedy r₁ ⟨s₁.reverse, s₂⟩ →
    Greedy (r₁.plus r₂) ⟨s₁.reverse, s₂⟩
  | plus_right (r₁ r₂ : Regex α) (s₁ s₂ : List α) :
    ¬(∃ s₃ s₄, s₃ ++ s₄ = s₁ ++ s₄ ∧ r₁.matches' s₃) →
    Greedy r₂ ⟨s₁.reverse, s₂⟩ →
    Greedy (r₁.plus r₂) ⟨s₁.reverse, s₂⟩
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
