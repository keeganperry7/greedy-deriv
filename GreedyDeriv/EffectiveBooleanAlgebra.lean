import Mathlib.Order.BooleanAlgebra

class Denotation (α : Type u) (σ : outParam (Type v)) where
  denote : α → σ → Bool
export Denotation (denote)

class EffectiveBooleanAlgebra (α : Type u) (σ : outParam (Type v))
    extends Denotation α σ, Bot α, Top α, Min α, Max α, HasCompl α where
  denote_bot : denote ⊥ c = false
  denote_top : denote ⊤ c = true
  denote_compl : denote aᶜ c = !denote a c
  denote_min : denote (a ⊓ b) c = (denote a c && denote b c)
  denote_max : denote (a ⊔ b) c = (denote a c || denote b c)

open EffectiveBooleanAlgebra in
attribute [simp] denote_bot denote_top denote_min denote_max denote_compl

inductive BA (α : Type u)
  | atom (a : α)
  | top | bot
  | and (a b : BA α)
  | or (a b : BA α)
  | not (a : BA α)
  deriving Repr, DecidableEq
open BA

protected def BA.denote [Denotation α σ] (c : σ) : BA α → Bool
  | atom a => denote a c
  | not a => !(a.denote c)
  | and a b => a.denote c && b.denote c
  | or a b => a.denote c || b.denote c
  | bot => false
  | top => true

instance [Denotation α σ] : EffectiveBooleanAlgebra (BA α) σ where
  bot := BA.bot
  top := BA.top
  min := BA.and
  max := BA.or
  compl := BA.not
  denote_bot := rfl
  denote_top := rfl
  denote_min := rfl
  denote_max := rfl
  denote_compl := rfl
  denote a c := a.denote c

instance : Denotation Char Char where
  denote a b := a == b
