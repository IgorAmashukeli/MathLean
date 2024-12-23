-- ∃! notation from previous problem
def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b
axiom negation_not_equiv (p : Prop) : ¬(p ↔ ¬p)
