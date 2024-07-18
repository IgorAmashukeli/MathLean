-- ∃! notation from previous problem
def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b


axiom morgan_uni (α : Type) (P : α → Prop) : (∀ x, ¬ P x) ↔ (¬ ∃ x, P x)
axiom morgan_exi (α : Type) (P : α → Prop) : (∃ x : α, ¬ P x) ↔ (¬ ∀ x : α, P x)
axiom uni_congr (α : Type) (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∀ x, P x) ↔ (∀ x, Q x))
axiom uni_conj (α : Type) (P Q: α → Prop) : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x)
axiom eq_subst (α : Type) (P : α → Prop) : (∀ (a b : α), a = b → P a → P b)
axiom disj_idemp (p : Prop) : (p ∨ p) ↔ p
axiom disj_comm (p q : Prop) : (p ∨ q) ↔ (q ∨ p)
axiom iff_symm (p q : Prop) : (p ↔ q) → (q ↔ p)
axiom iff_trans (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r)
axiom negation_not_equiv (p : Prop) : ¬ (p ↔ ¬p)
axiom de_morgan_and (p q : Prop) : ¬ (p ∧ q) ↔ (¬ p ∨ ¬ q)
axiom contraposition (p q : Prop) : (p → q) ↔ (¬q → ¬p)
axiom conj_congr (p q r : Prop) : (p ↔ q) → ((p ∧ r) ↔ (q ∧ r))


theorem iff_trans_symm (p q r : Prop) :  (p ↔ q) → (r ↔ q) → (p ↔ r) :=
  fun (h : (p ↔ q)) => fun (g : (r ↔ q)) => iff_trans p q r h (iff_symm r q g)
