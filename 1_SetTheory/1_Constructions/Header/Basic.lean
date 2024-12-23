-- ∃! notation from previous problem
def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b


axiom morgan_uni (α : Type) (P : α → Prop) : (∀ x, ¬ P x) ↔ (¬ ∃ x, P x)
axiom morgan_exi (α : Type) (P : α → Prop) : (∃ x : α, ¬ P x) ↔ (¬ ∀ x : α, P x)
axiom uni_congr (α : Type) (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∀ x, P x) ↔ (∀ x, Q x))
axiom uni_conj (α : Type) (P Q: α → Prop) : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x)
axiom eq_subst {α : Type} (P : α → Prop) : (∀ (a b : α), a = b → P a → P b)
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



axiom Set : Type
axiom membership : Set → Set → Prop
infix:50 (priority := high) " ∈ " => membership
infix:50 (priority := high) " ∉ " => (fun (x : Set) => (fun (y : Set) => ¬ membership x y))
axiom set_intro (P : Set → Prop) (h : ∃! x, P x) : Set
axiom set_intro_prop (P : Set → Prop) (h : ∃! x, P x) : P (set_intro P h) ∧ ∀ x, P x → (x = set_intro P h)


-- 2) Creation of new ∀ x ∈ A/∃ x ∈ A/∃! x ∈ A notations
def forall_in_A (P : Set → Prop) (A : Set) : Prop := (∀ x, (x ∈ A → P x))
def exists_in_A (P : Set → Prop) (A : Set) : Prop := (∃ x, (x ∈ A ∧ P x))
def exists_uniq_in_A (P : Set → Prop) (A : Set) : Prop := (∃! x, (x ∈ A ∧ P x))
declare_syntax_cat idents
syntax ident : idents
syntax ident idents : idents
syntax "∀" idents "∈" term ";" term : term
syntax "∃" idents "∈" term ";" term : term
syntax "∃!" idents "∈" term ";" term : term
macro_rules
  | `(∀ $idnt:ident ∈ $A:term; $b:term)  => `(forall_in_A (fun $idnt:ident => $b) $A)
  | `(∀ $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(forall_in_A (fun $idnt:ident => (∀ $idnts:idents ∈ $A; $b)) $A)
  | `(∃ $idnt:ident ∈ $A:term; $b:term)  => `(exists_in_A (fun $idnt:ident => $b) $A)
  | `(∃ $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(exists_in_A (fun $idnt:ident => (∃ $idnts:idents ∈ $A; $b)) $A)
  | `(∃! $idnt:ident ∈ $A:term; $b:term)  => `(exists_uniq_in_A (fun $idnt:ident => $b) $A)
  | `(∃! $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(exists_uniq_in_A (fun $idnt:ident => (∃ $idnts:idents ∈ $A; $b)) $A)

def empty (A : Set) : Prop := ∀ b, (b ∉ A)
def non_empty (A : Set) : Prop := ∃ b, (b ∈ A)


def subset (A B : Set) : Prop := ∀ x ∈ A; x ∈ B
infix:50 (priority := high) " ⊆ " => subset

def set_equality (A B : Set) := ∀ x, (x ∈ A ↔ x ∈ B)
def functional_predicate (A : Set) (P : Set → Set → Prop) : Prop := ∀ x ∈ A; ∃! y, P x y
def is_successor (m n : Set) : Prop := ∀ x, (x ∈ n ↔ x ∈ m ∨ x = m)



axiom extensionality : ∀ A B, set_equality A B → (A = B)
axiom boolean : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ x ⊆ A)
axiom union : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)
axiom infinity : ∃ A, (∃ b, empty b ∧ b ∈ A) ∧ (∀ x ∈ A; ∀ y, is_successor x y → y ∈ A)
axiom replacement (P : Set → Set → Prop) : ∀ A, functional_predicate A P → ∃ B, ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y)
axiom regularity : ∀ A, non_empty A → ∃ B ∈ A; ∀ x ∈ B; x ∉ A

axiom Russel_paradox : ¬ ∃ A, ∀ x, (x ∈ A ↔ x ∉ x)
