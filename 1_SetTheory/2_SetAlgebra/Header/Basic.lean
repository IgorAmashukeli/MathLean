def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b
axiom Set : Type
axiom membership : Set → Set → Prop
infix:50 (priority := high) " ∈ " => membership
infix:50 (priority := high) " ∉ " => (fun (x : Set) => (fun (y : Set) => ¬ membership x y))
axiom set_intro (P : Set → Prop) (h : ∃! x, P x) : Set
axiom set_to_prop (P : Set → Prop) (h : ∃! x, P x) : P (set_intro P h) ∧ ∀ x, x ≠ set_intro P h → ¬P x
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
def is_successor (m n : Set) : Prop := ∀ x, (x ∈ n ↔ x ∈ m ∨ x = m)
infix:50 (priority := high) " ⊆ " => subset
axiom exists_unique_empty : (∃! x, empty x)
axiom unique_unordered_pair : (∀ a₁ a₂, ∃! C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂))
axiom unique_union : ∀ A, ∃! B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)
axiom unique_specification (P : Set → Prop) : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x))
noncomputable def empty_set := set_intro empty exists_unique_empty
noncomputable def unordered_pair_set : (Set → Set → Set) := fun (a₁ : Set) => fun (a₂ : Set) =>
  set_intro (fun (B) => ∀ x, (x ∈ B ↔ x = a₁ ∨ x = a₂)) (unique_unordered_pair a₁ a₂)
noncomputable def singleton_set : (Set → Set) := fun (a) => unordered_pair_set a a
noncomputable def union_set : (Set → Set) := fun (A) => set_intro (fun (B) => ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)) (unique_union A)
noncomputable def specification_set (P : Set → Prop) : (Set → Set) :=
  fun (A) => set_intro (fun (B) => (∀ x, x ∈ B ↔ x ∈ A ∧ P x)) (unique_specification P A)
notation (priority := high) "∅" => empty_set
notation (priority := high) "{" a₁ ", " a₂ "}" => unordered_pair_set a₁ a₂
notation (priority := high) "{" a "}" => singleton_set a
notation (priority := high) "⋃" => union_set
syntax "{" ident "∈" term "|" term "}" : term
macro_rules
  | `({ $x:ident ∈ $A:term | $property:term })  => `(specification_set (fun ($x) => $property) $A)
def is_collective (P : Set → Prop) := ∃ A, ∀ x, (P x) → x ∈ A
def is_collective_A (P : Set → Prop) (A : Set) := ∀ x, (P x) → x ∈ A
def is_comprehense (P : Set → Prop) (X : Set) := (is_collective P → ∀ x, (x ∈ X ↔ P x)) ∨ (is_collective P → X = ∅)
axiom spec_unique (P : Set → Prop) : ∃! X, is_comprehense P X
noncomputable def collect_compreh_set (P : Set → Prop) := set_intro (fun (X) => is_comprehense P X) (spec_unique P)
syntax "{" ident "|" term "}" : term
macro_rules
  | `({ $x:ident | $property:term })  => `(collect_compreh_set (fun ($x) => $property))
axiom compr_is_compr (P : Set → Prop) : is_collective P → (∀ x, (x ∈ {x | P x} ↔ P x))
axiom compr_subs (P : Set → Prop) (A : Set) : is_collective_A P A → ({x | P x} ⊆ A)


-- you can clean this axioms add some your own previous theorems as axioms here:


-- current solution axioms

axiom disj_congr (p q r : Prop) : (p ↔ q) → (p ∨ r ↔ q ∨ r)
axiom syllogism (p q r : Prop) : (p → q) → (q → r) → (p → r)
axiom eq_subst (P : Set → Prop) : (∀ (a b : Set), a = b → P a → P b)
axiom eq_symm (x y : Set) : (x = y) → (y = x)
axiom iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r)
axiom iff_symm (p q : Prop) : (p ↔ q) → (q ↔ p)
axiom conj_indempodent (p : Prop) : p ∧ p ↔ p
axiom disj_indempodent (p : Prop) : p ∨ p ↔ p
axiom conj_disj_absorbtion (p q : Prop) : (p ∧ (p ∨ q) ↔ p)
axiom disj_conj_absorbtion (p q : Prop) : (p ∨ (p ∧ q) ↔ p)
axiom conj_comm (p q : Prop) : p ∧ q ↔ q ∧ p
axiom disj_comm (p q : Prop) : p ∨ q ↔ q ∨ p
axiom conj_assoc (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
axiom disj_assoc (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
axiom conj_congr_right (p q r : Prop) : (p ↔ q) → ((p ∧ r) ↔ (q ∧ r))
axiom conj_congr_left (p q r : Prop) : (p ↔ q) → ((r ∧ p) ↔ (r ∧ q))
axiom disj_congr_right (p q r : Prop) : (p ↔ q) → ((p ∨ r) ↔ (q ∨ r))
axiom disj_congr_left (p q r : Prop) : (p ↔ q) → ((r ∨ p) ↔ (r ∨ q))
axiom conj_disj_distrib (p q r : Prop) : (p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r))
axiom disj_conj_distrib (p q r : Prop) : (p ∨ (q ∧ r)) ↔ ((p ∨ q) ∧ (p ∨ r))
axiom neg_congr (p q: Prop) : (p ↔ q) → (¬ p ↔ ¬ q)
axiom de_morgan_conj (p q : Prop) : ¬(p ∧ q) ↔ (¬p ∨ ¬ q)
axiom de_morgan_disj (p q : Prop) : ¬(p ∨ q) ↔ (¬p ∧ ¬ q)
axiom double_neg (p : Prop) : ¬¬ p ↔ p
axiom no_contradiction (p : Prop) : ¬ (p ∧ ¬p)
axiom False_or_p (p : Prop) : False ∨ p ↔ p
axiom iff_congr_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x ↔ P y))
axiom iff_subst_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x → P y))
axiom empty_set_is_empty : empty ∅
axiom empty_set_is_subset_any : ∀ A, ∅ ⊆ A
axiom unordered_pair_set_is_unordered_pair : ∀ a₁ a₂ x, x ∈ {a₁, a₂} ↔ x = a₁ ∨ x = a₂
axiom unordered_pair_is_unordered : ∀ a₁ a₂, {a₁, a₂} = {a₂, a₁}
axiom left_unordered_pair : ∀ a₁ a₂, a₁ ∈ {a₁, a₂}
axiom right_unordered_pair : ∀ a₁ a₂, a₂ ∈ {a₁, a₂}
axiom union_set_is_union : (∀ A x, (x ∈ ⋃ A ↔ ∃ y ∈ A; x ∈ y))
axiom spec_is_spec (P : Set → Prop) : (∀ A x, x ∈ {x ∈ A | P x} ↔ x ∈ A ∧ P x)
axiom specification_set_subset (P : Set → Prop) : (∀ A, {x ∈ A | P x} ⊆ A)
axiom subset_trans : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C
axiom subset_then_equality : ∀ A B, A ⊆ B ∧ B ⊆ A → A = B
def set_equality (A B : Set) := ∀ x, (x ∈ A ↔ x ∈ B)
axiom extensionality : ∀ A B, set_equality A B → (A = B)
axiom subset_refl : ∀ A, A ⊆ A

noncomputable def intersection_set : Set → Set := fun (A) => {x ∈ ⋃ A | ∀ y ∈ A; x ∈ y}
notation (priority := high) "⋂" => intersection_set
theorem intersection_set_is_intersection : ∀ A x, x ∈ ⋂ A ↔ (x ∈ ⋃ A ∧ ∀ y ∈ A; x ∈ y) := sorry
theorem intersection_non_empty : ∀ A, (A ≠ ∅ → ∀ x, (x ∈ ⋂ A) ↔ ∀ y ∈ A; x ∈ y) := sorry
theorem intersect_subset_monotonic : ∀ A B, (A ≠ ∅) → (A ⊆ B) → (⋂ B ⊆ ⋂ A) := sorry
axiom set_non_empty_iff_non_empty : ∀ A, (A ≠ ∅) ↔ ∃ x, x ∈ A
