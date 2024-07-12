import «Header»

-- 1) Creation of a new type: Set, it has only one predicate: membership
-- and two properties: set_intro and set_intro_prop
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
  | `(∃ $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(exists_in_A (fun $idnt:ident => (∀ $idnts:idents ∈ $A; $b)) $A)
  | `(∃! $idnt:ident ∈ $A:term; $b:term)  => `(exists_uniq_in_A (fun $idnt:ident => $b) $A)
  | `(∃! $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(exists_uniq_in_A (fun $idnt:ident => (∀ $idnts:idents ∈ $A; $b)) $A)


-- 3) The problem of naive set theory
-- {x | P x} may not exists
-- for example {x | x ∉ x} doesn't exist
theorem Russel_paradox : ¬ ∃ A, ∀ x, (x ∈ A ↔ x ∉ x) := sorry


-- 4) Empty and non-empty definitions
def empty (A : Set) : Prop := ∀ b, (b ∉ A)
def non_empty (A : Set) : Prop := ∃ b, (b ∈ A)


-- 5) Subset notation
def subset (A B : Set) : Prop := ∀ x ∈ A; x ∈ B
infix:50 (priority := high) " ⊆ " => subset


-- 6) Subset theorems
theorem subset_refl : ∀ A, A ⊆ A := sorry
theorem subset_trans : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C := sorry
theorem empty_subset_any : ∀ A B, empty A → A ⊆ B := sorry

-- 7) Set equality definition
def set_equality (A B : Set) := ∀ x, (x ∈ A ↔ x ∈ B)

-- 8) Some useful definitions before listing ZF axioms
def functional_predicate (A : Set) (P : Set → Set → Prop) : Prop := ∀ x ∈ A; ∃! y, P x y
def is_successor (m n : Set) : Prop := ∀ x, (x ∈ n ↔ x ∈ m ∨ x = m)



-- 9) Full list of 6 Zermelo Fraenkel (ZF) axioms
-- Later we will add 7th axiom: axiom of choice
-- The system with this axioms will be called ZFC

-- set equality implies logical equality of types
axiom extensionality : ∀ A B, set_equality A B → (A = B)
-- there exists a set of all subsets of a set
axiom boolean : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ x ⊆ A)
-- there exists a union of a set
axiom union : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)
-- there exists an infinite set with a special structure
axiom infinity : ∃ A, (∃ b, empty b ∧ b ∈ A) ∧ (∀ x ∈ A; ∀ y, is_successor x y → y ∈ A)
-- if P is a functional 2-variable predicate for set A, then there exists an image of this predicate
axiom replacement (P : Set → Set → Prop) : ∀ A, functional_predicate A P → ∃ B, ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y)
-- in all non-empty set there exists a set, which elements can't be "on the level" of elements of A
axiom regularity : ∀ A, non_empty A → ∃ B ∈ A; ∀ x ∈ B; x ∉ A



-- 10) Subset and equality relation
theorem subs_subs_eq : ∀ A B, A ⊆ B ∧ B ⊆ A ↔ A = B := sorry
theorem equality_then_subset : ∀ A B, A = B → A ⊆ B := sorry


-- 11) construction of ∅ (empty set) and its properties
theorem exists_empty : (∃ x, empty x) := sorry
theorem exists_unique_empty : (∃! x, empty x) := sorry
noncomputable def empty_set := set_intro empty exists_unique_empty
notation (priority := high) "∅" => empty_set
theorem empty_set_is_empty : empty ∅ := sorry
theorem empty_set_subset_any : ∀ A, ∅ ⊆ A := sorry
theorem non_empty_uni_then_exi (P : Set → Prop) : ∀ A, (A ≠ ∅) → (∀ x ∈ A; P x) → ∃ x ∈ A; P x := sorry


-- 12) construction of 𝒫 A from A (boolean set)
theorem unique_boolean : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ⊆ A)) := sorry
noncomputable def boolean_func_sym : Set → Set :=
  fun (A : Set) => set_intro (fun (B : Set) => ∀ x, (x ∈ B ↔ x ⊆ A)) (unique_boolean A)
notation (priority := high) "𝒫" => boolean_func_sym
theorem boolean_set_is_boolean : ∀ A, (∀ x, x ∈ 𝒫 A ↔ x ⊆ A) := sorry
theorem empty_elem_boolean : ∀ A, ∅ ∈ 𝒫 A := sorry
theorem boolean_set_not_empty : ∀ A, 𝒫 A ≠ ∅ := sorry


-- 13) construction of a set, that exists by axiom of replacement and its properties
theorem unique_replacement (P : Set → Set → Prop) : ∀ A, functional_predicate A P → ∃! B, ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y) := sorry
noncomputable def replacement_set (P : Set → Set → Prop) (A : Set) (h : functional_predicate A P) : Set :=
  set_intro (fun (B) => ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y)) (unique_replacement P A h)
syntax "RepImg" "["  term ";"  term ";" term "]"  : term
macro_rules
  | `(RepImg [ $P:term ; $A:term ; $fun_rel_proof:term ])  => `(replacement_set $P $A $fun_rel_proof)
theorem replacement_set_is_replacement (p : Set → Set → Prop) (A : Set) (h : functional_predicate A P) :
  ∀ y, (y ∈ RepImg [P; A; h]) ↔ ∃ x ∈ A; P x y := sorry



-- 14) construction of {a₁, a₂} (unordered set) and its properties
theorem exists_unordered_pair : ∀ a₁ a₂, ∃ C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂) := sorry
theorem unique_unordered_pair : (∀ a₁ a₂, ∃! C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂)) := sorry
noncomputable def unordered_pair_set : (Set → Set → Set) := fun (a₁ : Set) => fun (a₂ : Set) =>
  set_intro (fun (B) => ∀ x, (x ∈ B ↔ x = a₁ ∨ x = a₂)) (unique_unordered_pair a₁ a₂)
notation (priority := high) "{" a₁ ", " a₂ "}" => unordered_pair_set a₁ a₂
theorem unordered_pair_set_is_unordered_pair : ∀ a₁ a₂ x, x ∈ {a₁, a₂} ↔ x = a₁ ∨ x = a₂ := sorry
theorem left_unordered_pair : ∀ a₁ a₂, a₁ ∈ {a₁, a₂} := sorry
theorem right_unordered_pair : ∀ a₁ a₂, a₂ ∈ {a₁, a₂} := sorry
theorem unordered_pair_is_unordered : ∀ a₁ a₂, {a₁, a₂} = {a₂, a₁} := sorry


-- 15) construction of {a} (singleton set) and its properties
noncomputable def singleton_set : (Set → Set) := fun (a) => unordered_pair_set a a
notation (priority := high) "{" a "}" => singleton_set a
theorem singleton_a_elem_is_a : ∀ a x, x ∈ {a} ↔ x = a := sorry
theorem x_in_singl_x : ∀ x, x ∈ {x} := sorry
theorem singleton_non_empty : ∀ x, non_empty {x} := sorry


-- 16) regularity properties
theorem neg_notin_refl : ∀ x, x ∉ x := sorry
theorem no_universal_set : ¬∃ A, ∀ x, x ∈ A := sorry


-- 17) ⋃ A (union set) construction and its properties
theorem unique_union : ∀ A, ∃! B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y) := sorry
noncomputable def union_set : (Set → Set) := fun (A) => set_intro (fun (B) => ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)) (unique_union A)
notation (priority := high) "⋃" => union_set
theorem union_set_is_union : (∀ A x, (x ∈ ⋃ A ↔ ∃ y ∈ A; x ∈ y)) := sorry
theorem union_empty : ⋃ ∅ = ∅ := sorry
theorem union_singleton : ∀ A, ⋃ {A} = A := sorry
theorem union_boolean : (∀ A, ⋃ (𝒫 A) = A) := sorry
theorem elem_subset_union : (∀ A, ∀ x ∈ A; x ⊆ ⋃ A) := sorry
theorem boolean_union : (∀ A, A ⊆ 𝒫 (⋃ A)) := sorry
theorem all_ss_then_union_ss : ∀ A B, (∀ X ∈ A; X ⊆ B) → (⋃ A ⊆ B) :=sorry
theorem union_subset_monotonic : ∀ A B, A ⊆ B → ⋃ A ⊆ ⋃ B := sorry


-- 18) {x ∈ A | P x} (specification set) construction and its properties
theorem specification_simple (P : Set → Prop) :  (∀ A, (¬∃ x ∈ A; P x) → ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) := sorry
theorem specification_hard (P : Set → Prop) : (∀ A, (∃ x ∈ A; P x) → ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) := sorry
theorem specification (P : Set → Prop) : (∀ A, ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) := sorry
theorem unique_specification (P : Set → Prop) : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) := sorry
noncomputable def specification_set (P : Set → Prop) : (Set → Set) :=
  fun (A) => set_intro (fun (B) => (∀ x, x ∈ B ↔ x ∈ A ∧ P x)) (unique_specification P A)
syntax "{" ident "∈" term "|" term "}" : term
macro_rules
  | `({ $x:ident ∈ $A:term | $property:term })  => `(specification_set (fun ($x) => $property) $A)
theorem specification_set_is_specification (P : Set → Prop) : (∀ A x, x ∈ {x ∈ A | P x} ↔ x ∈ A ∧ P x) := sorry
theorem specification_set_subset (P : Set → Prop) : (∀ A, {x ∈ A | P x} ⊆ A) := sorry


-- 19) ⋂ A (intersection set) construction and its properties
noncomputable def intersection_set : Set → Set := fun (A) => {x ∈ ⋃ A | ∀ y ∈ A; x ∈ y}
notation (priority := high) "⋂" => intersection_set
theorem intersection_set_is_intersection : ∀ A x, x ∈ ⋂ A ↔ (x ∈ ⋃ A ∧ ∀ y ∈ A; x ∈ y) := sorry
theorem intersection_non_empty : ∀ A, (A ≠ ∅ → ∀ x, (x ∈ ⋂ A) ↔ ∀ y ∈ A; x ∈ y) := sorry
theorem intersect_subset_monotonic : ∀ A B, (A ≠ ∅) → (A ⊆ B) → (⋂ B ⊆ ⋂ A) := sorry
