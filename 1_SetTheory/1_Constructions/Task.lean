import «Header»


-- 1) The problem of naive set theory
-- {x | P x} may not exists
-- for example {x | x ∉ x} doesn't exist
theorem Russel_paradox : ¬ ∃ A, ∀ x, (x ∈ A ↔ x ∉ x) := sorry


-- 2) Subset theorems
theorem subset_refl : ∀ A, A ⊆ A := sorry
theorem subset_trans : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C := sorry
theorem empty_subset_any : ∀ A B, empty A → A ⊆ B := sorry


-- 3) Subset and equality relation
theorem subs_subs_eq : ∀ A B, A ⊆ B ∧ B ⊆ A ↔ A = B := sorry
theorem equality_then_subset : ∀ A B, A = B → A ⊆ B := sorry


-- 4) construction of ∅ (empty set) and its properties
theorem exists_empty : (∃ x, empty x) := sorry
theorem exists_unique_empty : (∃! x, empty x) := sorry
noncomputable def empty_set := set_intro empty exists_unique_empty
notation (priority := high) "∅" => empty_set
theorem empty_set_is_empty : empty ∅ := sorry
theorem empty_set_subset_any : ∀ A, ∅ ⊆ A := sorry
theorem non_empty_uni_then_exi (P : Set → Prop) : ∀ A, (A ≠ ∅) → (∀ x ∈ A; P x) → ∃ x ∈ A; P x := sorry
theorem set_empty_iff_empty : ∀ A, (A = ∅) ↔ (∀ x, x ∉ A) := sorry
theorem set_non_empty_iff_non_empty : ∀ A, (A ≠ ∅) ↔ ∃ x, x ∈ A := sorry


-- 5) construction of 𝒫 A from A (boolean set)
theorem unique_boolean : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ⊆ A)) := sorry
noncomputable def boolean_func_sym : Set → Set :=
  fun (A : Set) => set_intro (fun (B : Set) => ∀ x, (x ∈ B ↔ x ⊆ A)) (unique_boolean A)
notation (priority := high) "𝒫" => boolean_func_sym
theorem boolean_set_is_boolean : ∀ A, (∀ x, x ∈ 𝒫 A ↔ x ⊆ A) := sorry
theorem empty_elem_boolean : ∀ A, ∅ ∈ 𝒫 A := sorry
theorem boolean_set_not_empty : ∀ A, 𝒫 A ≠ ∅ := sorry


-- 6) construction of a set, that exists by axiom of replacement and its properties
theorem unique_replacement (P : Set → Set → Prop) : ∀ A, functional_predicate A P → ∃! B, ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y) := sorry
noncomputable def replacement_set (P : Set → Set → Prop) (A : Set) (h : functional_predicate A P) : Set :=
  set_intro (fun (B) => ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y)) (unique_replacement P A h)
syntax "RepImg" "["  term ";"  term ";" term "]"  : term
macro_rules
  | `(RepImg [ $P:term ; $A:term ; $fun_rel_proof:term ])  => `(replacement_set $P $A $fun_rel_proof)
theorem replacement_set_is_replacement (p : Set → Set → Prop) (A : Set) (h : functional_predicate A P) :
  ∀ y, (y ∈ RepImg [P; A; h]) ↔ ∃ x ∈ A; P x y := sorry



-- 7) construction of {a₁, a₂} (unordered set) and its properties
theorem exists_unordered_pair : ∀ a₁ a₂, ∃ C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂) := sorry
theorem unique_unordered_pair : (∀ a₁ a₂, ∃! C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂)) := sorry
noncomputable def unordered_pair_set : (Set → Set → Set) := fun (a₁ : Set) => fun (a₂ : Set) =>
  set_intro (fun (B) => ∀ x, (x ∈ B ↔ x = a₁ ∨ x = a₂)) (unique_unordered_pair a₁ a₂)
notation (priority := high) "{" a₁ ", " a₂ "}" => unordered_pair_set a₁ a₂
theorem unordered_pair_set_is_unordered_pair : ∀ a₁ a₂ x, x ∈ {a₁, a₂} ↔ x = a₁ ∨ x = a₂ := sorry
theorem left_unordered_pair : ∀ a₁ a₂, a₁ ∈ {a₁, a₂} := sorry
theorem right_unordered_pair : ∀ a₁ a₂, a₂ ∈ {a₁, a₂} := sorry
theorem unordered_pair_is_unordered : ∀ a₁ a₂, {a₁, a₂} = {a₂, a₁} := sorry


-- 8) construction of {a} (singleton set) and its properties
noncomputable def singleton_set : (Set → Set) := fun (a) => unordered_pair_set a a
notation (priority := high) "{" a "}" => singleton_set a
theorem singleton_a_elem_is_a : ∀ a x, x ∈ {a} ↔ x = a := sorry
theorem x_in_singl_x : ∀ x, x ∈ {x} := sorry
theorem singleton_non_empty : ∀ x, non_empty {x} := sorry


-- 9) regularity properties
theorem neg_notin_refl : ∀ x, x ∉ x := sorry
theorem no_universal_set : ¬∃ A, ∀ x, x ∈ A := sorry


-- 10) ⋃ A (union set) construction and its properties
theorem unique_union : ∀ A, ∃! B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y) := sorry
noncomputable def union_set : (Set → Set) := fun (A) => set_intro (fun (B) => ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)) (unique_union A)
notation (priority := high) "⋃" => union_set
theorem union_set_is_union : (∀ A x, (x ∈ ⋃ A ↔ ∃ y ∈ A; x ∈ y)) := sorry
theorem union_empty : ⋃ ∅ = ∅ := sorry
theorem union_singleton : ∀ A, ⋃ {A} = A := sorry
theorem union_boolean : (∀ A, ⋃ (𝒫 A) = A) := sorry
theorem elem_subset_union : (∀ A, ∀ x ∈ A; x ⊆ ⋃ A) := sorry
theorem boolean_union : (∀ A, A ⊆ 𝒫 (⋃ A)) := sorry
theorem sub_bool_un_mem_bool : ∀ A B, (A ⊆ 𝒫 B → ((⋃ A) ∈ 𝒫 B)) := sorry
theorem all_ss_then_union_ss : ∀ A B, (∀ X ∈ A; X ⊆ B) → (⋃ A ⊆ B) :=sorry
theorem union_subset_monotonic : ∀ A B, A ⊆ B → ⋃ A ⊆ ⋃ B := sorry


-- 11) {x ∈ A | P x} (specification set) construction and its properties
theorem specification_simple (P : Set → Prop) :  (∀ A, (¬∃ x ∈ A; P x) → ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) := sorry
theorem specification_hard (P : Set → Prop) : (∀ A, (∃ x ∈ A; P x) → ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) := sorry
theorem specification (P : Set → Prop) : (∀ A, ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) := sorry
theorem unique_specification (P : Set → Prop) : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) := sorry
noncomputable def specification_set (P : Set → Prop) : (Set → Set) :=
  fun (A) => set_intro (fun (B) => (∀ x, x ∈ B ↔ x ∈ A ∧ P x)) (unique_specification P A)
syntax "{" ident "∈" term "|" term "}" : term
macro_rules
  | `({ $x:ident ∈ $A:term | $property:term })  => `(specification_set (fun ($x) => $property) $A)
theorem spec_is_spec (P : Set → Prop) : (∀ A x, x ∈ {x ∈ A | P x} ↔ x ∈ A ∧ P x) := sorry
theorem specification_set_subset (P : Set → Prop) : (∀ A, {x ∈ A | P x} ⊆ A) := sorry


-- 12) ⋂ A (intersection set) construction and its properties
noncomputable def intersection_set : Set → Set := fun (A) => {x ∈ ⋃ A | ∀ y ∈ A; x ∈ y}
notation (priority := high) "⋂" => intersection_set
theorem intersection_set_is_intersection : ∀ A x, x ∈ ⋂ A ↔ (x ∈ ⋃ A ∧ ∀ y ∈ A; x ∈ y) := sorry
theorem intersection_non_empty : ∀ A, (A ≠ ∅ → ∀ x, (x ∈ ⋂ A) ↔ ∀ y ∈ A; x ∈ y) := sorry
theorem intersect_subset_monotonic : ∀ A B, (A ≠ ∅) → (A ⊆ B) → (⋂ B ⊆ ⋂ A) := sorry


-- 13) Set of all singletons

noncomputable def singlbool_set (A) := {S ∈ 𝒫 (A) | ∃ x ∈ A; S = {x}}
syntax "𝒫₁" term : term
macro_rules
| `(𝒫₁ $A) => `(singlbool_set $A)

theorem singlbool_set_prop : ∀ A S, (S ∈ 𝒫₁ (A)) ↔ (∃ x ∈ A; S = {x}) := sorry
theorem in_singlbool_set : ∀ A x, ({x} ∈ 𝒫₁ (A)) ↔ (x ∈ A) := sorry
