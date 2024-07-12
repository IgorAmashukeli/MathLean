def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b
@[app_unexpander exists_unique] def unexpandexists_unique: Lean.PrettyPrinter.Unexpander
| `($(_) fun $x:ident ↦ ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
| `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
| `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! ($x:ident : $t), $b)
| _                                               => throw ()


axiom Set : Type
axiom membership : Set → Set → Prop
infix:50 (priority := high) " ∈ " => membership
infix:50 (priority := high) " ∉ " => (fun (x : Set) => (fun (y : Set) => ¬ membership x y))


-- we proved before
axiom eq_subst (P : Set → Prop) : (∀ (a b : Set), a = b → P a → P b)
axiom eq_symm (x y : Set) : (x = y) → (y = x)
axiom iff_congr_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x ↔ P y))
axiom iff_subst_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x → P y))


axiom set_to_prop (P : Set → Prop) (h : ∃! x, P x) : Set
axiom prop_to_set (P : Set → Prop) (h : ∃! x, P x) : P (set_to_prop P h) ∧ ∀ x, x ≠ set_to_prop P h → ¬P x


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


def empty (A : Set) : Prop := ∀ b, (b ∉ A)
def non_empty (A : Set) : Prop := ∃ b, (b ∈ A)
def subset (A B : Set) : Prop := ∀ x ∈ A; x ∈ B
def is_successor (m n : Set) : Prop := ∀ x, (x ∈ n ↔ x ∈ m ∨ x = m)
infix:50 (priority := high) " ⊆ " => subset

axiom subset_refl : ∀ A, A ⊆ A

axiom subset_trans_curry : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C
axiom subset_trans_export : ∀ A B C, A ⊆ B ∧ B ⊆ C → A ⊆ C
axiom empty_subset_any : ∀ A B, empty A → A ⊆ B

axiom morgan_exi (α : Type) (P : α → Prop) : (∃ x : α, ¬ P x) ↔ (¬ ∀ x : α, P x)
axiom morgan_uni (α : Type) (P : α → Prop) : (∀ x : α, ¬ P x) ↔ (¬ ∃ x : α, P x)


def set_equality (A B : Set) := ∀ x, (x ∈ A ↔ x ∈ B)
axiom boolean : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ x ⊆ A)
axiom extensionality : ∀ A B, set_equality A B → (A = B)
axiom exists_unique_empty : (∃! x, empty x)
axiom unique_unordered_pair : (∀ a₁ a₂, ∃! C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂))
axiom unique_union : ∀ A, ∃! B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)
axiom unique_specification (P : Set → Prop) : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x))
axiom unique_boolean : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ⊆ A))



noncomputable def empty_set := set_to_prop empty exists_unique_empty
noncomputable def unordered_pair_set : (Set → Set → Set) := fun (a₁ : Set) => fun (a₂ : Set) =>
  set_to_prop (fun (B) => ∀ x, (x ∈ B ↔ x = a₁ ∨ x = a₂)) (unique_unordered_pair a₁ a₂)
noncomputable def singleton_set : (Set → Set) := fun (a) => unordered_pair_set a a
noncomputable def union_set : (Set → Set) := fun (A) => set_to_prop (fun (B) => ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)) (unique_union A)
noncomputable def specification_set (P : Set → Prop) : (Set → Set) :=
  fun (A) => set_to_prop (fun (B) => (∀ x, x ∈ B ↔ x ∈ A ∧ P x)) (unique_specification P A)



notation (priority := high) "∅" => empty_set
notation (priority := high) "{" a₁ ", " a₂ "}" => unordered_pair_set a₁ a₂
notation (priority := high) "{" a "}" => singleton_set a
notation (priority := high) "⋃" => union_set
syntax "{" ident "∈" term "|" term "}" : term
macro_rules
  | `({ $x:ident ∈ $A:term | $property:term })  => `(specification_set (fun ($x) => $property) $A)

noncomputable def union_2sets (A B : Set) := ⋃ {A, B}
infix:60 (priority:=high) " ∪ " => union_2sets

noncomputable def intersect_2sets (A B : Set) := {x ∈ A | x ∈ B}
infix:60 (priority:=high) " ∩ " => intersect_2sets

noncomputable def difference (A B : Set) := {x ∈ A | x ∉ B}
infix:60 (priority:=high) " \\ " => difference

noncomputable def symmetric_difference (A B : Set) := (A \ B) ∪ (B \ A)
infix:60 (priority:=high) " △ " => symmetric_difference

noncomputable def intersection_set : Set → Set := fun (A) => {x ∈ ⋃ A | ∀ y ∈ A; x ∈ y}
notation (priority := high) "⋂" => intersection_set


declare_syntax_cat set_comprehension
syntax term "; " set_comprehension : set_comprehension
syntax term : set_comprehension
syntax "{" set_comprehension "}" : term

macro_rules
| `({$term1:term}) => `(singleton_set $term1:term)
| `({$term1:term; $term2:term}) => `(unordered_pair_set $term1:term $term2:term)
| `({$elem:term; $rest:set_comprehension}) => `({$rest:set_comprehension} ∪ {$elem:term})


-- was proved in the previous problem
axiom empty_set_is_empty : empty ∅
axiom empty_set_is_subset_any : ∀ A, ∅ ⊆ A
axiom subs_subs_eq : ∀ A B, A ⊆ B ∧ B ⊆ A ↔ A = B
axiom elem_in_singl : ∀ x, x ∈ {x}
axiom in_singl_elem : ∀ a x, x ∈ {a} → x = a
axiom unordered_pair_set_is_unordered_pair : ∀ a₁ a₂ x, x ∈ {a₁, a₂} ↔ x = a₁ ∨ x = a₂
axiom unordered_pair_is_unordered : ∀ a₁ a₂, {a₁, a₂} = {a₂, a₁}
axiom union_set_is_union : (∀ A x, (x ∈ ⋃ A ↔ ∃ y ∈ A; x ∈ y))
axiom union_sing : ∀ A, ⋃ {A} = A
axiom intersection_set_is_intersection : ∀ A x, x ∈ ⋂ A ↔ (x ∈ ⋃ A ∧ ∀ y ∈ A; x ∈ y)
axiom intersection_non_empty : ∀ A, (A ≠ ∅ → ∀ x, (x ∈ ⋂ A) ↔ ∀ y ∈ A; x ∈ y)
axiom specification_set_is_specification (P : Set → Prop) : (∀ A x, x ∈ {x ∈ A | P x} ↔ x ∈ A ∧ P x)
axiom specification_set_subset (P : Set → Prop) : (∀ A, {x ∈ A | P x} ⊆ A)
axiom subset_then_equality : ∀ A B, A ⊆ B ∧ B ⊆ A → A = B
axiom union2_sets_prop : (∀ A B x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B)
axiom union2_sets_subset_prop : (∀ A B, A ⊆ A ∪ B ∧ B ⊆ A ∪ B)
axiom intersect_2sets_prop : (∀ A B x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B)
axiom intersect_2_sets_idemp : (∀ A, A ∩ A = A)
axiom intersect_2sets_subset_prop : ∀ A B, (A ∩ B ⊆ A) ∧ (A ∩ B ⊆ B)
axiom comp_2sets_subset_prop : ∀ A B, A \ B ⊆ A
axiom difference_prop : (∀ A B x, x ∈ A \ B ↔ x ∈ A ∧ x ∉ B)
axiom left_unordered_pair : ∀ a₁ a₂, a₁ ∈ {a₁, a₂}
axiom right_unordered_pair : ∀ a₁ a₂, a₂ ∈ {a₁, a₂}
axiom elem_subset_union : (∀ A, ∀ x ∈ A; x ⊆ ⋃ A)
axiom union_subset_monotonic : ∀ A B, A ⊆ B → ⋃ A ⊆ ⋃ B
axiom all_ss_then_union_ss : ∀ A B, (∀ X ∈ A; X ⊆ B) → (⋃ A ⊆ B)
axiom equality_then_subset : ∀ A B, A = B → A ⊆ B
axiom difference_subset_prop : (∀ A B, A \ B ⊆ A)


noncomputable def boolean_func_sym : Set → Set :=
  fun (A : Set) => set_to_prop (fun (B : Set) => ∀ x, (x ∈ B ↔ x ⊆ A)) (unique_boolean A)


notation (priority := high) "𝒫" => boolean_func_sym

theorem boolean_set_is_boolean : ∀ A, (∀ x, x ∈ 𝒫 A ↔ x ⊆ A) :=
  fun (A : Set) => And.left (prop_to_set (fun (B : Set) => ∀ x, (x ∈ B ↔ x ⊆ A)) (unique_boolean A))

noncomputable def ordered_pair_set (a b : Set) := {{a}, {a, b}}
notation (priority := high) "(" a₁ ", " a₂ ")" => ordered_pair_set a₁ a₂

axiom union_boolean : (∀ A, ⋃ (𝒫 A) = A)

noncomputable def fst_coor (A : Set) : Set := ⋃ (⋂ A)
noncomputable def snd_coor (A : Set) : Set := ⋃ ({x ∈ ⋃ A | ⋃ A ≠ ⋂ A → x ∉ ⋂ A})
axiom ordered_pair_set_prop : ∀ a b c d, (a, b) = (c, d) ↔ (a = c ∧ b = d)
axiom coordinates_fst_corr : ∀ a b, fst_coor (a, b) = a
axiom coordinates_snd_corr : ∀ a b, snd_coor (a, b) = b


noncomputable def cartesian_product (A : Set) (B : Set) : Set := {z ∈ 𝒫 (𝒫 (A ∪ B)) | ∃ x ∈ A; ∃ y ∈ B; z = (x, y)}
infix:60 (priority:=high) " × " => cartesian_product

axiom cartesian_product_pair_prop : ∀ A B a b, (a, b) ∈ (A × B) ↔ (a ∈ A ∧ b ∈ B)
axiom cartesian_product_is_cartesian: ∀ A B pr, pr ∈ (A × B) ↔ (∃ x ∈ A; ∃ y ∈ B; pr = (x, y))
axiom cartesian_product_intersect : ∀ A B C D, (A × B) ∩ (C × D) ⊆ (A ∩ C) × (B ∩ D)

axiom cartesian_product_subset : ∀ A B C D, A ⊆ C → B ⊆ D → (A × B) ⊆ C × D

-- tuple syntax
declare_syntax_cat pair_comprehension
syntax  pair_comprehension "; " term : pair_comprehension
syntax term : pair_comprehension
syntax "⁅" pair_comprehension "⁆" : term
macro_rules
| `(⁅ $term1:term; $term2:term⁆) => `(ordered_pair_set $term1 $term2)
| `(⁅ $rest:pair_comprehension; $elem:term⁆) => `(ordered_pair_set ⁅$rest:pair_comprehension⁆ $elem:term)



noncomputable def binary_relation (R : Set) : Prop := ∀ z ∈ R; ∃ a, ∃ b, z = (a, b)

-- write (x . P . y) istead of (x, y) ∈ P
macro_rules
| `(($x:term . $P:term . $y:term)) => `(($x, $y) ∈ $P)


noncomputable def dom (R : Set) := {x ∈ ⋃ (⋃ R) | ∃ y, (x . R . y)}
noncomputable def rng (R : Set) := {y ∈ ⋃ (⋃ R) | ∃ x, (x . R . y)}


axiom binary_relation_prop : ∀ R, binary_relation R → R ⊆ dom R × rng R
axiom prop_then_binary_relation : ∀ A B R, R ⊆ A × B → binary_relation R ∧ dom R ⊆ A ∧ rng R ⊆ B
noncomputable def binary_relation_between (A B R : Set) : Prop := R ⊆ A × B
noncomputable def binary_relation_on (A R : Set) : Prop := R ⊆ A × A
noncomputable def comp (A B R : Set) : Set := (A × B) \ R



noncomputable def inv (R : Set) : Set := {z ∈ rng R × dom R | ∃ x, ∃ y, (z = (y, x) ∧ (x . R . y))}
syntax term"⁻¹" : term
macro_rules
| `($term1:term⁻¹) => `(inv $term1)
noncomputable def composition (P Q : Set) : Set := {pr ∈ dom Q × rng P | ∃ x y, (pr = (x, y)) ∧ ∃ z, (x . Q . z) ∧ (z . P . y)}
infix:60 (priority:=high) " ∘ " => composition

axiom inv_is_rel : ∀ R, binary_relation R → binary_relation (R⁻¹)
axiom inv_prop : ∀ R, binary_relation R → ((R⁻¹)⁻¹) = R
axiom inv_pair_prop : ∀ R, binary_relation R → ∀ x y, (x . R . y) ↔ (y . (R⁻¹) . x)
axiom rel_subset : (∀ P Q, binary_relation P → binary_relation Q → (∀ x y, (x . P . y) → (x . Q . y)) → P ⊆ Q)
axiom relation_equality : (∀ P Q, binary_relation P → binary_relation Q → ((∀ x y, (x . P . y) ↔ (x . Q . y)) → P = Q))
axiom inv_between : ∀ A B R, binary_relation_between A B R → binary_relation_between B A (R⁻¹)



axiom dom_prop : ∀ R x, x ∈ dom R ↔ ∃ y, (x . R . y)
axiom rng_prop : ∀ R y, y ∈ rng R ↔ ∃ x, (x . R . y)


axiom composition_pair_prop : ∀ P Q, ∀ x y, (x . (P ∘ Q) . y) ↔ ∃ z, (x . Q . z) ∧ (z . P . y)
axiom inv_pair_prop_mp : ∀ R, ∀ x y, (x . R . y) → (y . (R⁻¹) . x)


noncomputable def id_ (A : Set) : Set := {t ∈ (A × A) | ∃ x : Set, t = (x, x)}
noncomputable def rel_image (X R : Set) := {b ∈ rng R | ∃ a ∈ X; (a . R . b)}
syntax  term ".[" term "]" : term
macro_rules
  | `($R:term .[ $X:term ])  => `(rel_image $X $R)

axiom rel_pre_image_eq : ∀ Y R, binary_relation R → R⁻¹.[Y] = {a ∈ dom R | ∃ b ∈ Y; (a . R . b)}
axiom dom_preimage : ∀ A B P, binary_relation_between A B P → dom P = P⁻¹.[B]
axiom rel_preimage_composition : ∀ P Q X, binary_relation P → binary_relation Q → (P ∘ Q)⁻¹.[X] = Q⁻¹.[P⁻¹.[X]]
axiom id_is_rel : ∀ A, binary_relation (id_ A)
axiom id_prop : ∀ A x y, (x . (id_ A) . y) → (((x = y) ∧ (x ∈ A)) ∧ (y ∈ A))
axiom prop_then_id : ∀ A, ∀ x ∈ A; (x . (id_ A) . x)
axiom composition_is_rel : ∀ P Q, binary_relation (P ∘ Q)
axiom inv_dom: ∀ R, binary_relation R → dom (R⁻¹) = rng R
axiom inv_between_mp : ∀ A B R, binary_relation_between A B R → binary_relation_between B A (R⁻¹)
axiom union_empty : ⋃ ∅ = ∅
