axiom disj_comm (p q : Prop) : (p ∨ q) ↔ (q ∨ p)
axiom morgan_comm (p q : Prop) : ¬ (p ∧ q) ↔ ¬p ∨ ¬q
axiom iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r)

def xor_pr (p q : Prop) : Prop := (p ∧ ¬q) ∨ (¬p ∧ q)
syntax term "⨁" term : term
macro_rules
| `($p:term ⨁ $q:term) => `(xor_pr $p $q)

-- 28) Xor properties
axiom xor_equiv_def (p q : Prop) : (p ⨁ q) ↔ ((p ∨ q) ∧ (¬ (p ∧ q)))

axiom xor_equal (p : Prop) : ¬ (p ⨁ p)

axiom xor_neg (p : Prop) : (p ⨁ ¬ p)

axiom xor_comm (p q : Prop) : (p ⨁ q) ↔ (q ⨁ p)

axiom xor_assoc (p q r : Prop) : ((p ⨁ q) ⨁ r) ↔ (p ⨁ (q ⨁ r))


axiom xor_introl (p q : Prop) : (p ∧ ¬q) → (p ⨁ q)
axiom xor_intror (p q : Prop) : (¬p ∧ q) → (p ⨁ q)
axiom xor_intro (p q : Prop) : (p ∨ q) → (¬ (p ∧ q)) → (p ⨁ q)
axiom xor_left (p q : Prop) : (p ⨁ q) → (p ∨ q)
axiom xor_right (p q : Prop) : (p ⨁ q) → (¬ (p ∧ q))
axiom xor_elim (p q r : Prop) : (p ⨁ q) → ((p ∧ ¬q) → r) → ((¬p ∧ q) → r) → r

axiom morgan_conj (p q : Prop) :  ¬(p ∧ q) ↔ ¬p ∨ ¬q

def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b




axiom Set : Type
axiom membership : Set → Set → Prop
infix:50 (priority := high) " ∈ " => membership
infix:50 (priority := high) " ∉ " => (fun (x : Set) => (fun (y : Set) => ¬ membership x y))

axiom exists_unique_expansion_curry (P : Set → Prop) :
   (∃! (x : Set), P x) ↔ (∃ (x : Set), P x) ∧ (∀ (x y : Set), (P x → P y → x = y))

axiom set_to_prop (P : Set → Prop) (h : ∃! x, P x) : Set
axiom prop_to_set (P : Set → Prop) (h : ∃! x, P x) : P (set_to_prop P h) ∧ ∀ x, x ≠ set_to_prop P h → ¬P x
axiom eq_congr_func_arg {α β} (f : α → β) : (∀ (x y : α), x = y → f x = f y)
axiom eq_subst (P : Set → Prop) : (∀ (a b : Set), a = b → P a → P b)


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
  | `(∃! $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(exists_uniq_in_A (fun $idnt:ident => (∃! $idnts:idents ∈ $A; $b)) $A)


def empty (A : Set) : Prop := ∀ b, (b ∉ A)
def non_empty (A : Set) : Prop := ∃ b, (b ∈ A)
def subset (A B : Set) : Prop := ∀ x ∈ A; x ∈ B
def is_successor (m n : Set) : Prop := ∀ x, (x ∈ n ↔ x ∈ m ∨ x = m)
infix:50 (priority := high) " ⊆ " => subset
def neq_subset (A B : Set) : Prop := (A ⊆ B) ∧ (A ≠ B)
infix:50 (priority := high) " ⊊ " => neq_subset
def no_subset (A B : Set) : Prop := ¬ (A ⊆ B)
infix:50 (priority := high) " ⊈ " => no_subset

def set_equality (A B : Set) := ∀ x, (x ∈ A ↔ x ∈ B)
axiom extensionality : ∀ A B, set_equality A B → (A = B)
axiom exists_unique_empty : (∃! x, empty x)
axiom unique_unordered_pair : (∀ a₁ a₂, ∃! C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂))
axiom unique_union : ∀ A, ∃! B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)
axiom unique_specification (P : Set → Prop) : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x))
axiom unique_boolean : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ⊆ A))
axiom subset_refl : ∀ A, A ⊆ A




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





axiom spec_is_spec (P : Set → Prop) : (∀ A x, x ∈ {x ∈ A | P x} ↔ x ∈ A ∧ P x)

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

axiom sub_sub_then_eq : ∀ A B, (A ⊆ B) → (B ⊆ A) → (A = B)
axiom empty_set_is_empty : empty ∅
axiom elem_in_singl : ∀ x, x ∈ {x}
axiom in_singl_elem : ∀ a x, x ∈ {a} → x = a
axiom subset_using_equality : ∀ A B, (A ⊆ B ↔ A ∩ B = A) ∧ (A ⊆ B ↔ A ∪ B = B) ∧ (A ∩ B = A ↔ A ∪ B = B)
axiom intersec2_comm : (∀ A B, A ∩ B = B ∩ A)
axiom intersect_2sets_prop : (∀ A B x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B)
axiom interset2sets_subset_prop : (∀ A B, (A ∩ B ⊆ A) ∧ (A ∩ B ⊆ B))
axiom union2sets_prop : (∀ A B x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B)
axiom difference_subset_prop : (∀ A B, A \ B ⊆ A)
axiom difference_prop : (∀ A B x, x ∈ A \ B ↔ x ∈ A ∧ x ∉ B)
axiom specification_set_subset (P : Set → Prop) : (∀ A, {x ∈ A | P x} ⊆ A)
axiom unordered_pair_set_is_unordered_pair : ∀ a₁ a₂ x, x ∈ {a₁, a₂} ↔ x = a₁ ∨ x = a₂
axiom left_unordered_pair : ∀ a₁ a₂, a₁ ∈ {a₁, a₂}
axiom right_unordered_pair : ∀ a₁ a₂, a₂ ∈ {a₁, a₂}
axiom empty_subset_any : ∀ A B, empty A → A ⊆ B
axiom empty_set_is_subset_any : ∀ A, ∅ ⊆ A
axiom non_empty_uni_then_exi (P : Set → Prop) : ∀ A, (A ≠ ∅) → (∀ x ∈ A; P x) → ∃ x ∈ A; P x
axiom set_empty_iff_empty : ∀ A, (A = ∅) ↔ (∀ x, x ∉ A)
axiom set_non_empty_iff_non_empty : ∀ A, (A ≠ ∅) ↔ ∃ x, x ∈ A
axiom neg_mon_diff : ∀ A B C, (A ⊆ B) → (C \ B) ⊆ (C \ A)
axiom double_compl (U : Set) (A : Set)  (h : A ⊆ U) : (U \ (U \ A)) = A
axiom intersec2_idemp : (∀ A, A ∩ A = A)
axiom intersection_set_is_intersection : ∀ A x, x ∈ ⋂ A ↔ (x ∈ ⋃ A ∧ ∀ y ∈ A; x ∈ y)
axiom union_set_is_union : (∀ A x, (x ∈ ⋃ A ↔ ∃ y ∈ A; x ∈ y))
axiom intersection_non_empty : ∀ A, (A ≠ ∅ → ∀ x, (x ∈ ⋂ A) ↔ ∀ y ∈ A; x ∈ y)
axiom union_singleton : ∀ A, ⋃ {A} = A
axiom sub_sub_inter_sub : ∀ A B X, (X ⊆ A) → (X ⊆ B) → (X ⊆ (A ∩ B))
axiom sub_sub_union_sub : ∀ A B X, (A ⊆ X) → (B ⊆ X) → ((A ∪ B) ⊆ X)
axiom subset_trans : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C
axiom elem_subset_union : (∀ A, ∀ x ∈ A; x ⊆ ⋃ A)
axiom all_ss_then_union_ss : ∀ A B, (∀ X ∈ A; X ⊆ B) → (⋃ A ⊆ B)



axiom inter_union_distribution : (∀ A B C, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C))


declare_syntax_cat set_comprehension
syntax term "; " set_comprehension : set_comprehension
syntax term : set_comprehension
syntax "{" set_comprehension "}" : term

macro_rules
| `({$term1:term}) => `(singleton_set $term1:term)
| `({$term1:term; $term2:term}) => `(unordered_pair_set $term1:term $term2:term)
| `({$elem:term; $rest:set_comprehension}) => `({$rest:set_comprehension} ∪ {$elem:term})




noncomputable def boolean_func_sym : Set → Set :=
  fun (A : Set) => set_to_prop (fun (B : Set) => ∀ x, (x ∈ B ↔ x ⊆ A)) (unique_boolean A)


notation (priority := high) "𝒫" => boolean_func_sym

axiom boolean_set_is_boolean : ∀ A, (∀ x, x ∈ 𝒫 A ↔ x ⊆ A)
axiom sub_bool_un_mem_bool : ∀ A B, (A ⊆ 𝒫 B → ((⋃ A) ∈ 𝒫 B))

noncomputable def singlbool_set (A) := {S ∈ 𝒫 (A) | ∃ x ∈ A; S = {x}}
syntax "𝒫₁" term : term
macro_rules
| `(𝒫₁ $A) => `(singlbool_set $A)

axiom singlbool_set_prop : ∀ A S, (S ∈ 𝒫₁ (A)) ↔ (∃ x ∈ A; S = {x})
axiom in_singlbool_set : ∀ A x, ({x} ∈ 𝒫₁ (A)) ↔ (x ∈ A)

noncomputable def ordered_pair_set (a b : Set) := {{a}, {a, b}}
notation (priority := high) "(" a₁ ", " a₂ ")" => ordered_pair_set a₁ a₂


axiom ordered_pair_set_prop : ∀ a b c d, (a, b) = (c, d) ↔ (a = c ∧ b = d)

noncomputable def fst_coor (A : Set) : Set := ⋃ (⋂ A)
noncomputable def snd_coor (A : Set) : Set := ⋃ ({x ∈ ⋃ A | ⋃ A ≠ ⋂ A → x ∉ ⋂ A})

syntax "π₁" term : term
syntax "π₂" term : term
macro_rules
| `(π₁ $s) => `(fst_coor $s)
| `(π₂ $s) => `(snd_coor $s)

axiom coordinates_fst_coor : ∀ a b, fst_coor (a, b) = a
axiom coordinates_snd_coor : ∀ a b, snd_coor (a, b) = b

noncomputable def cartesian_product (A : Set) (B : Set) : Set := {z ∈ 𝒫 (𝒫 (A ∪ B)) | ∃ x ∈ A; ∃ y ∈ B; z = (x, y)}
infix:60 (priority:=high) " × " => cartesian_product


axiom union2sets_subset_prop : (∀ A B, (A ⊆ A ∪ B) ∧ (B ⊆ A ∪ B))
axiom cartesian_product_is_cartesian: ∀ A B pr, pr ∈ (A × B) ↔ (∃ x ∈ A; ∃ y ∈ B; pr = (x, y))
axiom cartesian_product_pair_prop : ∀ A B a b, (a, b) ∈ (A × B) ↔ (a ∈ A ∧ b ∈ B)
axiom cartesian_product_subset : ∀ A B C D, A ⊆ C → B ⊆ D → (A × B) ⊆ C × D
axiom fst_coor_set : ∀ A B pr, pr ∈ A × B → fst_coor pr ∈ A
axiom snd_coor_set : ∀ A B pr, pr ∈ A × B → snd_coor pr ∈ B
axiom fst_snd_then_unique : ∀ A B pr, pr ∈ A × B → pr = (fst_coor pr, snd_coor pr)
axiom equal_fst_snd : ∀ A B pr₁ pr₂, (pr₁ ∈ A × B) → (pr₂ ∈ A × B) →
  (fst_coor pr₁ = fst_coor pr₂) → (snd_coor pr₁ = snd_coor pr₂) → pr₁ = pr₂
axiom boolean_set_not_empty : ∀ A, 𝒫 A ≠ ∅



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


axiom dom_prop : ∀ R x, x ∈ dom R ↔ ∃ y, (x . R . y)
axiom rng_prop : ∀ R y, y ∈ rng R ↔ ∃ x, (x . R . y)

noncomputable def binary_relation_between (A B R : Set) : Prop := R ⊆ A × B
noncomputable def binary_relation_on (A R : Set) : Prop := R ⊆ A × A
noncomputable def comp (A B R : Set) : Set := (A × B) \ R

syntax "BinRel" term : term
macro_rules
|  `(BinRel $R:term) => `(binary_relation $R)
syntax term "BinRelOn" term : term
macro_rules
| `($R:term BinRelOn $A:term) => `(binary_relation_on $A $R)
syntax term "BinRelBtw" term "AND" term : term
macro_rules
| `($R:term BinRelBtw $A:term AND $B:term) => `(binary_relation_between $A $B $R)



noncomputable def inv (R : Set) : Set := {z ∈ rng R × dom R | ∃ x, ∃ y, (z = (y, x) ∧ (x . R . y))}
syntax term"⁻¹" : term
macro_rules
| `($term1:term⁻¹) => `(inv $term1)
noncomputable def composition (P Q : Set) : Set := {pr ∈ dom Q × rng P | ∃ x y, (pr = (x, y)) ∧ ∃ z, (x . Q . z) ∧ (z . P . y)}
infix:60 (priority:=high) " ∘ " => composition




axiom inv_is_rel : ∀ R, binary_relation R → (binary_relation (R⁻¹))
axiom inv_prop : ∀ R, (BinRel R) → (R⁻¹)⁻¹ = R
axiom inv_pair_prop: ∀ R, binary_relation R → ∀ x y, (x . R . y) ↔ (y . (R⁻¹) . x)
axiom inv_composition_prop : ∀ P Q, (BinRel P) → (BinRel Q) → (P ∘ Q)⁻¹ = ((Q⁻¹) ∘ (P⁻¹))
axiom inv_union_prop : ∀ P Q, (BinRel P) → (BinRel Q) → (P ∪ Q)⁻¹ = ((P⁻¹) ∪ Q⁻¹)

axiom composition_assoc : ∀ P Q R, ((P ∘ Q) ∘ R) = (P ∘ (Q ∘ R))
axiom union2_rel_is_rel : ∀ P Q, binary_relation P → binary_relation Q → binary_relation (P ∪ Q)

axiom relation_equality : (∀ P Q, (BinRel P) → (BinRel Q) → ((∀ x y, (x . P . y) ↔ (x . Q . y)) → P = Q))


noncomputable def id_ (A : Set) : Set := {t ∈ (A × A) | ∃ x : Set, t = (x, x)}
axiom id_is_rel : ∀ A, binary_relation (id_ A)
noncomputable def rel_image (X R : Set) := {b ∈ rng R | ∃ a ∈ X; (a . R . b)}
syntax  term ".[" term "]" : term
macro_rules
  | `($R:term .[ $X:term ])  => `(rel_image $X $R)


axiom id_prop : ∀ A x y, (x . (id_ A) . y) → (((x = y) ∧ (x ∈ A)) ∧ (y ∈ A))
axiom rel_subset : (∀ P Q, binary_relation P → binary_relation Q → (∀ x y, (x . P . y) → (x . Q . y)) → P ⊆ Q)
axiom prop_then_id : ∀ A, ∀ x ∈ A; (x . (id_ A) . x)
axiom inv_id : ∀ A, ((id_ A)⁻¹) = (id_ A)
axiom inv_between_mp : ∀ A B R, (R BinRelBtw A AND B) → (R⁻¹ BinRelBtw B AND A)
axiom composition_is_relbtw : ∀ P Q A B C, (P BinRelBtw B AND C) → (Q BinRelBtw A AND B) → ((P ∘ Q) BinRelBtw A AND C)

axiom intersect2_rel_is_rel : ∀ P Q, binary_relation P → binary_relation Q → binary_relation (P ∩ Q)

axiom prop_then_binary_relation : ∀ A B R, R ⊆ A × B → binary_relation R ∧ dom R ⊆ A ∧ rng R ⊆ B

axiom composition_is_rel : ∀ P Q, binary_relation (P ∘ Q)
axiom composition_pair_prop : ∀ P Q, ∀ x y, (x . (P ∘ Q) . y) ↔ ∃ z, (x . Q . z) ∧ (z . P . y)

axiom id_rel_composition_left : ∀ A B  R, binary_relation_between A B R → ((id_ B) ∘ R) = R
axiom id_rel_composition_right : ∀ A B R, binary_relation_between A B R → (R ∘ (id_ A)) = R
axiom monotonic_rel_image : ∀ X Y R, binary_relation R → X ⊆ Y → R.[X] ⊆ R.[Y]

axiom relation_equality_btw : ∀ P Q A B, (P BinRelBtw A AND B) → (Q BinRelBtw A AND B) → (∀ x ∈ A; ∀ y ∈ B; (x . P . y) ↔ (x . Q . y)) → (P = Q)

axiom rng_is_rel_image : ∀ R, binary_relation R → rng R = R.[dom R]
axiom image_prop : ∀ R X y, (y ∈ R.[X] ↔ ∃ x ∈ X; (x . R . y))

axiom rel_pre_image_eq : ∀ Y R, (BinRel R) → R⁻¹.[Y] = {a ∈ dom R | ∃ b ∈ Y; (a . R . b)}

noncomputable def is_functional (R : Set) : Prop := ∀ x y z, (x . R . y) → (x . R . z) → y = z
noncomputable def is_total (R X : Set) : Prop := ∀ x ∈ X; ∃ y, (x . R . y)
noncomputable def is_injective (R : Set) : Prop := ∀ x y z, (x . R . z) → (y . R . z) → x = y
noncomputable def is_surjective (R Y : Set) : Prop := ∀ y ∈ Y; ∃ x, (x . R . y)

noncomputable def rel_is_functional (R : Set) : Prop := binary_relation R ∧ is_functional R
noncomputable def rel_is_total (R X : Set) : Prop := binary_relation R ∧ is_total R X
noncomputable def rel_is_injective (R : Set) : Prop := binary_relation R ∧ is_injective R
noncomputable def rel_is_surjective (R Y : Set) : Prop := binary_relation R ∧ is_surjective R Y


noncomputable def partial_function (f A B : Set) : Prop := binary_relation_between A B f ∧ is_functional f
noncomputable def function (f A B : Set) : Prop := partial_function f A B ∧ is_total f A
syntax term "PartFun" term "To" term : term
macro_rules
  | `($f:term PartFun $A:term To $B:term)  => `(partial_function $f $A $B)
syntax term "Fun" term "To" term : term
macro_rules
  | `($f:term Fun $A:term To $B:term) => `(function $f $A $B)




axiom function_change_B : ∀ f A B C, (f Fun A To B) → (B ⊆ C) → (f Fun A To C)
axiom function_rng_def : ∀ f A B, (f Fun A To B) → (f Fun A To (rng f))
axiom rng_partial_function : ∀ f A B, (f PartFun A To B) → rng f ⊆ B

noncomputable def val_defined (f x : Set) : Prop := x ∈ dom f
noncomputable def val_undefined (f x : Set) : Prop := x ∉ dom f
syntax term "↓↓" term : term
macro_rules
  | `($f:term ↓↓ $x:term) => `(val_defined $f $x)
syntax term "↑↑" term : term
macro_rules
  | `($f:term ↑↑ $x:term) => `(val_undefined $f $x)

noncomputable def value_pick (f x : Set) : Set := ⋃ (f  .[ { x } ])
syntax term "⦅" term "⦆" : term
macro_rules
  | `($f:term ⦅ $x:term ⦆) => `(value_pick $f $x)

axiom val_in_B : ∀ f A B, (f Fun A To B) → ∀ x ∈ A; f⦅x⦆ ∈ B
axiom val_in_rng : ∀ f A B, (f Fun A To B) → ∀ x ∈ A; f⦅x⦆ ∈ rng f
axiom function_equal_value_prop : ∀ f A B, (f Fun A To B) → ∀ x y, x ∈ A → ( (x . f . y) ↔ (y = f⦅x⦆))
axiom dom_function: ∀ f A B, (f Fun A To B) → A = dom f
axiom function_value_pick_property: ∀ f A B, ∀ x ∈ A; (f Fun A To B) → (x . f . (f⦅x⦆) )
axiom if_val_in_C : ∀ f A B C, (f Fun A To B) → (∀ x ∈ A; (f⦅x⦆ ∈ C)) → (f Fun A To C)

noncomputable def part_same_val (f g x y : Set) : Prop := ((f ↑↑ x) ∧ g ↑↑ y) ∨ (((f ↓↓ x) ∧ (g ↓↓ y)) ∧ (f⦅x⦆ = g⦅y⦆))

syntax term "（" term "）" "≈" term "﹙" term "﹚" : term
macro_rules
  | `($f:term （ $x:term ） ≈ $g:term ﹙ $y:term ﹚) => `(part_same_val $f $g $x $y)


axiom function_composition : ∀ f g A B C, (f Fun A To B) → (g Fun B To C) → (((g ∘ f) Fun A To C) ∧ (∀ x ∈ dom f; (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆))

noncomputable def lam_fun (A B : Set) (P : Set → Set): Set := {z ∈ A × B | ∃ x, z = (x, P x)}
noncomputable def fun_restriction (f A : Set) := f ∩ (A × rng f)
infix:50 (priority := high) "⨡" => fun_restriction

axiom fun_restriction_prop : ∀ A B X f, (f Fun A To B) → (f ⨡ X) Fun (A ∩ X) To B
axiom fun_restriction_val : ∀ A B X f, (X ⊆ A) → (f Fun A To B) → ∀ x ∈ X; f⦅x⦆ = (f ⨡ X)⦅x⦆
axiom inj_restriction_prop : ∀ X f, (is_injective f) → (is_injective (f ⨡ X))



noncomputable def injection (f A B : Set) := (f Fun A To B) ∧ (is_injective f)
noncomputable def surjection (f A B : Set) := (f Fun A To B) ∧ (is_surjective f B)
noncomputable def bijection (f A B : Set) := (f Fun A To B) ∧ (is_injective f) ∧ (is_surjective f B)
syntax term "Inj" term "To" term : term
syntax term "Surj" term "To" term : term
syntax term "Bij" term "To" term : term
macro_rules
  | `($f:term Inj $A:term To $B:term) => `(injection $f $A $B)
  | `($f:term Surj $A:term To $B:term) => `(surjection $f $A $B)
  | `($f:term Bij $A:term To $B:term) => `(bijection $f $A $B)


axiom bij_is_inj : ∀ A B f, (f Bij A To B) → (f Inj A To B)
axiom bij_is_surj : ∀ A B f, (f Bij A To B) → (f Surj A To B)


axiom func_inj_prop : ∀ A B f, (f Fun A To B) → ((f Inj A To B) ↔ (∀ x y ∈ A; (f⦅x⦆ = f⦅y⦆) → x = y))
axiom func_surj_prop : ∀ A B f, (f Fun A To B) → ((f Surj A To B) ↔ (∀ y ∈ B; ∃ x ∈ A; y = f⦅x⦆))


axiom id_is_bij : ∀ A, (id_ A) Bij A To A
axiom id_val_prop : ∀ A x, (x ∈ A) → (id_ A⦅x⦆ = x)
axiom bijection_inv_mp : ∀ f A B, ((f Bij A To B) → (f⁻¹ Bij B To A))
axiom bijection_composition : ∀ f g A B C, (f Bij A To B) → (g Bij B To C) → ((g ∘ f) Bij A To C)
axiom lam_then_fun_prop (P : Set → Set) : ∀ A B, (∀ x ∈ A; P x ∈ B) →  (((lam_fun A B P) Fun A To B) ∧ (∀ x ∈ A; (lam_fun A B P)⦅x⦆ = P x))
axiom id_bijection_criterion : ∀ f A B, binary_relation_between A B f → ((f Bij A To B) ↔ ((f⁻¹ ∘ f = id_ A) ∧ (f ∘ f⁻¹ = id_ B)))
axiom equal_functions_abc_A:  ∀ f g A B C, (f Fun A To B) → (g Fun A To C) → ((f = g) ↔ (∀ x ∈ A; f⦅x⦆ = g⦅x⦆))
axiom injection_composition : ∀ f g A B C, (f Inj A To B) → (g Inj B To C) → (((g ∘ f) Inj A To C))
axiom surjection_composition : ∀ f g A B C, (f Surj A To B) → (g Surj B To C) → (((g ∘ f) Surj A To C))
axiom func_surj_crit : ∀ A B f, (f Fun A To B) → ((f Surj A To B) ↔ rng f = B)
axiom part_func_img_prop : ∀ f A B, (f PartFun A To B) → ∀ X, f.[X] ⊆ B

axiom monotonic_operator_fix_point : ∀ A F, (F Fun 𝒫 A To 𝒫 A) → (∀ X Y ∈ 𝒫 A; X ⊆ Y → F⦅X⦆ ⊆ F⦅Y⦆) → (∃ Z ∈ 𝒫 A; F⦅Z⦆ = Z)

axiom bij_finv_f : ∀ f A B, (f Bij A To B) → (∀ x ∈ A; (f⁻¹⦅f⦅x⦆⦆) = x)
axiom bij_f_finv : ∀ f A B, (f Bij A To B) → (∀ x ∈ B; (f⦅f⁻¹⦅x⦆⦆) = x)
axiom bijimg_finv_f : ∀ f A B, (f Bij A To B) → (∀ X, (X ⊆ A) → (f⁻¹.[f.[X]] = X))
axiom bijimg_f_finv : ∀ f A B, (f Bij A To B) → (∀ X, (X ⊆ B) → (f.[f⁻¹.[X]] = X))

noncomputable def power_set (B A : Set) : Set := {f ∈ 𝒫 (A × B) | f Fun A To B}
syntax term "ℙow" term : term
macro_rules
  |`($A:term ℙow $B:term) => `(power_set $A $B)
axiom power_set_prop : ∀ A B f, f ∈ (B ℙow A) ↔ f Fun A To B

axiom equinum_image_f : ∀ A B X f, X ⊆ A → (f Inj A To B) → (f ⨡ X) Bij X To (f.[X])


noncomputable def lam_cond_fun (A B : Set) (P : Set → Prop) (c d : Set → Set) :=
  {z ∈ A × B | ∃ x, (P x → z = (x, c x)) ∧ (¬P x → z = (x, d x))}
axiom lam_cond_part_fun_prop : ∀ A B : Set, ∀ P : Set → Prop, ∀ c d : Set → Set,
  ((lam_cond_fun A B P c d) PartFun A To B) ∧
  (∀ x ∈ dom (lam_cond_fun A B P c d) ;
  (P x → (lam_cond_fun A B P c d)⦅x⦆ = c x) ∧ (¬P x → (lam_cond_fun A B P c d)⦅x⦆ = d x))
axiom lam_cond_fun_prop : ∀ A B : Set, ∀ P : Set → Prop, ∀ c d : Set → Set,
  (∀ x ∈ A; (P x → c x ∈ B) ∧ (¬P x → d x ∈ B)) →
  ((lam_cond_fun A B P c d) Fun A To B) ∧
  (∀ x ∈ A ; (P x → (lam_cond_fun A B P c d)⦅x⦆ = c x) ∧ (¬P x → (lam_cond_fun A B P c d)⦅x⦆ = d x))


noncomputable def left_reversable (f A B : Set) : Prop := (f Fun A To B) ∧ ∃ g, (g Fun B To A) ∧ (g ∘ f = id_ A)
noncomputable def right_reversable (f A B : Set) : Prop := (f Fun A To B) ∧ ∃ g, (g Fun B To A) ∧ (f ∘ g = id_ B)
noncomputable def reversable (f A B : Set) : Prop := (f Fun A To B) ∧ ∃ g, (g Fun B To A) ∧ (g ∘ f = id_ A) ∧ (f ∘ g = id_ B)
syntax term "LeftRev" term "To" term : term
macro_rules
  | `($f:term LeftRev $A:term To $B:term)  => `(left_reversable $f $A $B)
syntax term "RightRev" term "To" term : term
macro_rules
  | `($f:term RightRev $A:term To $B:term) => `(right_reversable $f $A $B)
syntax term "Rev" term "To" term : term
macro_rules
  | `($f:term Rev $A:term To $B:term) => `(reversable $f $A $B)

noncomputable def choice_function (A f : Set) : Prop := (f Fun A To (⋃ A)) ∧ (∀ X ∈ A; f⦅X⦆ ∈ X)
syntax term "Choice" term : term
infix:60 (priority := high) " Choice " => fun (f) => fun (A) => choice_function A f

axiom rev_criterion :
 ∀ f A B, (f Rev A To B) ↔ (f Bij A To B)

axiom leftrev_criterion:
  ∀ f A B, (f LeftRev A To B) ↔ ((f Inj A To B) ∧ (A ≠ ∅ ∨ B = ∅))

def choice_ax : Prop := ∀ A, ∅ ∉ A → ∃ f, f Choice A

axiom axiom_of_choice : choice_ax


axiom function_composition_A :
∀ f g A B C, (f Fun A To B) → (g Fun B To C) → (((g ∘ f) Fun A To C) ∧ (∀ x ∈ A; (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆))





def right_rev_criterion_prop : Prop := ∀ f A B, (f RightRev A To B) ↔ (f Surj A To B)

axiom rightrev_criterion_AC_eq: choice_ax ↔ right_rev_criterion_prop


syntax term "⦅" term "," term "⦆" : term
syntax term "⦅" pair_comprehension "⦆" : term
macro_rules
| `($f:term ⦅ $x:term ; $y:term ⦆) =>  `($f⦅($x, $y)⦆)
| `($f:term ⦅ $x:pair_comprehension ; $y:term ⦆) => `($f⦅⁅ $x ; $y ⁆⦆)


def equinumerous (A B : Set) : Prop := ∃ f, f Bij A To B
syntax term "~" term : term
syntax term "≁" term : term
macro_rules
  | `($A:term ~ $B:term) => `(equinumerous $A $B)
  | `($A:term ≁ $B:term) => `(¬($A ~ $B))


axiom equinum_refl : ∀ A, A ~ A
axiom equinum_symm : ∀ A B, (A ~ B) → B ~ A
axiom equinum_trans : ∀ A B C, (A ~ B) → (B ~ C) → (A ~ C)


def includes (A B : Set) := ∃ f, f Inj A To B
syntax term "≾" term : term
syntax term "⋨" term : term
syntax term "⋠" term : term
macro_rules
  | `($A:term ≾ $B:term) => `(includes $A $B)
  | `($A:term ⋠ $B:term) => `(¬($A ≾ $B))
  | `($A:term ⋨ $B:term) => `(($A ≾ $B) ∧ ($A ≁ $B))


def covers (A B : Set) := ∃ f, f Surj A To B
syntax term "≿" term : term
syntax term "⋩" term : term
syntax term "⋡" term : term
macro_rules
| `($A:term ≿ $B:term) => `(covers $A $B)
| `($A:term ⋩ $B:term) => `(¬ ($A ≿ $B))
| `($A:term ⋡ $B:term) => `(($A ≿ $B) ∧ ($A ≁ $B))


theorem incl_cov_prop_AC : choice_ax → (∀ A B, (A ≾ B) ↔ ((B ≿ A) ∨ (A = ∅ ∧ B ≠ ∅))) := sorry


-- 38) Indexation with function· defintion
def fun_indexation (A I : Set) : Prop := ∃ X, A Fun I To X
syntax term "IndxFun" term : term
macro_rules
| `($A:term IndxFun $I:term) => `(fun_indexation  $A $I)

-- 39) Indexed family
noncomputable def indexed_family (A I : Set) := A.[I]
syntax "{" term "of" term "where" term "in" term "}" : term
macro_rules
| `({ $A:term of $i:term where $i:term in $I:term }) => `(indexed_family $A $I)


-- 40) Element of indexation
noncomputable def indexed_set (A i : Set) := A⦅i⦆
infix:60 (priority := high) " _ " => indexed_set


-- 41) Indexation defintion and its condition
def indexation (A I : Set) : Prop := (∀ x, (x ∈ ({A of i where i in I})) ↔ (∃ i ∈ I; x = (A _ i)))
syntax term "Indx" term : term
macro_rules
| `($A:term Indx $I:term) => `(indexation $A $I)
axiom fun_indexed_is_indexed :
∀ A I, (A IndxFun I) → (A Indx I)


-- 42) Indexed_union and its property
noncomputable def indexed_union (A I : Set) := ⋃ (A.[I])
syntax "⋃[" term "in" term "]" term "at" term : term
macro_rules
| `(⋃[ $i:term in $I:term ] $A:term at $i:term ) => `(indexed_union $A $I)
axiom indexed_union_is_union :
∀ A I, (A Indx I) → ∀ x, (x ∈ (⋃[ i in I ] A at i)) ↔ (∃ i ∈ I; x ∈ (A _ i))
axiom indexed_sub_indexed_union : ∀ A I, (A Indx I) → (∀ i ∈ I; (A _ i) ⊆ (⋃[ i in I ] A at i))


-- 43) Indexed_intersection and its property
noncomputable def indexed_intersection (A I : Set) := ⋂ (A.[I])
syntax "⋂[" term "in" term "]" term "at" term : term
macro_rules
| `(⋂[ $i:term in $I:term ] $A:term at $i:term ) => `(indexed_intersection $A $I)
axiom indexed_intersection_is_intersection :
∀ A I, (I ≠ ∅) → (A IndxFun I) → ∀ x, (x ∈ (⋂[ i in I ] A at i)) ↔ (∀ i ∈ I; x ∈ (A _ i))
axiom indexed_intersection_sub_indexed :
∀ A I, (A IndxFun I) → (∀ i ∈ I; (⋂[ i in I ] A at i) ⊆ (A _ i))
axiom indexed_intersection_empty :
∀ A I, (I = ∅) → ((⋂[ i in I ] A at i) = ∅)




-- Now we again consider arbitrary binary relations between A and B
-- But let A = B
-- (We consider binary relations on one set A)


-- 1) Some information about binary relations on one set and specification on binary relation
axiom bin_on_is_bin : ∀ A R, binary_relation_on A R → binary_relation R
axiom id_is_binon : ∀ A, ((id_ A) BinRelOn A)
noncomputable def rel_specification (R B) := R ∩ (B × B)
syntax term "spec" term : term
macro_rules
| `($R spec $B) => `(rel_specification $R $B)


-- 2) properties of binary relations on one set
def refl (R A : Set) : Prop := ∀ x ∈ A; (x . R . x)
def irrefl (R : Set) : Prop := ∀ x, ¬ (x . R . x)
def symm (R : Set) : Prop := ∀ x y, ((x . R . y) → (y . R . x))
def antisymm (R : Set) : Prop := ∀ x y, ((x . R . y) ∧ (y . R . x) → (x = y))
def asymm (R : Set) : Prop := ∀ x y, ((x . R . y) → ¬ (y . R . x))
def transit(R : Set) : Prop := ∀ x y z, (x . R . y) ∧ (y . R . z) → (x . R . z)
def str_conn (R A : Set) : Prop := ∀ x y ∈ A; ((x . R . y) ∨ (y . R . x))
def wkl_conn (R A : Set) : Prop := ∀ x y ∈ A; ((x ≠ y) → (x . R . y) ∨ (y . R . x))
def trichotomous (R A : Set) : Prop := ∀ x y ∈ A; ((x = y) ⨁ (x . R . y) ⨁ (y . R . x))


-- 3) Criteria of the properties of binary relations on one sets
axiom refl_crit : ∀ A R, (R BinRelOn A) → ((refl R A) ↔ ((id_ A) ⊆ R))
axiom irrefl_crit : ∀ A R, (R BinRelOn A) → ((irrefl R) ↔ (R ∩ (id_ A) = ∅))
axiom symmetric_crit_sub_left : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R ⊆ R⁻¹))
axiom symmetric_crit_sub_right : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R⁻¹ ⊆ R))
axiom symmetric_crit_eq : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R = R⁻¹))
axiom antisymmetric_crit : ∀ A R, (R BinRelOn A) → ((antisymm R) ↔ (R ∩ R⁻¹ ⊆ (id_ A)))
axiom asymmetric_crit : ∀ A R, (R BinRelOn A) → ((asymm R) ↔ (R ∩ R⁻¹ = ∅))
axiom transitive_crit : ∀ A R, (R BinRelOn A) → ((transit R) ↔ (R ∘ R ⊆ R))
axiom strongly_connected_crit : ∀ A R, (R BinRelOn A) → ((str_conn R A) ↔ ((A × A) ⊆ (R ∪ R⁻¹)))
axiom weakly_connected_crit : ∀ A R, (R BinRelOn A) → ((wkl_conn R A) ↔ (((A × A) \ (id_ A)) ⊆ (R ∪ R⁻¹)))


-- 4) Relations between properties
axiom assym_iff_antisymm_irrefl : ∀ A R, (R BinRelOn A) → ((asymm R) ↔ (antisymm R ∧ irrefl R))
axiom strcon_iff_wkcon_refl : ∀ A R, (R BinRelOn A) → ((str_conn R A) ↔ (wkl_conn R A ∧ refl A R))
axiom emp_refl_irrefl : ∀ A R, (R BinRelOn A) → ((A = ∅) ↔ (refl R A ∧ irrefl R))
axiom emp_symm_asymm : ∀ A R, (R BinRelOn A) → ((R = ∅) ↔ (symm R ∧ asymm R))
axiom trans_irrefl_antisymm : ∀ A R, (R BinRelOn A) → (transit R) → (irrefl R) → (antisymm R)
axiom trans_irrefl_asymm : ∀ A R, (R BinRelOn A) → (transit R) → (irrefl R) → (asymm R)
axiom refl_symm_antisymm : ∀ A R, (R BinRelOn A) → (((refl R A) ∧ (symm R) ∧ (antisymm R)) ↔ (R = (id_ A)))


-- 5) Inverse relation to the properties
axiom inv_binon : ∀ A R, (R BinRelOn A) → ((R⁻¹) BinRelOn A)
axiom refl_inv : ∀ A R, (R BinRelOn A) → ((refl R A) ↔ (refl (R⁻¹) A))
axiom irrefl_inv : ∀ A R, (R BinRelOn A) → ((irrefl R) ↔ (irrefl (R⁻¹)))
axiom symm_inv : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (symm (R⁻¹)))
axiom antisymm_inv : ∀ A R, (R BinRelOn A) → ((antisymm R) ↔ (antisymm (R⁻¹)))
axiom asymm_inv : ∀ A R, (R BinRelOn A) → ((asymm R) ↔ (asymm (R⁻¹)))
axiom transit_inv : ∀ A R, (R BinRelOn A) → ((transit R) ↔ (transit (R⁻¹)))
axiom str_conn_inv : ∀ A R, (R BinRelOn A) → ((str_conn R A) ↔ (str_conn (R⁻¹) A))
axiom wkl_conn_inv : ∀ A R, (R BinRelOn A) → ((wkl_conn R A) ↔ (wkl_conn (R⁻¹) A))


-- 6) Composition relation to the properties
axiom compos_binon : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → ((P ∘ Q) BinRelOn A)
axiom refl_compos_char : ∀ A P Q, (refl P A) → (refl Q A) → (refl (P ∘ Q) A)
axiom refl_compos_prop : ∀ A P Q, (refl (P ∘ Q) A) → ((is_surjective P A) ∧ (is_total Q A))
axiom symm_compos_prop : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → (symm P) → (symm Q) → (((P ∘ Q)⁻¹) = (Q ∘ P))


-- 7) Subset relation to the properties
axiom subs_binon : ∀ A P Q, (Q BinRelOn A) → (P ⊆ Q) → (P BinRelOn A)
axiom refl_subs : ∀ A P Q, (refl P A) → (P ⊆ Q) → (refl Q A)
axiom irrefl_subs : ∀ P Q, (irrefl Q) → (P ⊆ Q) → (irrefl P)
axiom antisymm_subs : ∀ P Q, (antisymm Q) → (P ⊆ Q) → (antisymm P)
axiom asymm_subs : ∀ P Q, (asymm Q) → (P ⊆ Q) → (asymm P)
axiom str_conn_subs : ∀ A P Q, (P ⊆ Q) → (str_conn P A) → (str_conn Q A)
axiom wkl_conn_subs : ∀ A P Q, (P ⊆ Q) → (wkl_conn P A) → (wkl_conn Q A)


-- 8) Union relations to the properties
axiom un_binon : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → ((P ∪ Q) BinRelOn A)
axiom refl_un_left : ∀ A P Q, (refl P A) → (refl (P ∪ Q) A)
axiom refl_un_right : ∀ A P Q, (refl Q A) → (refl (P ∪ Q) A)
axiom irrefl_un : ∀ P Q, (irrefl P) → (irrefl Q) → (irrefl (P ∪ Q))
axiom symm_un : ∀ P Q, (symm P) → (symm Q) → (symm (P ∪ Q))
axiom str_un : ∀ A P Q, (str_conn P A) → (str_conn Q A) → (str_conn (P ∪ Q) A)
axiom str_con_un_left : ∀ A P Q, (str_conn P A) → (str_conn (P ∪ Q) A)
axiom str_con_un_right : ∀ A P Q, (str_conn Q A) → (str_conn (P ∪ Q) A)
axiom wkl_con_un_left : ∀ A P Q, (wkl_conn P A) → (wkl_conn (P ∪ Q) A)
axiom wkl_con_un_right : ∀ A P Q, (wkl_conn Q A) → (wkl_conn (P ∪ Q) A)


-- 9) Intersection relation to the properties
axiom int_binon_left : ∀ A P Q, (P BinRelOn A) → ((P ∩ Q) BinRelOn A)
axiom int_binon_right : ∀ A P Q, (Q BinRelOn A) → ((P ∩ Q) BinRelOn A)
axiom refl_int_left : ∀ A P Q, (refl P A) → (refl Q A) → (refl (P ∩ Q) A)
axiom irrefl_int_right : ∀ P Q, (irrefl Q) → (irrefl (P ∩ Q))
axiom symm_int : ∀ P Q, (symm P) → (symm Q) → (symm (P ∩ Q))
axiom antisym_int : ∀ P Q, (antisymm P) → (antisymm Q) → (antisymm (P ∩ Q))
axiom antisym_int_left : ∀ P Q, (antisymm P) → (antisymm (P ∩ Q))
axiom antisym_int_right : ∀ P Q, (antisymm Q) → (antisymm (P ∩ Q))
axiom trans_int : ∀ P Q, (transit P) → (transit Q) → (transit (P ∩ Q))


-- 10) Difference relation to the properties
axiom diff_binon : ∀ A P Q, (P BinRelOn A) → ((P \ Q) BinRelOn A)
axiom irrefl_diff : ∀ P Q, (irrefl P) → (irrefl (P \ Q))
axiom symm_diff : ∀ P Q, (symm P) → (symm Q) → (symm (P \ Q))
axiom asymm_diff : ∀ P Q, (asymm P) → (asymm (P \ Q))
axiom antisymm_diff : ∀ P Q, (antisymm P) → (antisymm (P \ Q))


-- 11) Complement relation to the properties
axiom compl_binon : ∀ A P, ((comp A A P) BinRelOn A)
axiom symm_compl : ∀ A P, (symm P) → (symm (comp A A P))


-- 12) Strict and non strict partial order definition
def is_strict_partial_order (R A : Set) := (R BinRelOn A) ∧ irrefl R ∧ transit R
syntax term "SPO" term : term
macro_rules
| `($R:term SPO $A:term) => `(is_strict_partial_order $R $A)
def is_nonstrict_partial_order (R A : Set) := (R BinRelOn A) ∧ refl R A ∧ antisymm R ∧ transit R
syntax term "NSPO" term : term
macro_rules
| `($R:term NSPO $A:term) => `(is_nonstrict_partial_order $R $A)


-- 13) Strict partial order is also antisymmetric and asymmetric
axiom spo_antisymm : ∀ A R, (R SPO A) → antisymm R
axiom spo_asymm : ∀ A R, (R SPO A) → asymm R

-- 15) relations between strict and non strict order
noncomputable def str (A R) := R \ (id_ A)
noncomputable def nonstr (A R) := R ∪ (id_ A)
axiom spo_then_nspo : ∀ A R, (R SPO A) → ((nonstr A R) NSPO A)
axiom nspo_then_spo : ∀ A R, (R NSPO A) → ((str A R) SPO A)
axiom str_nonstr_id : ∀ A R, (R SPO A) → ((str A (nonstr A R)) = R)
axiom nonstr_str_id : ∀ A R, (R NSPO A) → ((nonstr A (str A R)) = R)
noncomputable def SPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R SPO A) }
noncomputable def NSPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R NSPO A) }
axiom SPOS_NSPOS_equinum : ∀ A, (SPOS A) ~ (NSPOS A)


-- 16) partial order (strict and non strict) and its equivalent criteria
def is_partial_order (A R₁ R₂ : Set) : Prop := A ≠ ∅ ∧ (R₁ SPO A) ∧ (R₂ = nonstr A R₁)
syntax term "with" term "PO" term  : term
macro_rules
| `($R₁:term with $R₂:term PO $A:term) => `(is_partial_order $A $R₁ $R₂)
axiom part_ord_nspo_crit : ∀ A R₁ R₂, (R₁ with R₂ PO A) ↔ ((A ≠ ∅) ∧ (R₂ NSPO A) ∧ (R₁ = str A R₂))
axiom part_ord_crit :
∀ A R₁ R₂, (R₁ with R₂ PO A) ↔ (A ≠ ∅ ∧ (R₁ SPO A) ∧ (R₂ NSPO A) ∧ (R₂ = nonstr A R₁) ∧ (R₁ = str A R₂))
def is_PO (𝓐 : Set) : Prop := ∃ A R₁ R₂, 𝓐 = ⁅A; R₁; R₂⁆ ∧ (is_partial_order A R₁ R₂)
syntax "PartOrd" term : term
macro_rules
| `(PartOrd $𝓐:term) => `(is_PO $𝓐)
noncomputable def set_PO (𝓐 : Set) := fst_coor (fst_coor 𝓐)
noncomputable def less_PO (𝓐 : Set) := snd_coor (fst_coor 𝓐)
noncomputable def less_eq_PO (𝓐 : Set) := snd_coor 𝓐
syntax "setPO(" term ")" : term
syntax "≺(" term ")" : term
syntax "≼(" term ")" : term
syntax "≽(" term ")" : term
syntax "≻(" term ")" : term
macro_rules
| `(setPO( $𝓐:term )) => `(set_PO $𝓐)
| `(≺($𝓐:term )) => `(less_PO $𝓐)
| `(≼($𝓐:term )) => `(less_eq_PO $𝓐)
| `(≻($𝓐:term )) => `((≺($𝓐))⁻¹)
| `(≽($𝓐:term )) => `((≼($𝓐))⁻¹)

noncomputable def inv_PO (𝓐) := ⁅setPO(𝓐); ≻(𝓐); ≽(𝓐)⁆
syntax "invPO" term : term
macro_rules
| `(invPO $𝓐:term) => `(inv_PO $𝓐)

noncomputable def subs_part_ord (𝓐 X) := ⁅X; ≺(𝓐) spec X; ≼(𝓐) spec X⁆
syntax term "SubsPO" term : term
macro_rules
| `($𝓐 SubsPO $X) => `(subs_part_ord $𝓐 $X)

noncomputable def inter_part_ord (𝓐 𝓑) := ⁅setPO(𝓐); ≺(𝓐) ∩ ≺(𝓑); ≼(𝓐) ∩ ≼(𝓑)⁆
syntax term "InterPO" term : term
macro_rules
| `($𝓐 InterPO $𝓑) => `(inter_part_ord $𝓐 $𝓑)



noncomputable def leq_cart (𝓐 𝓑) := {s ∈ (setPO(𝓐) × setPO(𝓑)) × (setPO(𝓐) × setPO(𝓑)) | ∃ x₁ ∈ setPO(𝓐); ∃ y₁ ∈ setPO(𝓑); ∃ x₂ ∈ setPO(𝓐); ∃ y₂ ∈ setPO(𝓐);
(s = ((x₁, y₁), (x₂, y₂))) ∧ (x₁ . ≼(𝓐) . x₂) ∧ (y₁ . ≼(𝓑) . y₂)}

noncomputable def le_cart (𝓐 𝓑) := str (setPO(𝓐) × setPO(𝓑)) (leq_cart 𝓐 𝓑)

noncomputable def cartesian_part_ord (𝓐 𝓑) := ⁅setPO(𝓐) × setPO(𝓑); le_cart 𝓐 𝓑; leq_cart 𝓐 𝓑⁆
syntax term "CartPO" term : term
macro_rules
| `($𝓐 CartPO $𝓑) => `(cartesian_part_ord $𝓐 $𝓑)




axiom setPO_is_setPO : ∀ A R₁ R₂, (setPO(⁅A; R₁; R₂⁆) = A)
axiom lessPO_is_lessPO :  ∀ A R₁ R₂, (≺(⁅A; R₁; R₂⁆) = R₁)
axiom lesseqPO_is_lesseqPO : ∀ A R₁ R₂, (≼(⁅A; R₁; R₂⁆) = R₂)
axiom triple_po_is_po : ∀ 𝓐, (PartOrd 𝓐) → (is_partial_order setPO(𝓐) ≺(𝓐) ≼(𝓐))
axiom po_is_triple_po : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (PartOrd (⁅A; R₁; R₂⁆))
axiom po_less_more : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≺(𝓐)) . y) ↔ (y . ≻(𝓐) . x)
axiom po_lesseq_moreeq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≼(𝓐)) . y) ↔ (y . ≽(𝓐) . x)
axiom po_emp : ∀ 𝓐, (PartOrd 𝓐) → (setPO(𝓐) ≠ ∅)

-- 17) sub of PO, inverse of a PO, intersection of two PO, cartesian product of two PO
axiom inv_is_PO : ∀ 𝓐, (PartOrd 𝓐) → (PartOrd (invPO 𝓐) )
axiom sub_is_PO : ∀ 𝓐 B, (B ≠ ∅) → (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (PartOrd (𝓐 SubsPO B))
axiom inter_is_PO_PO :
∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (setPO(𝓐) = setPO(𝓑)) → (PartOrd (𝓐 InterPO 𝓑))
axiom inv_PO_less : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≺(invPO 𝓐)) . y) ↔ (y . (≺(𝓐)) . x)
axiom inv_PO_lesseq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≼(invPO 𝓐)) . y) ↔ (y . (≼(𝓐)) . x)
axiom cart_PO_PO : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (PartOrd (𝓐 CartPO 𝓑))


-- 18) partial order pair properties
def noncomparable_nonstr (𝓐 x y : Set) : Prop := (¬ (x . (≼(𝓐)) . y)) ∧ (¬ (x . (≽(𝓐)) . y))
def noncomparable_str (𝓐 x y : Set) : Prop := (¬ (x . (≺(𝓐)) . y)) ∧ (¬ (x . (≻(𝓐)) . y))
axiom part_ord_pair_prop :
∀ 𝓐, (PartOrd 𝓐) → (∀ x y ∈ (setPO(𝓐)); ((x . (≺(𝓐)) . y) ↔ ((x . ≼(𝓐) . y) ∧ x ≠ y)) ∧
((x . (≼(𝓐)) . y) ↔ ((x . (≺(𝓐)) . y) ∨ x = y)))
axiom par_ord_pair_prop_R₁_A : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≺(𝓐)) . y) → ((x ∈ (setPO(𝓐))) ∧ (y ∈ (setPO(𝓐)))))
axiom par_ord_pair_prop_R₂_A : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≼(𝓐)) . y) → ((x ∈ (setPO(𝓐))) ∧ (y ∈ (setPO(𝓐)))))
axiom part_ord_pair_prop_R₁R₂ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . ≺(𝓐) . y) → (x . (≼(𝓐)) . y)
axiom part_ord_pair_prop_R₁neq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y ∈ (setPO(𝓐)); (x . ≺(𝓐) . y) → (x ≠ y)
axiom part_ord_pair_prop_eqR₂ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y ∈ (setPO(𝓐)); (x = y) → (x . (≼(𝓐)) . y)
axiom part_ord_pair_prop_neqR₂R₁ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, ((x . (≼(𝓐)) . y) ∧ (x ≠ y)) → (x . (≺(𝓐)) . y)
axiom irrefl_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x, ¬ (x . (≺(𝓐)) . x))
axiom asymm_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≺(𝓐)) . y) → ¬ (y . (≺(𝓐)) . x))
axiom refl_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x ∈ (setPO(𝓐)); (x . (≼(𝓐)) . x))
axiom antisymm_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . x) → (x = y))
axiom trans_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x . (≼(𝓐)) . z))
axiom stabil_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x = z) → ((x = y) ∧ (y = z)))
axiom no_symm_R₁_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, ¬ ((x . (≺(𝓐)) . y) ∧ (y . (≼(𝓐)) . x)))
axiom PO_noncomp :
∀ 𝓐, (PartOrd 𝓐) → (∀ x y ∈ (setPO(𝓐)); (noncomparable_nonstr 𝓐 x y) ↔ (x ≠ y ∧ (noncomparable_str 𝓐 x y)))



-- 19) (𝒫 A, ⊊, ⊆) is a partial order



noncomputable def sub_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊆ C ∧ z = (B, C) }
noncomputable def subneq_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊊ C ∧ z = (B, C) }
noncomputable def boolean_PO_set (A) := ⁅(𝒫 A); (subneq_binrel A); (sub_binrel A)⁆
syntax "BoolPO" term : term
macro_rules
| `(BoolPO $A:term) => `(boolean_PO_set $A)

axiom NSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (sub_binrel A) ↔ (B ⊆ C)
axiom SNSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (subneq_binrel A) ↔ (B ⊊ C)
axiom boolean_PO : ∀ A, (PartOrd (BoolPO A))


-- 20) maximal (minimal) and maximum (minimim) elements, maximal and minimal sets
def is_maximal (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (x . (≺(𝓐)) . y))
def is_minimal (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (y . (≺(𝓐)) . y))
def is_maximum (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (y . (≼(𝓐)) . x))
def is_minimum (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (x . (≼(𝓐)) . y))


noncomputable def max_set (𝓐 B) := {z ∈ B | is_maximal 𝓐 B z }
noncomputable def min_set (𝓐 B) := {z ∈ B | is_minimal 𝓐 B z }

-- 21) basic properties of maxsets and minsets
axiom max_set_is_max_set : ∀ 𝓐 B x, ((x ∈ max_set 𝓐 B) ↔ (is_maximal 𝓐 B x))
axiom min_set_is_min_set : ∀ 𝓐 B x, ((x ∈ min_set 𝓐 B) ↔ (is_minimal 𝓐 B x))


-- 22) properites of maximal/minimal, maximum/minimum, maxset/minset with respect to inverse
axiom min_max_inv_al : ∀ 𝓐 B x, ((is_minimal 𝓐 B x) ↔ (is_maximal (invPO 𝓐) B x))
axiom max_min_inv_al : ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_maximal 𝓐 B x) ↔ (is_minimal (invPO 𝓐) B x))
axiom min_max_inv_um :  ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_minimum 𝓐 B x) ↔ (is_maximum (invPO 𝓐) B x))
axiom max_min_inv_um :  ∀ 𝓐 B x, ((is_maximum 𝓐 B x) ↔ (is_minimum (invPO 𝓐) B x))
axiom min_max_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (max_set 𝓐 B = min_set (invPO 𝓐) B)
axiom max_min_set_inv : ∀ 𝓐 B, (min_set 𝓐 B = max_set (invPO 𝓐) B)

-- 23) maximal/minimal, maximum/minimum and subset
axiom max_al_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_maximal 𝓐 B x) → (x ∈ C) → (is_maximal 𝓐 C x)
axiom min_al_subsets_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_minimal 𝓐 B x) → (x ∈ C) → (is_minimal 𝓐 C x)
axiom max_um_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_maximum 𝓐 B x) → (x ∈ C) → (is_maximum 𝓐 C x)
axiom min_um_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_minimum 𝓐 B x) → (x ∈ C) → (is_minimum 𝓐 C x)
axiom min_um_sub_cmp : ∀ 𝓐 B C x y, (C ⊆ B) → (is_minimum 𝓐 B x) → (is_minimum 𝓐 C y) → (x . ≼(𝓐) . y)
axiom max_um_sub_cmp : ∀ 𝓐 B C x y, (C ⊆ B) → (is_maximum 𝓐 B x) → (is_maximum 𝓐 C y) → (y . ≼(𝓐) . x)


-- 24) maximal/minimal, maximum/minimum and intersection
axiom max_al_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_maximal 𝓐 (B _ i) x) → (is_maximal 𝓐 (⋂[ i in I ] B at i) x)
axiom min_al_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_minimal 𝓐 (B _ i) x) → (is_minimal 𝓐 (⋂[ i in I ] B at i) x)
axiom max_um_inter_prop :
∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_maximum 𝓐 (B _ i) x) → (is_maximum 𝓐 (⋂[ i in I ] B at i) x)
axiom min_um_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_minimum 𝓐 (B _ i) x) → (is_minimum 𝓐 (⋂[ i in I ] B at i) x)

axiom um_min_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (is_minimum 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_minimum 𝓐 ((B _ i)) y) → (y . ≼(𝓐) . x)
 axiom um_max_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (is_maximum 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_maximum 𝓐 ((B _ i)) y) → (x . ≼(𝓐) . y)


-- 25) maximal/minimal, maximum/minimum and union

axiom max_al_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_maximal 𝓐 (B _ i) x) → (is_maximal 𝓐 (⋃[i in I] B at i) x)
axiom min_al_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_minimal 𝓐 (B _ i) x) → (is_minimal 𝓐 (⋃[i in I] B at i) x)
axiom max_um_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_maximum 𝓐 (B _ i) x) → (is_maximum 𝓐 (⋃[i in I] B at i) x)
axiom min_um_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_minimum 𝓐 (B _ i) x) → (is_minimum 𝓐 (⋃[i in I] B at i) x)



-- 26) maximal/minimal, maximum/minimum properties in PO set
axiom max_um_is_al : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_maximum 𝓐 B x) → (is_maximal 𝓐 B x)
axiom min_um_is_al : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_minimum 𝓐 B x) → (is_minimal 𝓐 B x)
axiom max_um_unique_sub : ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_maximum R₂ B x) → (is_maximum R₂ B y) → (x = y)
axiom min_um_unique_sub : ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_minimum R₂ B x) → (is_minimum R₂ B y) → (x = y)
axiom max_um_maxset_singl : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_maximum 𝓐 B x) → (max_set 𝓐 B = {x})
axiom min_um_minset_singl : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_minimum 𝓐 B x) → (min_set 𝓐 B = {x})



-- 27) upper and lower bounds of a Set and their basic properties
def is_upper_bound (𝓐 B x : Set) := x ∈ setPO(𝓐) ∧ ∀ y ∈ B; (y . (≼(𝓐)) . x)
def is_lower_bound (𝓐 B x : Set) := x ∈ setPO(𝓐) ∧ ∀ y ∈ B; (x . (≼(𝓐)) . y)
noncomputable def lower_bounds (𝓐 B) := {z ∈ setPO(𝓐) | is_lower_bound 𝓐 B z}
noncomputable def upper_bounds (𝓐 B) := {z ∈ setPO(𝓐) | is_upper_bound 𝓐 B z}
syntax term "▴" term : term
syntax term "▾" term : term
macro_rules
| `($𝓐:term ▾ $B:term) => `(lower_bounds $𝓐 $B)
| `($𝓐:term ▴ $B:term) => `(upper_bounds $𝓐 $B)
axiom inv_low_upp_bou : ∀ 𝓐 B x, (is_upper_bound 𝓐 B x) ↔ (is_lower_bound (invPO 𝓐) B x)
axiom inv_upp_low_bou : ∀ 𝓐 B, (PartOrd 𝓐) → ∀ x, (is_lower_bound 𝓐 B x) ↔ (is_upper_bound (invPO 𝓐) B x)
axiom low_bou_set_is_low_bou : ∀ 𝓐 B, ∀ x, (x ∈ (𝓐 ▾ B) ↔ (is_lower_bound 𝓐 B x))
axiom upp_bou_set_is_upp_bou : ∀ 𝓐 B, ∀ x, (x ∈ (𝓐 ▴ B) ↔ (is_upper_bound 𝓐 B x))
axiom low_bou_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 ▾ B) = ((invPO 𝓐) ▴ B)
axiom upp_bou_set_inv :  ∀ 𝓐 B, (𝓐 ▴ B) = ((invPO 𝓐) ▾ B)
axiom max_um_upp_bou : ∀ 𝓐 B x, (B ⊆ (setPO(𝓐))) → (is_maximum 𝓐 B x) → (is_upper_bound 𝓐 B x)
axiom min_um_low_bou : ∀ 𝓐 B x, (B ⊆ (setPO(𝓐))) → (is_minimum 𝓐 B x) → (is_lower_bound 𝓐 B x)
axiom upp_bou_max_um : ∀ 𝓐 B x, (is_upper_bound 𝓐 B x) → (x ∈ B) → (is_maximum 𝓐 B x)
axiom low_bou_min_um : ∀ 𝓐 B x, (is_lower_bound 𝓐 B x) → (x ∈ B) → (is_minimum 𝓐 B x)
axiom upp_bou_subset : ∀ 𝓐 B C x, (B ⊆ C) → (is_upper_bound 𝓐 C x) → (is_upper_bound 𝓐 B x)
axiom low_bou_subset : ∀ 𝓐 B C x, (B ⊆ C) → (is_lower_bound 𝓐 C x) → (is_lower_bound 𝓐 B x)
axiom upp_bou_set_subset : ∀ 𝓐 B C, (B ⊆ C) → (𝓐 ▴ C) ⊆ (𝓐 ▴ B)
axiom low_bou_set_subset : ∀ 𝓐 B C, (B ⊆ C) → (𝓐 ▾ C) ⊆ (𝓐 ▾ B)
axiom sub_upp_low : ∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (B ⊆ (𝓐 ▴ (𝓐 ▾ B)))
axiom sub_low_upp :∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (B ⊆ (𝓐 ▾ (𝓐 ▴ B)))
axiom upp_low_upp_is_low : ∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (𝓐 ▴ (𝓐 ▾ (𝓐 ▴ B))) = (𝓐 ▴ B)
axiom low_upp_low_is_upp : ∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (𝓐 ▾ (𝓐 ▴ (𝓐 ▾ B))) = (𝓐 ▾ B)
axiom upp_bou_inter :
∀ 𝓐 B I x, (B IndxFun I) → (∃ i ∈ I; is_upper_bound 𝓐 (B _ i) x) → (is_upper_bound 𝓐 (⋂[ i in I ] B at i) x)
axiom low_bou_inter :
∀ 𝓐 B I x, (B IndxFun I) → (∃ i ∈ I; is_lower_bound 𝓐 (B _ i) x) → (is_lower_bound 𝓐 (⋂[ i in I ] B at i) x)
axiom upp_bou_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_upper_bound 𝓐 (B _ i) x) → (is_upper_bound 𝓐 (⋃[i in I] B at i) x)
axiom low_bou_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_lower_bound 𝓐 (B _ i) x) → (is_lower_bound 𝓐 (⋃[i in I] B at i) x)


-- 28) supremum and infimum
def is_supremum (𝓐 B x : Set) : Prop := is_minimum 𝓐 (𝓐 ▴ B) x
def is_infimum (𝓐 B x : Set) : Prop := is_maximum 𝓐 (𝓐 ▾ B) x
axiom sup_is_upp : ∀ 𝓐 B x, is_supremum 𝓐 B x → (is_upper_bound 𝓐 B x)
axiom inf_is_low : ∀ 𝓐 B x, is_infimum 𝓐 B x → (is_lower_bound 𝓐 B x)
axiom sup_is_sm_upp : ∀ 𝓐 B x, is_supremum 𝓐 B x → (∀ y, (is_upper_bound 𝓐 B y) → (x . (≼(𝓐)) . y))
axiom inf_is_big_low : ∀ 𝓐 B x, is_infimum 𝓐 B x → (∀ y, (is_lower_bound 𝓐 B y) → (x . (≽(𝓐)) . y))
axiom upp_and_sm_upp_sup :
∀ 𝓐 B x, (is_upper_bound 𝓐 B x) → (∀ y, (is_upper_bound 𝓐 B y) → (x . (≼(𝓐)) . y)) → (is_supremum 𝓐 B x)
axiom low_and_big_low_inf :
∀ 𝓐 B x, (is_lower_bound 𝓐 B x) → (∀ y, (is_lower_bound 𝓐 B y) → (x . (≽(𝓐)) . y)) → (is_infimum 𝓐 B x)
axiom sup_uni : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_supremum 𝓐 B x) → (is_supremum 𝓐 B y) → (x = y)
axiom inf_uni : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_infimum 𝓐 B x) → (is_infimum 𝓐 B y) → (x = y)
axiom inv_is_sup_inf : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_supremum 𝓐 B x) ↔ (is_infimum (invPO 𝓐) B x))
axiom inv_is_inf_sup : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_infimum 𝓐 B x) ↔ (is_supremum (invPO 𝓐) B x))
axiom max_um_is_sup : ∀ 𝓐 B x, (PartOrd 𝓐) → (B ⊆ setPO(𝓐)) → (is_maximum 𝓐 B x) → (is_supremum 𝓐 B x)
axiom min_um_is_inf :∀ 𝓐 B x, (PartOrd 𝓐) → (B ⊆ setPO(𝓐)) → (is_minimum 𝓐 B x) → (is_infimum 𝓐 B x)
axiom sup_subset : ∀ 𝓐 B C x y, (PartOrd 𝓐) → (B ⊆ C) → (is_supremum 𝓐 C x) → (is_supremum 𝓐 B y) → (¬ (x . (≺(𝓐)) . y))
axiom inf_subset : ∀ 𝓐 B C x y, (PartOrd 𝓐) → (B ⊆ C) → (is_infimum 𝓐 C x) → (is_infimum 𝓐 B y) → (¬ (x . (≻(𝓐)) . y))
axiom sup_union :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_supremum 𝓐 (B _ i) x) → (is_supremum 𝓐 (⋃[i in I] B at i) x)
axiom inf_union :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_infimum 𝓐 (B _ i) x) → (is_infimum 𝓐 (⋃[i in I] B at i) x)


-- 29) minimum, maximum, supremum and infimum existence properties
def maximum_exists (𝓐 B : Set) : Prop := ∃ x, is_maximum 𝓐 B x
def minimum_exists (𝓐 B : Set) : Prop := ∃ x, is_minimum 𝓐 B x
def supremum_exists (𝓐 B : Set) : Prop := ∃ x, is_supremum 𝓐 B x
def infimum_exists (𝓐 B : Set) : Prop := ∃ x, is_infimum 𝓐 B x
syntax term "MaxExi" term : term
syntax term "MinExi" term : term
syntax term "SuprExi" term : term
syntax term "InfmExi" term : term
macro_rules
| `($𝓐:term MaxExi $B:term) => `(maximum_exists $𝓐 $B)
| `($𝓐:term MinExi $B:term) => `(minimum_exists $𝓐 $B)
| `($𝓐:term SuprExi $B:term) => `(supremum_exists $𝓐 $B)
| `($𝓐:term InfmExi $B:term) => `(infimum_exists $𝓐 $B)


axiom partmin_um_un_prop : ∀ 𝓐 B I x, (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_minimum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_minimum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimum 𝓐 (B _ i) y} x))
axiom partmax_um_un_prop : ∀ 𝓐 B I x, (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_maximum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_maximum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximum 𝓐 (B _ i) y} x))


-- 30) minimum, maximum, supremum and infimum as an element and their main properties
noncomputable def maximum (𝓐 B) := ⋃ {b ∈ B | is_maximum 𝓐 B b}
noncomputable def minimum (𝓐 B) := ⋃ {b ∈ B | is_minimum 𝓐 B b}
noncomputable def supremum (𝓐 B) := ⋃ {a ∈ setPO(𝓐) | is_supremum 𝓐 B a}
noncomputable def infimum (𝓐 B) := ⋃ {a ∈ setPO(𝓐) | is_infimum 𝓐 B a}
syntax term "Max" term : term
syntax term "Min" term : term
syntax term "Supr" term : term
syntax term "Infm" term : term
macro_rules
| `($𝓐:term Max $B:term) => `(maximum $𝓐 $B)
| `($𝓐:term Min $B:term) => `(minimum $𝓐 $B)
| `($𝓐:term Supr $B:term) => `(supremum $𝓐 $B)
| `($𝓐:term Infm $B:term) => `(infimum $𝓐 $B)

axiom max_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MaxExi B) → (is_maximum 𝓐 B (𝓐 Max B))
axiom min_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MinExi B) → (is_minimum 𝓐 B (𝓐 Min B))
axiom supr_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 SuprExi B) → (is_supremum 𝓐 B (𝓐 Supr B))
axiom inf_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 InfmExi B) → (is_infimum 𝓐 B (𝓐 Infm B))
axiom max_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 MaxExi B) → ((is_maximum 𝓐 B x) ↔ (x = 𝓐 Max B))
axiom min_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 MinExi B) → ((is_minimum 𝓐 B x) ↔ (x = 𝓐 Min B))
axiom supr_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 SuprExi B) → ((is_supremum 𝓐 B x) ↔ (x = 𝓐 Supr B))
axiom infm_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 InfmExi B) → ((is_infimum 𝓐 B x) ↔ (x = 𝓐 Infm B))

axiom sup_is_max :  ∀ 𝓐 B, (B ⊆ setPO(𝓐)) → (PartOrd 𝓐) → (𝓐 MaxExi B) → (𝓐 SuprExi B) ∧ ((𝓐 Supr B) = 𝓐 Max B)
axiom inf_is_min : ∀ 𝓐 B, (B ⊆ setPO(𝓐)) → (PartOrd 𝓐) → (𝓐 MinExi B) → (𝓐 InfmExi B) ∧ ((𝓐 Infm B) = 𝓐 Min B)
axiom max_min_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MaxExi B) → (((invPO 𝓐) MinExi B) ∧ ((𝓐 Max B) = (invPO(𝓐)) Min B))
axiom min_max_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MinExi B) → (((invPO 𝓐) MaxExi B) ∧ ((𝓐 Min B) = (invPO(𝓐)) Max B))
axiom max_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MaxExi B) → (((𝓐 Max B) ∈ C) ↔ ((𝓐 MaxExi C) ∧ ((𝓐 Max C) = 𝓐 Max B)))
axiom min_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MinExi B) → (((𝓐 Min B) ∈ C) ↔ ((𝓐 MinExi C) ∧ ((𝓐 Min C) = 𝓐 Min B)))
axiom max_inter_prop :
∀ 𝓐 B I i, i ∈ I → (PartOrd 𝓐) → (B IndxFun I) → ((𝓐 Max (B _ i)) ∈ (⋂[ i in I ] B at i)) →
(𝓐 MaxExi (B _ i)) → ((𝓐 MaxExi (⋂[ i in I ] B at i)) ∧ ((𝓐 Max (⋂[ i in I ] B at i)) = 𝓐 Max (B _ i)))
axiom min_inter_prop :
∀ 𝓐 B I i, i ∈ I → (PartOrd 𝓐) → (B IndxFun I) → ((𝓐 Min (B _ i)) ∈ (⋂[ i in I ] B at i)) →
(𝓐 MinExi (B _ i)) → ((𝓐 MinExi (⋂[ i in I ] B at i)) ∧ ((𝓐 Min (⋂[ i in I ] B at i)) = 𝓐 Min (B _ i)))
axiom max_un_prop :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) →
(∀ i j ∈ I; (𝓐 Max (B _ i)) = (𝓐 Max (B _ j))) → ((𝓐 MaxExi (⋃[ i in I ] B at i)) ∧
(∀ s ∈ I; (𝓐 Max ((⋃[ i in I ] B at i))) = (𝓐 Max (B _ s))))
axiom min_un_prop :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) →
(∀ i j ∈ I; (𝓐 Min (B _ i)) = (𝓐 Min (B _ j))) → ((𝓐 MinExi (⋃[ i in I ] B at i)) ∧
(∀ s ∈ I; (𝓐 Min ((⋃[ i in I ] B at i))) = (𝓐 Min (B _ s))))

axiom supr_subset : ∀ 𝓐 B C, (PartOrd 𝓐) →
 (B ⊆ C) → (𝓐 SuprExi C) → (𝓐 SuprExi B) → (¬ ((𝓐 Supr C) . (≺(𝓐)) . (𝓐 Supr B)))

axiom infm_subset : ∀ 𝓐 B C, (PartOrd 𝓐) → (B ⊆ C) → (𝓐 InfmExi C) → (𝓐 InfmExi B)
→ (¬ ((𝓐 Infm B) . (≺(𝓐)) . (𝓐 Infm C)))

axiom supr_union :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; 𝓐 SuprExi (B _ i))
→ (∀ i j ∈ I; (𝓐 Supr (B _ i)) = (𝓐 Supr (B _ j))) →
((𝓐 SuprExi (⋃[i in I] B at i)) ∧
(∀ s ∈ I; (𝓐 Supr (⋃[i in I] B at i)) = (𝓐 Supr (B _ s))))

axiom infm_union :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; 𝓐 InfmExi (B _ i))
→ (∀ i j ∈ I; (𝓐 Infm (B _ i)) = (𝓐 Infm (B _ j))) →
((𝓐 InfmExi (⋃[i in I] B at i)) ∧
(∀ s ∈ I; (𝓐 Infm (⋃[i in I] B at i)) = (𝓐 Infm (B _ s))))


-- 31) Intervals and some of their obvious properties

noncomputable def lro_intl (𝓐 a b) := {x ∈ setPO(𝓐) | (a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b) }
noncomputable def lcro_intl (𝓐 a b) := {x ∈ setPO(𝓐) | (a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b) }
noncomputable def lorc_intl (𝓐 a b) := {x ∈ setPO(𝓐) | (a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b) }
noncomputable def lrc_intl (𝓐 a b) := {x ∈ setPO(𝓐) | (a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b) }
noncomputable def lc_intl (𝓐 a) := {x ∈ setPO(𝓐) | (a . (≼(𝓐)) . x) }
noncomputable def rc_intl (𝓐 b) := {x ∈ setPO(𝓐) | (x . (≼(𝓐)) . b) }
noncomputable def lo_intl (𝓐 a) := {x ∈ setPO(𝓐) | (a . (≺(𝓐)) . x) }
noncomputable def ro_intl (𝓐 b) := {x ∈ setPO(𝓐) | (x . (≺(𝓐)) . b) }
noncomputable def f_intl (𝓐) := setPO(𝓐)
syntax "⦗" term ";" term "⦘" "of" term : term
syntax "⟦" term ";" term "⦘" "of" term : term
syntax "⦗" term ";" term "⟧" "of" term : term
syntax "⟦" term ";" term "⟧" "of" term : term
syntax "⟦" term ";" "+" "∞" "⦘" "of" term : term
syntax "⦗" "-" "∞" ";" term "⟧" "of" term : term
syntax "⦗" term ";" "+" "∞" "⦘" "of" term : term
syntax "⦗" "-" "∞" ";" term "⦘" "of" term : term
syntax "⦗" "-" "∞" ";"  "+" "∞" "⦘" "of" term : term
macro_rules
| `( ⦗ $a:term ; $b:term ⦘ of $𝓐:term) => `(lro_intl $𝓐 $a $b)
| `( ⟦ $a:term ; $b:term ⦘ of $𝓐:term) => `(lcro_intl $𝓐 $a $b)
| `( ⦗ $a:term ; $b:term ⟧ of $𝓐:term) => `(lorc_intl $𝓐 $a $b)
| `( ⟦ $a:term ; $b:term ⟧ of $𝓐:term) => `(lrc_intl $𝓐 $a $b)
| `(⟦ $a:term ; +∞ ⦘  of $𝓐:term) => `(lc_intl $𝓐 $a)
| `( ⦗ -∞; $b:term ⟧ of $𝓐:term) => `(rc_intl $𝓐 $b)
| `(⦗ $a:term ; +∞⦘ of $𝓐:term) => `(lo_intl $𝓐 $a)
| `(⦗-∞; $b:term ⦘ of $𝓐:term) => `(ro_intl $𝓐 $b)
| `(⦗ -∞; +∞ ⦘ of $𝓐:term) => `(f_intl $𝓐)

axiom lro_sub_all : ∀ 𝓐 a b, ( ⦗ a ; b ⦘ of 𝓐 ) ⊆ setPO(𝓐)
axiom lcro_sub_all : ∀ 𝓐 a b, ( ⟦ a ; b ⦘ of 𝓐) ⊆ setPO(𝓐)
axiom lorc_sub_all : ∀ 𝓐 a b, ( ⦗ a ; b ⟧ of 𝓐) ⊆ setPO(𝓐)
axiom lrc_sub_all : ∀ 𝓐 a b, ( ⟦ a ; b ⟧ of 𝓐) ⊆ setPO(𝓐)
axiom lc_sub_all : ∀ 𝓐 a, ( ⟦ a ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐)
axiom rc_sub_all : ∀ 𝓐 b, ( ⦗ -∞ ; b ⟧ of 𝓐) ⊆ setPO(𝓐)
axiom lo_sub_all : ∀ 𝓐 a, ( ⦗ a ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐)
axiom ro_sub_all : ∀ 𝓐 b, ( ⦗ -∞ ; b ⦘ of 𝓐) ⊆ setPO(𝓐)
axiom f_sub_all :  ∀ 𝓐, (⦗ -∞ ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐)
axiom f_eq_all : ∀ 𝓐, (⦗ -∞ ; +∞  ⦘ of 𝓐) = setPO(𝓐)

axiom lro_is_lro : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; b ⦘ of 𝓐) ↔ ((a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b))
axiom lcro_is_lcro : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; b ⦘ of 𝓐) ↔ ((a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b))
axiom locr_is_locr : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; b ⟧ of 𝓐) ↔ ((a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b))
axiom lrc_is_lrc : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; b ⟧ of 𝓐) ↔ ((a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b))
axiom lc_is_lc : ∀ 𝓐 a, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; +∞ ⦘ of 𝓐) ↔ (a . (≼(𝓐)) . x)
axiom rc_is_rc : ∀ 𝓐 b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; b ⟧ of 𝓐) ↔ (x . (≼(𝓐)) . b)
axiom lo_is_lo : ∀ 𝓐 a, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; +∞ ⦘ of 𝓐) ↔ (a . (≺(𝓐)) . x)
axiom ro_is_ro : ∀ 𝓐 b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; b ⦘ of 𝓐) ↔ (x . (≺(𝓐)) . b)
axiom full_is_full : ∀ 𝓐, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; +∞ ⦘ of 𝓐)

axiom lrc_nemp : ∀ 𝓐, ∀ a ∈ setPO(𝓐); ∀ b, (PartOrd 𝓐) → ((⟦ a ; b ⟧ of 𝓐) ≠ ∅ ↔ (a . ≼(𝓐) . b))
axiom lrc_min : ∀ 𝓐, ∀ a ∈ setPO(𝓐); ∀ b, (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_minimum 𝓐 (⟦ a ; b ⟧ of 𝓐) a)
axiom lrc_max : ∀ 𝓐 a, ∀ b ∈ setPO(𝓐); (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_maximum 𝓐 (⟦ a ; b ⟧ of 𝓐) b)


-- 32) lattice, complete lattice, monotonic functions on relation, fix point sets and their properties
def is_lattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ x y ∈ (setPO(𝓐)); (𝓐 SuprExi ({x, y})) ∧ (𝓐 InfmExi ({x, y})))
syntax "Latt" term : term
macro_rules
| `(Latt $𝓐:term) => `(is_lattice $𝓐)
def is_complete_lattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ X, (X ⊆ setPO(𝓐)) → (𝓐 SuprExi X))
syntax "CompLatt" term : term
macro_rules
| `(CompLatt $𝓐) => `(is_complete_lattice $𝓐)
def monotonic_func_rel (𝓐 f : Set) : Prop := (f Fun setPO(𝓐) To setPO(𝓐)) ∧ (
  ∀ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) → ((f⦅x⦆) . (≼(𝓐)) . (f⦅y⦆))
)
syntax term "MotFunRelOn" term : term
macro_rules
| `($f MotFunRelOn $𝓐) => `(monotonic_func_rel $𝓐 $f)

noncomputable def fix_point_set (𝓐 f) := {x ∈ setPO(𝓐) | f⦅x⦆ = x}
syntax term "FixOn" term : term
macro_rules
| `($f:term FixOn $𝓐) => `(fix_point_set $𝓐 $f)

axiom boolean_Latt : ∀ A, (Latt (BoolPO A))
axiom compl_latt_inf_crit : ∀ 𝓐, (CompLatt 𝓐) ↔ (∀ X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X))
axiom compl_latt_is_latt : ∀ 𝓐, (CompLatt 𝓐) → (Latt 𝓐)
axiom boolean_CompLatt : ∀ A, (CompLatt (BoolPO A))
axiom Knaster_Tarski_lemma₀ : ∀ 𝓐, ∀ a b ∈ setPO(𝓐); (a . ≼(𝓐) . b) → (CompLatt 𝓐) → (CompLatt (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)))
axiom Knaster_Tarski_lemma₁ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (𝓐 MaxExi (f FixOn 𝓐))
axiom Knaster_Tarski_lemma₂ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → ((f FixOn 𝓐) ≠ ∅)
axiom Knaster_Tarski_axiom : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (CompLatt (𝓐 SubsPO (f FixOn 𝓐)))


-- 33) linear order and it's main properties
def is_linear_order (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧ (str_conn (≼(𝓐)) setPO(𝓐))
syntax "LinOrd" term : term
macro_rules
| `(LinOrd $𝓐) => `(is_linear_order $𝓐)


axiom inv_is_LO : ∀ 𝓐, (LinOrd 𝓐) → (LinOrd (invPO 𝓐))
axiom sub_is_LO : ∀ 𝓐 B, (B ≠ ∅) → (LinOrd 𝓐) → (B ⊆ setPO(𝓐)) → (LinOrd (𝓐 SubsPO B))


axiom lin_ord_prop : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∨ (y . (≼(𝓐)) . x))
axiom lin_ord_wk_prop : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (x ≠ y) → ((x . ≺(𝓐) . y) ∨ (y . (≺(𝓐)) . x)))
axiom lin_ord_nR₁ : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (¬ (x . (≺(𝓐)) . y)) → (y . (≼(𝓐)) . x))
axiom lin_ord_nR₂ : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (¬ (x . (≼(𝓐)) . y)) → (y . (≺(𝓐)) . x))


axiom linmin_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_minimal 𝓐 X x) ↔ (is_minimum 𝓐 X x))
axiom linmax_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_maximal 𝓐 X x) ↔ (is_maximum 𝓐 X x))

axiom linmin_al_sub_cmp : ∀ 𝓐 B C x y, (LinOrd 𝓐) →
(C ⊆ B) → (B ⊆ setPO(𝓐)) → (is_minimal 𝓐 B x) → (is_minimal 𝓐 C y) → (x . ≼(𝓐) . y)
axiom linmax_al_sub_cmp : ∀ 𝓐 B C x y, (LinOrd 𝓐) →
(C ⊆ B) → (B ⊆ setPO(𝓐)) → (is_maximal 𝓐 B x) → (is_maximal 𝓐 C y) → (y . ≼(𝓐) . x)
axiom lin_al_min_inter_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))
→ (B IndxFun I) → (is_minimal 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_minimal 𝓐 ((B _ i)) y) → (y . ≼(𝓐) . x)
axiom lin_al_max_inter_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B IndxFun I) → (is_maximal 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_maximal 𝓐 ((B _ i)) y) → (x . ≼(𝓐) . y)
axiom lin_partmin_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_minimal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_minimal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimal 𝓐 (B _ i) y} x))
axiom lin_partmax_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_maximal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_maximal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximal 𝓐 (B _ i) y} x))

axiom linsup_al : ∀ 𝓐 B x, (LinOrd 𝓐) → ((is_supremum 𝓐 B x) ↔ (is_minimal 𝓐 (𝓐 ▴ B) x))
axiom lininf_al : ∀ 𝓐 B x, (LinOrd 𝓐) → ((is_infimum 𝓐 B x) ↔ (is_maximal 𝓐 (𝓐 ▾ B) x))

axiom lin_supr_subset : ∀ 𝓐 B C, (LinOrd 𝓐) →
 (B ⊆ C) → (𝓐 SuprExi C) → (𝓐 SuprExi B) → (((𝓐 Supr B) . (≼(𝓐)) . (𝓐 Supr C)))
axiom lin_infm_subset : ∀ 𝓐 B C, (LinOrd 𝓐) →
 (B ⊆ C) → (𝓐 InfmExi C) → (𝓐 InfmExi B) → (((𝓐 Infm C) . (≼(𝓐)) . (𝓐 Infm B)))


axiom linsup_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 SuprExi (B _ i)))
 → ((is_supremum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_supremum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_supremum 𝓐 (B _ i) y} x))

axiom lininf_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 InfmExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_infimum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_infimum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_infimum 𝓐 (B _ i) y} x))


axiom lin_latt : ∀ 𝓐, (LinOrd 𝓐) → (Latt 𝓐)


-- 34) Well ordered set definition


def is_well_order 𝓐 := (LinOrd 𝓐) ∧ ∀ X, (X ⊆ setPO(𝓐)) →  (X ≠ ∅) → (𝓐 MinExi X)
syntax "WellOrd" term : term
macro_rules
| `(WellOrd $𝓐) => `(is_well_order $𝓐)


-- 35) chain and anti chain and some of their properties

def is_chain (𝓐 B) := (PartOrd 𝓐) ∧ (B ⊆ setPO(𝓐)) ∧ (LinOrd (𝓐 SubsPO B))
syntax term "Chain" term : term
macro_rules
| `($𝓐 Chain $B) => `(is_chain $𝓐 $B)

def anti_chain (𝓐 B) := (PartOrd 𝓐) ∧ (B ⊆ setPO(𝓐)) ∧ (∀ x y ∈ B; noncomparable_str 𝓐 x y)
syntax term "AntiChain" term : term
macro_rules
| `($𝓐 AntiChain $B) => `(anti_chain $𝓐 $B)

axiom lin_chain : ∀ 𝓐 B, (B ≠ ∅) → (B ⊆ setPO(𝓐)) → (LinOrd 𝓐) → (𝓐 Chain B)
axiom antichain : ∀ 𝓐 𝓑 A B, (𝓐 AntiChain A) → (𝓑 AntiChain B) → ((𝓐 CartPO 𝓑) AntiChain (A × B))


-- 36) Order isomorphism


def ispo_iso (𝓐 𝓑 f : Set) := (f Bij setPO(𝓐) To setPO(𝓑)) ∧ (∀ x y ∈ setPO(𝓐); (x . ≼(𝓐) . y) ↔ ((f⦅x⦆) . (≼(𝓑)) . (f⦅y⦆)))
syntax term "PO_ISO" term "To" term : term
macro_rules
| `($f PO_ISO $𝓐 To $𝓑) => `(ispo_iso $𝓐 $𝓑 $f)

def ispo_iso_po (𝓐 𝓑 f : Set) := (PartOrd 𝓐) ∧ (PartOrd 𝓑) ∧ (f PO_ISO 𝓐 To 𝓑)
syntax term "PO_ISO_PO" term "To" term : term
macro_rules
| `($f PO_ISO_PO $𝓐 To $𝓑) => `(ispo_iso_po $𝓐 $𝓑 $f)


def pos_iso (𝓐 𝓑 : Set) := ∃ f, (f PO_ISO 𝓐 To 𝓑)
syntax term "≃O" term : term
macro_rules
| `($𝓐 ≃O $𝓑) => `(pos_iso $𝓐 $𝓑)


def pos_iso_po (𝓐 𝓑 : Set) := (PartOrd 𝓐) ∧ (PartOrd 𝓑) ∧ (𝓐 ≃O 𝓑)
syntax term "P≃O" term : term
macro_rules
| `($𝓐 P≃O $𝓑) => `(pos_iso_po $𝓐 $𝓑)

--- 37) Main properties: reflexivity, symmetry, transitivity, equinumerosity of sets


axiom iso_equin : ∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (setPO(𝓐) ~ setPO(𝓑))
axiom iso_refl : ∀ 𝓐, (𝓐 ≃O 𝓐)
axiom iso_symm : ∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (𝓑 ≃O 𝓐)
axiom iso_trans : ∀ 𝓐 𝓑 𝓒, (𝓐 ≃O 𝓑) → (𝓑 ≃O 𝓒) → (𝓐 ≃O 𝓒)


-- 38) Simple properties that doesn't change through isomorphism in different partial ordered set

axiom iso_in₀ : ∀ 𝓐 𝓑 f x, (f PO_ISO 𝓐 To 𝓑) → (x ∈ setPO(𝓐)) → ((f⦅x⦆)) ∈ setPO(𝓑)
axiom iso_in₁ : ∀ 𝓐 𝓑 f x, (f PO_ISO 𝓐 To 𝓑) → (x ∈ setPO(𝓐)) → ((x ∈ setPO(𝓐)) ↔ ((f⦅x⦆)) ∈ setPO(𝓑))
axiom iso_in₂ : ∀ 𝓐 𝓑 T f x, (x ∈ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → ((x ∈ T) ↔ (f⦅x⦆) ∈ f.[T])

axiom iso_R₂ : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → ∀ x y ∈ setPO(𝓐); (x . ≼(𝓐) . y) ↔ ((f⦅x⦆) . (≼(𝓑)) . (f⦅y⦆))
axiom iso_eq : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → ∀ x y ∈ setPO(𝓐); (x = y) ↔ ((f⦅x⦆) = (f⦅y⦆))
axiom iso_R₁ : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (PartOrd 𝓐) → (PartOrd 𝓑) → (∀ x y ∈ setPO(𝓐); (x . ≺(𝓐) . y) ↔ ((f⦅x⦆) . (≺(𝓑)) . (f⦅y⦆)))


-- 39) Logical properties that doesn't change through isomorphism in different partial ordered set


axiom poiso_not_equiv (φ₁ φ₂ : Set → Prop) : ∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((¬(φ₁ x)) ↔ (¬φ₂ (f⦅x⦆)))
axiom poiso_and_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ∧ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ∧ (φ₄ (f⦅x⦆))))
axiom poiso_or_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ∨ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ∨ (φ₄ (f⦅x⦆))))
axiom poiso_if_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) → ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) → (φ₄ (f⦅x⦆))))
axiom poiso_iff_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ↔ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ↔ (φ₄ (f⦅x⦆))))


axiom poiso_all_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ X; ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∀ x ∈ X; (φ₁ x)) ↔ (∀ x ∈ f.[X]; (φ₂ x)))

axiom poiso_exi_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ X; ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∃ x ∈ X; (φ₁ x)) ↔ (∃ x ∈ f.[X]; (φ₂ x)))


axiom poiso_allin_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ setPO(𝓐); ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∀ x ∈ setPO(𝓐); (φ₁ x)) ↔ (∀ x ∈ setPO(𝓑); (φ₂ x)))

axiom posio_exiin_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ setPO(𝓐); ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∃ x ∈ setPO(𝓐); (φ₁ x)) ↔ (∃ x ∈ setPO(𝓑); (φ₂ x)))


-- 40) Using the above axioms about isomorphism for particular properties

axiom poiso_minal : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_minimal 𝓐 X x) ↔ (is_minimal 𝓑 (f.[X]) (f⦅x⦆)))
axiom poiso_maxal : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_maximal 𝓐 X x) ↔ (is_maximal 𝓑 (f.[X]) (f⦅x⦆)))
axiom poiso_minum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_minimum 𝓐 X x) ↔ (is_minimum 𝓑 (f.[X]) (f⦅x⦆)))
axiom poiso_maxum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_maximum 𝓐 X x) ↔ (is_maximum 𝓑 (f.[X]) (f⦅x⦆)))
axiom poiso_lowbou : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_lower_bound 𝓐 X x) ↔ (is_lower_bound 𝓑 (f.[X]) (f⦅x⦆)) )
axiom poiso_uppbou : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_upper_bound 𝓐 X x) ↔ (is_upper_bound 𝓑 (f.[X]) (f⦅x⦆)) )
axiom poiso_minexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 MinExi X) ↔ (𝓑 MinExi f.[X]))
axiom poiso_maxexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 MaxExi X) ↔ (𝓑 MaxExi f.[X]))


-- 41) axioms about equal subsets because of isomorphism and its application for particular subsets

axiom poiso_subs_eq (φ : Set → Set → Set → Prop) (ψ : Set → Set → Set) : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 X x, (x ∈ ψ 𝓧 X ↔ φ 𝓧 X x)) →
(∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (ψ 𝓧 X) ⊆ setPO(𝓧)) → (∀ X, (∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆)))) →
(f.[ψ 𝓐 X] = ψ 𝓑 (f.[X])))

axiom poiso_interv_eq (c d : Set) (φ : Set → Set → Set → Set → Prop) (ψ : Set → Set → Set → Set)
 : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 x, ∀ a b, (x ∈ ψ 𝓧 a b ↔ φ 𝓧 a b x)) →
 (∀ 𝓧 a b, (ψ 𝓧 a b) ⊆ setPO(𝓧)) → ((∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 c d x) ↔ (φ 𝓑 (f⦅c⦆) (f⦅d⦆) (f⦅x⦆)))) → (
  f.[ψ 𝓐 c d] = ψ 𝓑 (f⦅c⦆) (f⦅d⦆)
 ))



 axiom poiso_interv_eq₂ (c : Set) (φ : Set → Set → Set → Prop) (ψ : Set → Set → Set)
 : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 x, ∀ a, (x ∈ ψ 𝓧 a ↔ φ 𝓧 a x)) →
 (∀ 𝓧 a, (ψ 𝓧 a) ⊆ setPO(𝓧)) → ((∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 c x) ↔ (φ 𝓑 (f⦅c⦆) (f⦅x⦆)))) → (
  f.[ψ 𝓐 c] = ψ 𝓑 (f⦅c⦆)
 ))

axiom poiso_minset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[min_set 𝓐 X] = min_set 𝓑 (f.[X]))
axiom poiso_maxset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[max_set 𝓐 X] = max_set 𝓑 (f.[X]))
axiom poiso_lowset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[𝓐 ▾ X] = 𝓑 ▾ (f.[X]))
axiom poiso_uppset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[𝓐 ▴ X] = 𝓑 ▴ (f.[X]))
axiom poiso_sup : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_supremum 𝓐 X x) ↔ (is_supremum 𝓑 (f.[X]) (f⦅x⦆)))
axiom poiso_inf : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_infimum 𝓐 X x) ↔ (is_infimum 𝓑 (f.[X]) (f⦅x⦆)))
axiom poiso_supexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 SuprExi X) ↔ (𝓑 SuprExi (f.[X])))
axiom poiso_infexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 InfmExi X) ↔ (𝓑 InfmExi (f.[X])))



axiom poiso_lro : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐))
 → (f.[⦗ a ; b ⦘ of 𝓐] = ⦗ f⦅a⦆ ; f⦅b⦆ ⦘ of 𝓑)
axiom poiso_lcro : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐))
→ (f.[⟦ a ; b ⦘ of 𝓐] = ⟦ f⦅a⦆ ; f⦅b⦆ ⦘ of 𝓑)
axiom poiso_locr : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐))
→ (f.[⦗ a ; b ⟧ of 𝓐] = ⦗ f⦅a⦆ ; f⦅b⦆ ⟧ of 𝓑)
axiom poiso_lrc : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐))
→ (f.[⟦ a ; b ⟧ of 𝓐] = ⟦ f⦅a⦆ ; f⦅b⦆ ⟧ of 𝓑)
axiom poiso_lc : ∀ 𝓐 𝓑 f a, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (f.[⟦ a ; +∞ ⦘ of 𝓐] = ⟦ f⦅a⦆ ; +∞ ⦘ of 𝓑)
axiom poiso_rc : ∀ 𝓐 𝓑 f b, (f PO_ISO_PO 𝓐 To 𝓑) → (b ∈ setPO(𝓐)) → (f.[ ⦗ -∞ ; b ⟧ of 𝓐] = ⦗  -∞  ; f⦅b⦆ ⟧ of 𝓑)
axiom poiso_lo : ∀ 𝓐 𝓑 f a, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (f.[ ⦗  a ; +∞ ⦘ of 𝓐] = ⦗ f⦅a⦆ ; +∞ ⦘ of 𝓑)
axiom poiso_ro : ∀ 𝓐 𝓑 f b, (f PO_ISO_PO 𝓐 To 𝓑) → (b ∈ setPO(𝓐)) → (f.[⦗ -∞ ; b ⦘ of 𝓐] = ⦗ -∞ ; f⦅b⦆ ⦘ of 𝓑)
axiom poiso_full : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (f.[⦗ -∞ ; +∞  ⦘ of 𝓐] = ⦗ -∞ ; +∞  ⦘ of 𝓑)



-- 42) axiom about equal element constructions because of isomorphism and its applications

axiom poiso_elconstr  (φ : Set → Set → Set → Prop ) (ψ : Set → Set → Set) (cond : Set → Set → Prop)  :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (cond 𝓐 X) → (cond 𝓑 (f.[X])) → (f PO_ISO_PO 𝓐 To 𝓑) →
(∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (PartOrd 𝓧) → (cond 𝓧 X) → ψ 𝓧 X ∈ setPO(𝓧)) →
(∀ 𝓧 X t, (PartOrd 𝓧) → (cond 𝓧 X) →  ((φ 𝓧 X (t) ↔ (t = ψ 𝓧 X)))) →
(∀ X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆)))) →
(f⦅ψ 𝓐 X⦆ = ψ 𝓑 (f.[X]))



axiom poiso_minumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 MinExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Min X⦆ = 𝓑 Min (f.[X]))
axiom poiso_maxumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 MaxExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Max X⦆ = 𝓑 Max (f.[X]))
axiom poiso_supel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 SuprExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Supr X⦆ = 𝓑 Supr (f.[X]))
axiom poiso_infel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Infm X⦆ = 𝓑 Infm (f.[X]))


-- 43 ) Properties about partial order itself also doesn't change through isomorphism


axiom poiso_if_then_iff (φ : Set → Prop) :
(∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → (φ 𝓐) → (φ 𝓑)) → (∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((φ 𝓐) ↔ (φ 𝓑)))

axiom poiso_subset_prop (φ : Set → Set → Prop) :
(∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X) ↔ (φ 𝓑 (f.[X])))) →
(∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((∀ X, (X ⊆ setPO(𝓐)) → (φ 𝓐 X)) ↔ (∀ X, (X ⊆ setPO(𝓑)) → (φ 𝓑 X))))

axiom poiso_latt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((Latt 𝓐) ↔ (Latt 𝓑))
axiom poiso_complatt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((CompLatt 𝓐) ↔ (CompLatt 𝓑))
axiom poiso_linord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((LinOrd 𝓐) ↔ (LinOrd 𝓑))
axiom poiso_welord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((WellOrd 𝓐) ↔ (WellOrd 𝓑))


-- 44) Partial order isomorphism translates through different partial order constructions

axiom poiso_inv : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((inv_PO 𝓐) P≃O (inv_PO 𝓑))
axiom poiso_subs : ∀ 𝓐 𝓑 f X, (X ≠ ∅) → (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 SubsPO X) P≃O (𝓑 SubsPO (f.[X])))
axiom poiso_inter : ∀ 𝓐 𝓑 𝓒 𝓓 f, (setPO(𝓐) = setPO(𝓒)) →
(setPO(𝓑) = setPO(𝓓)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f PO_ISO_PO 𝓒 To 𝓓) → (f PO_ISO_PO (𝓐 InterPO 𝓒) To (𝓑 InterPO 𝓓))
axiom poiso_cart : ∀ 𝓐 𝓑 𝓒 𝓓, (𝓐 P≃O 𝓑) → (𝓒 P≃O 𝓓) → ((𝓐 CartPO 𝓒) P≃O (𝓑 CartPO 𝓓))


-- 45) induced order with order function saving creates isomorphic partial order

noncomputable def induced_R₂ (𝓐 f: Set) := {s ∈ (rng f) × (rng f) | ∃ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∧ s = (f⦅x⦆, f⦅y⦆)}
noncomputable def induced_order (𝓐 f: Set) := ⁅rng f; str (rng f) (induced_R₂ 𝓐 f); (induced_R₂ 𝓐 f)⁆

axiom poiso_induced : ∀ 𝓐 f X, (PartOrd 𝓐) → (f Inj (setPO(𝓐)) To X) → (f PO_ISO_PO 𝓐 To (induced_order 𝓐 f))
