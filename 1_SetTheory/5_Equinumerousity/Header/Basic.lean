axiom morgan_conj (p q : Prop) :  ¬(p ∧ q) ↔ ¬p ∨ ¬q

def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b

axiom Set : Type
axiom membership : Set → Set → Prop
infix:50 (priority := high) " ∈ " => membership
infix:50 (priority := high) " ∉ " => (fun (x : Set) => (fun (y : Set) => ¬ membership x y))

axiom set_to_prop (P : Set → Prop) (h : ∃! x, P x) : Set
axiom prop_to_set (P : Set → Prop) (h : ∃! x, P x) : P (set_to_prop P h) ∧ ∀ x, x ≠ set_to_prop P h → ¬P x

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
axiom neg_mon_diff : ∀ A B C, (A ⊆ B) → (C \ B) ⊆ (C \ A)
axiom double_compl (U : Set) (A : Set)  (h : A ⊆ U) : (U \ (U \ A)) = A



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


axiom cartesian_product_is_cartesian: ∀ A B pr, pr ∈ (A × B) ↔ (∃ x ∈ A; ∃ y ∈ B; pr = (x, y))
axiom cartesian_product_pair_prop : ∀ A B a b, (a, b) ∈ (A × B) ↔ (a ∈ A ∧ b ∈ B)
axiom cartesian_product_subset : ∀ A B C D, A ⊆ C → B ⊆ D → (A × B) ⊆ C × D
axiom fst_coor_set : ∀ A B pr, pr ∈ A × B → fst_coor pr ∈ A
axiom snd_coor_set : ∀ A B pr, pr ∈ A × B → snd_coor pr ∈ B
axiom fst_snd_then_unique : ∀ A B pr, pr ∈ A × B → pr = (fst_coor pr, snd_coor pr)
axiom equal_fst_snd : ∀ A B pr₁ pr₂, (pr₁ ∈ A × B) → (pr₂ ∈ A × B) →
  (fst_coor pr₁ = fst_coor pr₂) → (snd_coor pr₁ = snd_coor pr₂) → pr₁ = pr₂


-- tuple syntax
declare_syntax_cat pair_comprehension
syntax  pair_comprehension "; " term : pair_comprehension
syntax term : pair_comprehension
syntax "⁅" pair_comprehension "⁆" : term
macro_rules
| `(⁅ $term1:term; $term2:term⁆) => `(ordered_pair_set $term1 $term2)
| `(⁅ $rest:pair_comprehension; $elem:term⁆) => `(ordered_pair_set ⁅$rest:pair_comprehension⁆ $elem:term)



noncomputable def binary_relation (R : Set) : Prop := ∀ z ∈ R; ∃ a, ∃ b, z = (a, b)
noncomputable def binary_relation_between (A B R : Set) : Prop := R ⊆ A × B
noncomputable def binary_relation_on (A R : Set) : Prop := R ⊆ A × A


noncomputable def disjoint_union (A B : Set) := (A × {∅}) ∪ (B × {{∅}})
syntax term "⊔" term : term
macro_rules
| `($A ⊔ $B) => `(disjoint_union $A $B)



noncomputable def disjoint_union_left (X: Set) := {y ∈ X | (π₂ y) = ∅}
noncomputable def disjoint_union_right (X : Set) := {y ∈ X | (π₂ y) = {∅}}
syntax "DUL" term : term
syntax "DUR" term : term
macro_rules
| `(DUL $X) => `(disjoint_union_left $X)
| `(DUR $X) => `(disjoint_union_right $X)


axiom dul_A : ∀ A B, (DUL (A ⊔ B)) = (A × {∅})
axiom dur_B : ∀ A B, (DUR (A ⊔ B)) = (B × {{∅}})
axiom dul_subs : ∀ A B, (DUL (A ⊔ B)) ⊆ (A ⊔ B)
axiom dur_subs : ∀ A B, (DUR (A ⊔ B)) ⊆ (A ⊔ B)
axiom dulr_un : ∀ A B, (A ⊔ B) = (DUL (A ⊔ B)) ∪ (DUR (A ⊔ B))
axiom dulr_in : ∀ A B, (DUL (A ⊔ B)) ∩ (DUR (A ⊔ B)) = ∅
axiom disj_in_left : ∀ A B x, (x ∈ A) → ((x, ∅) ∈ (A ⊔ B))
axiom disj_in_right : ∀ A B x, (x ∈ B) → ((x, {∅}) ∈ (A ⊔ B))
axiom disjunion2_pair_prop : ∀ A B x y, (x, y) ∈ (A ⊔ B) ↔ (x ∈ A ∧ y = ∅) ∨ (x ∈ B ∧ y = {∅})


syntax "BinRel" term : term
macro_rules
|  `(BinRel $R:term) => `(binary_relation $R)
syntax term "BinRelOn" term : term
macro_rules
| `($R:term BinRelOn $A:term) => `(binary_relation_on $A $R)
syntax term "BinRelBtw" term "AND" term : term
macro_rules
| `($R:term BinRelBtw $A:term AND $B:term) => `(binary_relation_between $A $B $R)

-- write (x . P . y) istead of (x, y) ∈ P
macro_rules
| `(($x:term . $P:term . $y:term)) => `(($x, $y) ∈ $P)


noncomputable def dom (R : Set) := {x ∈ ⋃ (⋃ R) | ∃ y, (x . R . y)}
noncomputable def rng (R : Set) := {y ∈ ⋃ (⋃ R) | ∃ x, (x . R . y)}


axiom dom_prop : ∀ R x, x ∈ dom R ↔ ∃ y, (x . R . y)
axiom rng_prop : ∀ R y, y ∈ rng R ↔ ∃ x, (x . R . y)


noncomputable def comp (A B R : Set) : Set := (A × B) \ R



noncomputable def inv (R : Set) : Set := {z ∈ rng R × dom R | ∃ x, ∃ y, (z = (y, x) ∧ (x . R . y))}
syntax term"⁻¹" : term
macro_rules
| `($term1:term⁻¹) => `(inv $term1)
noncomputable def composition (P Q : Set) : Set := {pr ∈ dom Q × rng P | ∃ x y, (pr = (x, y)) ∧ ∃ z, (x . Q . z) ∧ (z . P . y)}
infix:60 (priority:=high) " ∘ " => composition


axiom composition_assoc : ∀ P Q R, ((P ∘ Q) ∘ R) = (P ∘ (Q ∘ R))


noncomputable def id_ (A : Set) : Set := {t ∈ (A × A) | ∃ x : Set, t = (x, x)}
noncomputable def rel_image (X R : Set) := {b ∈ rng R | ∃ a ∈ X; (a . R . b)}
syntax  term ".[" term "]" : term
macro_rules
  | `($R:term .[ $X:term ])  => `(rel_image $X $R)

axiom prop_then_binary_relation : ∀ A B R, R ⊆ A × B → binary_relation R ∧ dom R ⊆ A ∧ rng R ⊆ B

axiom id_rel_composition_left : ∀ A B  R, binary_relation_between A B R → ((id_ B) ∘ R) = R
axiom id_rel_composition_right : ∀ A B R, binary_relation_between A B R → (R ∘ (id_ A)) = R
axiom monotonic_rel_image : ∀ X Y R, binary_relation R → X ⊆ Y → R.[X] ⊆ R.[Y]

axiom rng_is_rel_image : ∀ R, binary_relation R → rng R = R.[dom R]

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
axiom function_equal_value_prop : ∀ f A B, (f Fun A To B) → ∀ x y, x ∈ A → ( (x . f . y) ↔ (y = f⦅x⦆))
axiom dom_function: ∀ f A B, (f Fun A To B) → A = dom f
axiom function_value_pick_property: ∀ f A B, ∀ x ∈ A; (f Fun A To B) → (x . f . (f⦅x⦆) )

noncomputable def part_same_val (f g x y : Set) : Prop := ((f ↑↑ x) ∧ g ↑↑ y) ∨ (((f ↓↓ x) ∧ (g ↓↓ y)) ∧ (f⦅x⦆ = g⦅y⦆))

syntax term "（" term "）" "≈" term "﹙" term "﹚" : term
macro_rules
  | `($f:term （ $x:term ） ≈ $g:term ﹙ $y:term ﹚) => `(part_same_val $f $g $x $y)


axiom function_composition : ∀ f g A B C, (f Fun A To B) → (g Fun B To C) → (((g ∘ f) Fun A To C) ∧ (∀ x ∈ dom f; (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆))

noncomputable def lam_fun (A B : Set) (P : Set → Set): Set := {z ∈ A × B | ∃ x, z = (x, P x)}
noncomputable def fun_restriction (f A : Set) := f ∩ (A × rng f)
infix:50 (priority := high) "⨡" => fun_restriction

axiom fun_restriction_prop : ∀ A B X f, (f Fun A To B) → (f ⨡ X) Fun (A ∩ X) To B
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

noncomputable def power_set (B A : Set) : Set := {f ∈ 𝒫 (A × B) | f Fun A To B}
syntax term "ℙow" term : term
macro_rules
  |`($A:term ℙow $B:term) => `(power_set $A $B)
axiom power_set_prop : ∀ A B f, f ∈ (B ℙow A) ↔ f Fun A To B


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

axiom leftrev_criterion:
  ∀ f A B, (f LeftRev A To B) ↔ ((f Inj A To B) ∧ (A ≠ ∅ ∨ B = ∅))

def choice_ax : Prop := ∀ A, ∅ ∉ A → ∃ f, f Choice A

axiom axiom_of_choice : choice_ax



-- 33) Right reversability criterion equivalent to axiom of choice
def right_rev_criterion_prop : Prop := ∀ f A B, (f RightRev A To B) ↔ (f Surj A To B)

axiom rightrev_criterion_AC_eq: choice_ax ↔ right_rev_criterion_prop


syntax term "⦅" term "," term "⦆" : term
syntax term "⦅" pair_comprehension "⦆" : term
macro_rules
| `($f:term ⦅ $x:term ; $y:term ⦆) =>  `($f⦅($x, $y)⦆)
| `($f:term ⦅ $x:pair_comprehension ; $y:term ⦆) => `($f⦅⁅ $x ; $y ⁆⦆)



-- 39) Indexed disjoint union and its properties
def fun_indexation (A I : Set) : Prop := ∃ X, A Fun I To X
syntax term "IndxFun" term : term
macro_rules
| `($A:term IndxFun $I:term) => `(fun_indexation  $A $I)

noncomputable def indexed_family (A I : Set) := A.[I]
syntax "{" term "of" term "where" term "in" term "}" : term
macro_rules
| `({ $A:term of $i:term where $i:term in $I:term }) => `(indexed_family $A $I)

noncomputable def indexed_set (A i : Set) := A⦅i⦆
infix:60 (priority := high) "_" => indexed_set

def indexation (A I : Set) : Prop := (∀ x, (x ∈ ({A of i where i in I})) ↔ (∃ i ∈ I; x = (A _ i)))
syntax term "Indx" term : term
macro_rules
| `($A:term Indx $I:term) => `(indexation $A $I)
axiom fun_indexed_is_indexed :
∀ A I, (A IndxFun I) → (A Indx I)


-- 37) Indexed union and its properties
noncomputable def indexed_union (A I : Set) := ⋃ (A.[I])
syntax "⋃[" term "in" term "]" term "at" term : term
macro_rules
| `(⋃[ $i:term in $I:term ] $A:term at $i:term) => `(indexed_union $A $I)
axiom indexed_union_is_union :
∀ A I, (A Indx I) → ∀ x, (x ∈ (⋃[ i in I ] A at i)) ↔ (∃ i ∈ I; x ∈ (A _ i))
axiom indexed_sub_indexed_union :
∀ A I, (A Indx I) → (∀ i ∈ I; (A _ i) ⊆ (⋃[ i in I ] A at i))


-- 38) Indexed intersection and its properties
noncomputable def indexed_intersection (A I : Set) := ⋂ (A.[I])
syntax "⋂[" term "in" term "]" term "at" term : term
macro_rules
| `(⋂[ $i:term in $I:term ] $A:term at $i:term ) => `(indexed_intersection $A $I)
axiom indexed_intersection_is_intersection :
∀ A I, (I ≠ ∅) → (A IndxFun I) → ∀ x, (x ∈ (⋂[ i in I ] A at i)) ↔ (∀ i ∈ I; x ∈ (A _ i))
axiom indexed_intersection_empty :
∀ A I, (I = ∅) → ((⋂[ i in I ] A at i) = ∅)
axiom indexed_intersection_sub_indexed:
∀ A I, (A IndxFun I) → (∀ i ∈ I; (⋂[ i in I ] A at i) ⊆ (A _ i))




-- 39) Indexed disjoint union and its properties
noncomputable def indexed_disjoined_union (A I : Set) := {s ∈ ((⋃[ i in I ] A at i) × I) | ∃ i ∈ I; ∃ x ∈ (A _ i); s = (x, i)}
syntax "⨆[" term "in" term "]" term "at" term : term
macro_rules
| `( ⨆[$i:term in $I:term ] $A:term at $i:term) => `(indexed_disjoined_union $A $I)
axiom indexed_disjoined_union_is_disjoined_union :
∀ A I, (A IndxFun I) → (∀ s, (s ∈ ⨆[ i in I ] A at i) ↔ (∃ i ∈ I; ∃ x ∈ (A _ i); s = (x, i)))

axiom indexed_disjoined_union_pair_prop₁ :
∀ A I, (A IndxFun I) → (∀ x y, ((x, y) ∈ ⨆[ i in I ] A at i) ↔ (∃ i ∈ I; x ∈ (A _ i) ∧ y = i))

axiom indexed_disjoined_union_pair_prop₂ :
∀ A I i, (A IndxFun I) → (i ∈ I) → (∀ x, ((x, i) ∈ ⨆[ i in I ] A at i) ↔ (x ∈ (A _ i)))

axiom indexed_disjoined_union_in :
∀ A I x i, (A IndxFun I) → (i ∈ I) → (x ∈ (A _ i)) → ((x, i) ∈ ⨆[ i in I ] A at i)

noncomputable def indexed_func (A) := lam_fun (dom A) (𝒫 (⋃ (rng A) × dom A)) (fun (i) => (A _ i) × {i})
syntax "DU" term : term
macro_rules
| `(DU $A) => `(indexed_func $A)


axiom DU_is_func : ∀ A I X, (A Fun I To X) → ((DU A) Fun I To (𝒫 (⋃ (rng A) × I))) ∧ (∀ i ∈ I; (DU A) _ i = (A _ i) × {i})
axiom DU_indxfun : ∀ A I, (A IndxFun I) → ((DU A) IndxFun I) ∧ (∀ i ∈ I; (DU A) _ i = (A _ i) × {i})


axiom indexed_disjoined_set_is_eq : ∀ A I i, (A IndxFun I) → (i ∈ I) → ((DU A) _ i) = {x ∈ ⨆[ i in I ] A at i | (π₂ x) = i}
axiom indexed_dishoined_set_subs : ∀ A I i, (A IndxFun I) → (i ∈ I) → ((DU A) _ i) ⊆ (⨆[ i in I ] A at i)
axiom indexed_disjoined_set_un : ∀ A I, (A IndxFun I) → (⨆[ i in I ] A at i) = (⋃[i in I] (DU A) at i)
axiom indexed_disjoined_set_int2 : ∀ A I i j, (A IndxFun I) → (i ∈ I) → (j ∈ I) → (i ≠ j) → ((DU A) _ i) ∩ ((DU A) _ j) = ∅
axiom indexed_disjoined_set_int : ∀ A I, (∀ j, I ≠ {j}) → (A IndxFun I) → (⋂[i in I] (DU A) at i) = ∅


-- 40) Indexed product and its properties
noncomputable def indexed_product (A I : Set) := {f ∈ ((⋃[ i in I ] A at i) ℙow (I)) | ∀ i ∈ I; f⦅i⦆ ∈ (A _ i)}
syntax "∏[" term "in" term "]" term "at" term : term
macro_rules
  |  `(∏[ $i:term in $I:term ] $A:term at $i:term ) => `(indexed_product $A $I)

axiom prod_pow : ∀ A I B, (A Indx I) → (∀ i ∈ I; (A _ i = B)) → (∏[ i in I ] A at i) = B ℙow I
axiom product_AC_eq : choice_ax ↔ (∀ A I, (A IndxFun I) → (∀ I ∈ I; (A _ I) ≠ ∅) → (∏[ i in I ] A at i) ≠ ∅)
