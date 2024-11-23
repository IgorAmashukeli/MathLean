import «Header»


-- 1) (a₁, a₂) (Ordered pair) construction and property
noncomputable def ordered_pair_set (a b : Set) := {{a}, {a, b}}
notation (priority := high) "(" a₁ ", " a₂ ")" => ordered_pair_set a₁ a₂
theorem ordered_pair_set_prop : ∀ a b c d, (a, b) = (c, d) ↔ (a = c ∧ b = d) := sorry
theorem ordered_pair_set_belonging: ∀ A B, ∀ a ∈ A; ∀ b ∈ B; (a, b) ∈ 𝒫 (𝒫 (A ∪ B)) := sorry
theorem inter_pair_is_singl_fst : ∀ a b, ⋂ (a, b) = {a} := sorry
theorem union_pair_is_all_coords : ∀ a b, ⋃ (a, b) = {a, b} := sorry
theorem coordinates_snd_corr_lemma : ∀ a b, {x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)} = {b} := sorry

-- 2) First coordinate and second coordinate projectors and their properties
noncomputable def fst_coor (A : Set) : Set := ⋃ (⋂ A)
noncomputable def snd_coor (A : Set) : Set := ⋃ ({x ∈ ⋃ A | ⋃ A ≠ ⋂ A → x ∉ ⋂ A})
theorem coordinates_fst_coor : ∀ a b, fst_coor (a, b) = a := sorry
theorem coordinates_snd_copr : ∀ a b, snd_coor (a, b) = b := sorry

syntax "π₁" term : term
syntax "π₂" term : term
macro_rules
| `(π₁ $s) => `(fst_coor $s)
| `(π₂ $s) => `(snd_coor $s)



-- 3) A × B (cartesian product) construction and its property
noncomputable def cartesian_product (A : Set) (B : Set) : Set := {z ∈ 𝒫 (𝒫 (A ∪ B)) | ∃ x ∈ A; ∃ y ∈ B; z = (x, y)}
infix:60 (priority:=high) " × " => cartesian_product
theorem cartesian_product_is_cartesian: ∀ A B pr, pr ∈ (A × B) ↔ (∃ x ∈ A; ∃ y ∈ B; pr = (x, y)) := sorry
theorem cartesian_product_pair_prop : ∀ A B a b, (a, b) ∈ (A × B) ↔ (a ∈ A ∧ b ∈ B) := sorry
theorem fst_snd_then_unique : ∀ A B pr, pr ∈ A × B → pr = (fst_coor pr, snd_coor pr) := sorry
theorem equal_fst_snd : ∀ A B pr₁ pr₂, (pr₁ ∈ A × B) → (pr₂ ∈ A × B) →
  (fst_coor pr₁ = fst_coor pr₂) → (snd_coor pr₁ = snd_coor pr₂) → pr₁ = pr₂ := sorry
theorem cartesian_product_subset : ∀ A B C D, A ⊆ C → B ⊆ D → (A × B) ⊆ C × D := sorry



-- 4) Tuple construction
-- ⁅a⁆, ⁅a, b⁆, ⁅a, b, c⁆, ⁅a, b, c, d⁆, ...
declare_syntax_cat pair_comprehension
syntax  pair_comprehension "; " term : pair_comprehension
syntax term : pair_comprehension
syntax "⁅" pair_comprehension "⁆" : term
macro_rules
| `(⁅ $term1:term⁆) => `($term1)
| `(⁅ $term1:term; $term2:term⁆) => `(ordered_pair_set $term1 $term2)
| `(⁅ $rest:pair_comprehension; $elem:term⁆) => `(ordered_pair_set ⁅$rest:pair_comprehension⁆ $elem:term)


-- 5) BinRelary relation construction and its property
noncomputable def binary_relation (R : Set) : Prop := ∀ z ∈ R; ∃ a, ∃ b, z = (a, b)

-- 6) BinRelary relation, implemented as a cartesian product subset
noncomputable def binary_relation_between (A B R : Set) : Prop := R ⊆ A × B
noncomputable def binary_relation_on (A R : Set) : Prop := R ⊆ A × A

syntax "BinRel" term : term
macro_rules
|  `(BinRel $R:term) => `(binary_relation $R)
syntax term "BinRelOn" term : term
macro_rules
| `($R:term BinRelOn $A:term) => `(binary_relation_on $A $R)
syntax term "BinRelBtw" term "AND" term : term
macro_rules
| `($R:term BinRelBtw $A:term AND $B:term) => `(binary_relation_between $A $B $R)


macro_rules
| `(($x:term . $P:term . $y:term)) => `(($x, $y) ∈ $P)
theorem binary_relation_elements_set: ∀ R x y, (x . R . y) → (x ∈ ⋃ (⋃ R) ∧ y ∈ ⋃ (⋃ R)) := sorry


-- 7)  Domain and range of binary relation and their properties
noncomputable def dom (R : Set) := {x ∈ ⋃ (⋃ R) | ∃ y, (x . R . y)}
noncomputable def rng (R : Set) := {y ∈ ⋃ (⋃ R) | ∃ x, (x . R . y)}
theorem dom_rng_rel_prop: ∀ R, (BinRel R) → (dom R ∪ rng R = ⋃ (⋃ R)) := sorry
theorem dom_prop : ∀ R x, x ∈ dom R ↔ ∃ y, (x . R . y) := sorry
theorem rng_prop : ∀ R y, y ∈ rng R ↔ ∃ x, (x . R . y) := sorry
theorem binary_relation_prop : ∀ R, (BinRel R) → (R BinRelBtw dom R AND rng R) := sorry
theorem prop_then_binary_relation : ∀ A B R, (R BinRelBtw A AND B) → (BinRel R) ∧ dom R ⊆ A ∧ rng R ⊆ B := sorry
theorem rel_dom_rng_elem : ∀ R, (BinRel R) → ∀ x y, (x . R . y) → x ∈ dom R ∧ y ∈ rng R := sorry


-- 8) Union and intersection of binary relation is binary relation
theorem union2_rel_is_rel : ∀ P Q, (BinRel P) → (BinRel Q) → (BinRel (P ∪ Q)) := sorry
theorem intersect2_rel_is_rel : ∀ P Q, (BinRel P) → (BinRel Q) → (BinRel (P ∩ Q)) := sorry



-- 9) Complement binary relation
noncomputable def comp (A B R : Set) : Set := (A × B) \ R
theorem comp_is_rel : ∀ A B R, (BinRel (comp A B R)) := sorry


-- 10) Properties, enough for subset and equality of binary relation
theorem rel_subset : (∀ P Q, (BinRel P) → (BinRel Q) → (∀ x y, (x . P . y) → (x . Q . y)) → P ⊆ Q) := sorry
theorem relation_equality : (∀ P Q, (BinRel P) → (BinRel Q) → ((∀ x y, (x . P . y) ↔ (x . Q . y)) → P = Q)) := sorry


-- 11) R⁻¹ (inverse binary relation) construction and its properties
noncomputable def inv (R : Set) : Set := {z ∈ rng R × dom R | ∃ x, ∃ y, (z = (y, x) ∧ (x . R . y))}
syntax term"⁻¹" : term
macro_rules
| `($term1:term⁻¹) => `(inv $term1)
theorem inv_is_rel : ∀ R, (BinRel R) → (BinRel (R⁻¹)) := sorry
theorem inv_pair_prop: ∀ R, (BinRel R) → ∀ x y, (x . R . y) ↔ (y . (R⁻¹) . x):= sorry
theorem inv_prop : ∀ R, (BinRel R) → (R⁻¹)⁻¹ = R := sorry
theorem inv_dom: ∀ R, (BinRel R) → dom (R⁻¹) = rng R := sorry
theorem inv_rng: ∀ R, (BinRel R) → rng (R⁻¹) = dom R := sorry
theorem inv_between_mp : ∀ A B R, (R BinRelBtw A AND B) → (R⁻¹ BinRelBtw B AND A) := sorry


-- 12) P ∘ Q (composition of binary relations) construction and its properties
noncomputable def composition (P Q : Set) : Set := {pr ∈ dom Q × rng P | ∃ x y, (pr = (x, y)) ∧ ∃ z, (x . Q . z) ∧ (z . P . y)}
infix:60 (priority:=high) " ∘ " => composition
theorem composition_is_rel : ∀ P Q, binary_relation (P ∘ Q) := sorry
theorem composition_pair_prop : ∀ P Q, ∀ x y, (x . (P ∘ Q) . y) ↔ ∃ z, (x . Q . z) ∧ (z . P . y) := sorry
theorem composition_pair_assoc: ∀ P Q R x y, (x . ((P ∘ Q) ∘ R) . y) ↔ (x . (P ∘ (Q ∘ R)) . y) := sorry
theorem composition_assoc : ∀ P Q R, ((P ∘ Q) ∘ R) = (P ∘ (Q ∘ R)) := sorry


-- 13) Inverse and other operations
theorem inv_composition_pair_prop : ∀ P Q, (BinRel P) → (BinRel Q) → (∀ x y, (x . ((P ∘ Q)⁻¹) . y) ↔ (x . ((Q⁻¹) ∘ P⁻¹) . y)) := sorry
theorem inv_composition_prop : ∀ P Q, (BinRel P) → (BinRel Q) → (P ∘ Q)⁻¹ = ((Q⁻¹) ∘ (P⁻¹)) := sorry
theorem inv_union_pair_prop : ∀ P Q, (BinRel P) → (BinRel Q) → ∀ x y, (x . ((P ∪ Q)⁻¹) . y) ↔ (x . (P⁻¹ ∪ Q⁻¹) . y) := sorry
theorem inv_union_prop : ∀ P Q, (BinRel P) → (BinRel Q) → (P ∪ Q)⁻¹ = ((P⁻¹) ∪ Q⁻¹) := sorry
theorem comp_inv_prop_pair : ∀ P A B, (P  BinRelBtw A AND B) → ∀ x y, (x . (comp A B (P⁻¹)) . y) ↔ (x . ((comp B A P)⁻¹) . y) := sorry
theorem comp_inv_prop : ∀ P A B, (P  BinRelBtw A AND B) → comp A B (P⁻¹) = (comp B A P)⁻¹ := sorry


-- 14) Composition and other operations
theorem union_composition_pair_prop_right : ∀ P Q R, ∀ x y, (x . ((P ∪ Q) ∘ R) . y) ↔ (x . ((P ∘ R) ∪ (Q ∘ R)) . y) := sorry
theorem union_composition_prop_right : ∀ P Q R, ((P ∪ Q) ∘ R) = ((P ∘ R) ∪ (Q ∘ R))  := sorry
theorem union_composition_pair_prop_left : ∀ P Q R, ∀ x y, (x . (P ∘ (Q ∪ R)) . y) ↔ (x . ((P ∘ Q) ∪ (P ∘ R)) . y) := sorry
theorem compostion_union_prop_left : ∀ P Q R, P ∘ (Q ∪ R) = (P ∘ Q) ∪ (P ∘ R) := sorry
theorem monotonic_subset_composition_pair_right : ∀ P Q R, P ⊆ Q → (∀ x y, (x . (P ∘ R) . y) → (x . (Q ∘ R) . y)) := sorry
theorem monotonic_subset_composition_right : ∀ P Q R, P ⊆ Q → P ∘ R ⊆ Q ∘ R := sorry
theorem monotonic_subset_composition_pair_left : ∀ P Q R, P ⊆ Q → (∀ x y, (x . (R ∘ P) . y) → (x . (R ∘ Q) . y)) := sorry
theorem monotonic_subset_composition_left : ∀ P Q R, P ⊆ Q → R ∘ P ⊆ R ∘ Q := sorry
theorem intersect2_composition_prop_right: ∀ P Q R, (P ∩ Q) ∘ R ⊆ (P ∘ R) ∩ (Q ∘ R) := sorry
theorem intersect2_composition_prop_left: ∀ P Q R, P ∘ (Q ∩ R) ⊆ (P ∘ Q) ∩ (P ∘ R) := sorry


-- 15) Identical binary relation andits properties
noncomputable def id_ (A : Set) : Set := {t ∈ (A × A) | ∃ x : Set, t = (x, x)}
theorem id_is_rel : ∀ A, binary_relation (id_ A) := sorry
theorem id_prop : ∀ A x y, (x . (id_ A) . y) → (((x = y) ∧ (x ∈ A)) ∧ (y ∈ A)) := sorry
theorem prop_then_id : ∀ A, ∀ x ∈ A; (x . (id_ A) . x) := sorry
theorem inv_id : ∀ A, ((id_ A)⁻¹) = (id_ A) := sorry
theorem id_rel_composition_right : ∀ A B R, (R BinRelBtw A AND B) → (R ∘ (id_ A)) = R := sorry
theorem id_rel_composition_left : ∀ A B R, (R BinRelBtw A AND B) → ((id_ B) ∘ R) = R := sorry


-- 16) Image of a binary relation construction
noncomputable def rel_image (X R : Set) := {b ∈ rng R | ∃ a ∈ X; (a . R . b)}
syntax  term ".[" term "]" : term
macro_rules
  | `($R:term .[ $X:term ])  => `(rel_image $X $R)


-- 17) Preimage is just image of inverse
-- but it can be deined differently
theorem rel_pre_image_eq : ∀ Y R, (BinRel R) → R⁻¹.[Y] = {a ∈ dom R | ∃ b ∈ Y; (a . R . b)} := sorry


-- 18) Image and preimage main properties
theorem image_prop : ∀ R y X, (y ∈ R.[X] ↔ ∃ x ∈ X; (x . R . y)) := sorry
theorem preimage_prop : ∀ R Y, (BinRel R) → ∀ x, (x ∈ R⁻¹.[Y] ↔ ∃ y ∈ Y; (x . R . y)) := sorry



-- 19) Range and domain as image and preimage
theorem rng_is_rel_image : ∀ R, (BinRel R) → rng R = R.[dom R] := sorry
theorem dom_preimage : ∀ A B P, (P  BinRelBtw A AND B) → dom P = P⁻¹.[B] := sorry


-- 20) Image and preimage other properties
theorem rel_image_union : ∀ X Y R, (BinRel R) → R.[X ∪ Y] = R.[X] ∪ R.[Y] := sorry
theorem rel_preimage_union : ∀ X Y R , (BinRel R) → R⁻¹.[X ∪ Y] = R⁻¹.[X] ∪ R⁻¹.[Y] := sorry
theorem monotonic_rel_image : ∀ X Y R, (BinRel R) → X ⊆ Y → R.[X] ⊆ R.[Y] := sorry
theorem monotonic_rel_preimage : ∀ X Y R, (BinRel R) → X ⊆ Y → R⁻¹.[X] ⊆ R⁻¹.[Y] := sorry
theorem rel_image_inter : ∀ X Y R, (BinRel R) → R.[X ∩ Y] ⊆ (R.[X] ∩ R.[Y]) := sorry
theorem rel_preimage_inter : ∀ X Y R, (BinRel R) → R⁻¹.[X ∩ Y] ⊆ (R⁻¹.[X] ∩ R⁻¹.[Y]) := sorry
theorem rel_image_composition : ∀ P Q X, (P ∘ Q).[X] = P.[Q.[X]] := sorry
theorem rel_preimage_composition : ∀ P Q X, (BinRel P) → (BinRel Q) → (P ∘ Q)⁻¹.[X] = Q⁻¹.[P⁻¹.[X]] := sorry
theorem rel_image_diff : ∀ X Y R, (R.[X] \ R.[Y]) ⊆ (R.[X \ Y]) := sorry
theorem rel_preimage_diff : ∀ X Y R, (R⁻¹.[X] \ R⁻¹.[Y]) ⊆ (R⁻¹.[X \ Y]) := sorry
