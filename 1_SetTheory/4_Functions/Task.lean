import «Header»

-- 1) Main properties : Functionality, totality, injectivity and surjectivity
noncomputable def is_functional (R : Set) : Prop := ∀ x y z, (x . R . y) → (x . R . z) → y = z
noncomputable def is_total (R X : Set) : Prop := ∀ x ∈ X; ∃ y, (x . R . y)
noncomputable def is_injective (R : Set) : Prop := ∀ x y z, (x . R . z) → (y . R . z) → x = y
noncomputable def is_surjective (R Y : Set) : Prop := ∀ y ∈ Y; ∃ x, (x . R . y)
noncomputable def rel_is_functional (R : Set) : Prop := (BinRel R) ∧ is_functional R
noncomputable def rel_is_total (R X : Set) : Prop := (BinRel R) ∧ is_total R X
noncomputable def rel_is_injective (R : Set) : Prop := (BinRel R) ∧ is_injective R
noncomputable def rel_is_surjective (R Y : Set) : Prop := (BinRel R) ∧ is_surjective R Y


-- 2) Inverse relation and functionality, totality, injectivity and surjectivity
theorem func_inv_inj : ∀ R, (BinRel R) → (is_functional R ↔ is_injective (R⁻¹)) := sorry
theorem inj_inv_func : ∀ R, (BinRel R) → (is_injective R ↔ is_functional (R⁻¹)) := sorry
theorem tot_inv_surj : ∀ R X, (BinRel R) → ((is_total R X) ↔ (is_surjective (R⁻¹) X)) := sorry
theorem surj_inv_tot : ∀ R X, (BinRel R) → ((is_surjective R X) ↔ (is_total (R⁻¹) X)) := sorry


-- 3) Subset and functionality, totality, injectivity and surjectivity
theorem func_subs : ∀ P Q, (is_functional Q) → (P ⊆ Q) → (is_functional P) := sorry
theorem inj_subs : ∀ P Q, (is_injective Q) → (P ⊆ Q) → (is_injective P) := sorry
theorem tot_subs : ∀ P Q, (is_total P A) → (P ⊆ Q) → (is_total Q (A ∪ dom Q)) := sorry
theorem surj_subs : ∀ P Q, (is_surjective P A) → (P ⊆ Q) → (is_surjective Q (A ∪ rng Q)) := sorry


-- 4) Union and functionality, totality, injectivity and surjectivity
theorem func_un :
∀ A B C D P Q,
(P BinRelBtw A AND B) → (Q BinRelBtw C AND D) → (A ∩ C = ∅) → (is_functional P) → (is_functional Q) → (is_functional (P ∪ Q)) := sorry
theorem inj_un :
∀ A B C D P Q,
 (P BinRelBtw A AND B) → (Q BinRelBtw C AND D) → (B ∩ D = ∅) → (is_injective P) → (is_injective Q) → (is_injective (P ∪ Q)) := sorry
theorem tot_un :
∀ A B P Q, (is_total P A) → (is_total Q B) → (is_total (P ∪ Q) (A ∪ B)) := sorry
theorem surj_un :
∀ A B P Q, (is_surjective P A) → (is_surjective Q B) → (is_surjective (P ∪ Q) (A ∪ B)) := sorry


-- 5) Intersection and functionality, totality, injectivity and surjectivity
theorem func_intr :
∀ P Q, (is_functional P ∨ is_functional Q) → (is_functional (P ∩ Q)) := sorry
theorem inj_intr :
∀ P Q, (is_injective P ∨ is_injective Q) → (is_injective (P ∩ Q)) := sorry
theorem tot_intr :
∀ P Q A B, (is_total P A) → (is_total Q B) → (is_functional (P ∪ Q)) → (is_total (P ∩ Q) (A ∩ B)) := sorry
theorem surj_intr :
∀ P Q A B, (is_surjective P A) → (is_surjective Q B) → (is_injective (P ∪ Q)) → (is_surjective (P ∩ Q) (A ∩ B)) := sorry


-- 6) Difference and functionality, totality, injectivity and surjectivity
theorem func_diff : ∀ P Q, (is_functional P) → (is_functional (P \ Q)) := sorry
theorem inj_diff : ∀ P Q, (is_injective P) → (is_injective (P \ Q)) := sorry
theorem tot_diff : ∀ P Q A, (is_total P A) → (is_total (P \ Q) (A \ (dom (P ∩ Q)) )) := sorry
theorem surj_diff : ∀ P Q A, (is_surjective P A) → (is_surjective (P \ Q) (A \ (rng (P ∩ Q)))) := sorry


-- 7) Main properties and domain, range, image and preimage
theorem tot_dom_prop : ∀ R X, ((is_total R X) ↔ (X ⊆ dom R)) := sorry
theorem surj_rng_prop : ∀ R X, ((is_surjective R X) ↔ (X ⊆ rng R)) := sorry
theorem preimage_inter_func : ∀ R, (BinRel R) → ((is_functional R) ↔ (∀ X Y, R⁻¹.[X ∩ Y] = (R⁻¹.[X] ∩ R⁻¹.[Y]))) := sorry
theorem image_inter_inject : ∀ R, (BinRel R) → ((is_injective R) ↔ (∀ X Y, R.[X ∩ Y] = (R.[X] ∩ R.[Y]) )) := sorry
theorem preimage_diff_func : ∀ R, (BinRel R) → ((is_functional R) ↔ (∀ X Y, R⁻¹.[X \ Y] = (R⁻¹.[X]) \ (R⁻¹.[Y]))) := sorry
theorem image_diff_inj : ∀ R, (BinRel R) → ((is_injective R) ↔ (∀ X Y, R.[X \ Y] = (R.[X]) \ (R.[Y]))) := sorry


-- 8) Composition and functionality, totality, injectivity and surjectivity
theorem composition_functional : ∀ P Q, is_functional P → is_functional Q → is_functional (P ∘ Q) := sorry
theorem composition_injective : ∀ P Q, is_injective P → is_injective Q → is_injective (P ∘ Q) := sorry
theorem composition_total : ∀ P Q X Y, (Q BinRelBtw Y AND X) → is_total P X → is_total Q Y → is_total (P ∘ Q) Y := sorry
theorem composition_surjective
: ∀ P Q X Y, (P BinRelBtw Y AND X) → is_surjective P X → is_surjective Q Y → is_surjective (P ∘ Q) X := sorry


-- 9) Partial Funaction and Function definion
noncomputable def partial_function (f A B : Set) : Prop := (f BinRelBtw A AND B) ∧ is_functional f
syntax term "PartFun" term "To" term : term
macro_rules
  | `($f:term PartFun $A:term To $B:term)  => `(partial_function $f $A $B)

noncomputable def function (f A B : Set) : Prop := (f PartFun A To B) ∧ is_total f A
syntax term "Fun" term "To" term : term
macro_rules
  | `($f:term Fun $A:term To $B:term) => `(function $f $A $B)


-- 10) Power set and its property
noncomputable def power_set (B A : Set) : Set := {f ∈ 𝒫 (A × B) | f Fun A To B}
syntax term "ℙow" term : term
macro_rules
  |`($A:term ℙow $B:term) => `(power_set $A $B)
theorem power_set_prop : ∀ A B f, f ∈ (B ℙow A) ↔ f Fun A To B := sorry


-- 11) Defined and undefined value
noncomputable def val_defined (f x : Set) : Prop := x ∈ dom f
noncomputable def val_undefined (f x : Set) : Prop := x ∉ dom f
syntax term "↓↓" term : term
macro_rules
  | `($f:term ↓↓ $x:term) => `(val_defined $f $x)
syntax term "↑↑" term : term
macro_rules
  | `($f:term ↑↑ $x:term) => `(val_undefined $f $x)


-- 12) Each function is partial function
-- each partial function can have different B and different A
-- each function can have different B
-- each function has defined A
theorem function_is_partial_function: ∀ f A B, (f Fun A To B) → (f PartFun A To B) := sorry
theorem partial_function_change_B : ∀ f A B C, (f PartFun A To B) → (B ⊆ C) → (f PartFun A To C) := sorry
theorem partial_function_change_A : ∀ f A B C, (f PartFun A To B) → (A ⊆ C) → (f PartFun C To B) := sorry
theorem function_change_B : ∀ f A B C, (f Fun A To B) → (B ⊆ C) → (f Fun A To C) := sorry
theorem function_no_change_A : ∀ f A B C, (f Fun A To B) → (f Fun C To B) → (A = C) := sorry
theorem function_rng_def : ∀ f A B, (f Fun A To B) → (f Fun A To (rng f)) := sorry
theorem partfunction_dom_def : ∀ f A B, (f PartFun A To B) → (f Fun (dom f) To B) := sorry


-- 13) Domain and range of partial function and function properties
theorem dom_partial_function : ∀ f A B, (f PartFun A To B) → dom f ⊆ A := sorry
theorem rng_partial_function : ∀ f A B, (f PartFun A To B) → rng f ⊆ B := sorry
theorem dom_function: ∀ f A B, (f Fun A To B) → A = dom f := sorry


-- 14) Value of a partial function/function
noncomputable def value_pick (f x : Set) : Set := ⋃ (f  .[ { x } ])
syntax term "⦅" term "⦆" : term
macro_rules
  | `($f:term ⦅ $x:term ⦆) => `(value_pick $f $x)


-- 15) Axiom of Choice
-- This is the last axiom of ZFC set theory
-- ZFC consists of ZF and AC, ZF axioms were shown before
-- Later all the theorems proved with this axiom will be named with ending on AC
noncomputable def choice_function (A f : Set) : Prop := (f Fun A To (⋃ A)) ∧ (∀ X ∈ A; f⦅X⦆ ∈ X)
syntax term "Choice" term : term
infix:60 (priority := high) " Choice " => fun (f) => fun (A) => choice_function A f
def choice_ax : Prop := ∀ A, ∅ ∉ A → ∃ f, f Choice A
axiom axiom_of_choice : choice_ax


-- 16) Value main properties
theorem partial_function_value_pick_property_defined : ∀ f A B x, (f PartFun A To B) → (f ↓↓ x) → (x . f . (f⦅x⦆)) := sorry
theorem function_value_pick_property: ∀ f A B, ∀ x ∈ A; (f Fun A To B) → (x . f . (f⦅x⦆) ) := sorry
theorem partial_function_equal_value_prop : ∀ f A B, (f PartFun A To B) → ∀ x y, (f ↓↓ x) → ( (x . f . y) ↔ (y = f⦅x⦆)) := sorry
theorem function_equal_value_prop : ∀ f A B, (f Fun A To B) → ∀ x y, x ∈ A → ( (x . f . y) ↔ (y = f⦅x⦆)) := sorry


--  17) f⦅x ; y⦆, f⦅x ; y ; z⦆, f⦅x ; y ; z ; a⦆ defnitions
syntax term "⦅" term "," term "⦆" : term
syntax term "⦅" pair_comprehension "⦆" : term
macro_rules
| `($f:term ⦅ $x:term ; $y:term ⦆) =>  `($f⦅($x, $y)⦆)
| `($f:term ⦅ $x:pair_comprehension ; $y:term ⦆) => `($f⦅⁅ $x ; $y ⁆⦆)


-- 18) Same values definition
noncomputable def part_same_val (f g x y : Set) : Prop := ((f ↑↑ x) ∧ g ↑↑ y) ∨ (((f ↓↓ x) ∧ (g ↓↓ y)) ∧ (f⦅x⦆ = g⦅y⦆))
syntax term "（" term "）" "≈" term "﹙" term "﹚" : term
macro_rules
  | `($f:term （ $x:term ） ≈ $g:term ﹙ $y:term ﹚) => `(part_same_val $f $g $x $y)


-- 19) Paritial function and function equality criteria
theorem partial_equal_functions : ∀ f g A B C D, (f PartFun A To B) → (g PartFun C To D) → ((f = g) ↔ (∀ x, (f（x） ≈ g﹙x﹚))) := sorry
theorem equal_functions_abcd : ∀ f g A B C D, (f Fun A To B) → (g Fun C To D) → ((f = g) ↔ (dom f = dom g ∧ ∀ x, f⦅x⦆ = g⦅x⦆)) := sorry
theorem equal_functions_abc: ∀ f g A B C, (f Fun A To B) → (g Fun A To C) → ((f = g) ↔ (∀ x, f⦅x⦆ = g⦅x⦆)) := sorry
theorem equal_functions_abc_A:  ∀ f g A B C, (f Fun A To B) → (g Fun A To C) → ((f = g) ↔ (∀ x ∈ A; f⦅x⦆ = g⦅x⦆)) := sorry


-- 20) Value membership
theorem part_val_in_B : ∀ f A B, (f PartFun A To B) → ∀ x ∈ dom f; f⦅x⦆ ∈ B := sorry
theorem part_val_in_rng : ∀ f A B, (f PartFun A To B) → ∀ x ∈ dom f; f⦅x⦆ ∈ rng f := sorry
theorem val_in_B : ∀ f A B, (f Fun A To B) → ∀ x ∈ A; f⦅x⦆ ∈ B := sorry
theorem val_in_rng : ∀ f A B, (f Fun A To B) → ∀ x ∈ A; f⦅x⦆ ∈ rng f := sorry
theorem if_val_in_C : ∀ f A B C, (f Fun A To B) → (∀ x ∈ A; (f⦅x⦆ ∈ C)) → (f Fun A To C) := sorry


-- 21) Image/preimage and value and image property
theorem part_fun_val_image_prop : ∀ f A B, (f PartFun A To B) → ∀ x y, (x ∈ dom f) → ((f⦅x⦆ = y) ↔ (f.[{x}] = {y})) := sorry
theorem func_val_image_singl_prop : ∀ f A B, (f Fun A To B) → ∀ x y, (x ∈ A) → ((f⦅x⦆ = y) ↔ (f.[{x}] = {y})) := sorry
theorem part_func_val_preimage_prop : ∀ f A B C, (f PartFun A To B) → ∀ x ∈ dom f; f⦅x⦆ ∈ C ↔ x ∈ f⁻¹.[C] := sorry
theorem part_func_img_prop : ∀ f A B, (f PartFun A To B) → ∀ X, f.[X] ⊆ B := sorry


-- 22) Composition of partial function and function
theorem partial_composition :
 ∀ f g A B C, (f PartFun A To B) → (g PartFun B To C) → (((g ∘ f) PartFun A To C) ∧ (∀ x ∈ dom f; (g ∘ f)（x） ≈ g﹙f⦅x⦆﹚)) := sorry
theorem function_composition :
 ∀ f g A B C, (f Fun A To B) → (g Fun B To C) → (((g ∘ f) Fun A To C) ∧ (∀ x ∈ dom f; (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆)) := sorry
theorem function_composition_A :
∀ f g A B C, (f Fun A To B) → (g Fun B To C) → (((g ∘ f) Fun A To C) ∧ (∀ x ∈ A; (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆)) := sorry


-- 23) Lambda function set
noncomputable def lam_fun (A B : Set) (P : Set → Set): Set := {z ∈ A × B | ∃ x, z = (x, P x)}
theorem lam_then_part_fun_prop (P : Set → Set) :
∀ A B, (∀ x ∈ dom (lam_fun A B P); P x ∈ B)
 → ((lam_fun A B P) PartFun A To B) ∧ (∀ x ∈ dom (lam_fun A B P); (lam_fun A B P)⦅x⦆ = P x) := sorry
theorem lam_then_fun_prop (P : Set → Set) :
 ∀ A B, (∀ x ∈ A; P x ∈ B) →  (((lam_fun A B P) Fun A To B) ∧ (∀ x ∈ A; (lam_fun A B P)⦅x⦆ = P x)) := sorry
theorem prop_then_lam_part_fun (P : Set → Set) :
 ∀ A B f, (f PartFun A To B) → (∀ x ∈ dom f; f⦅x⦆ = P x) → (∀ x, x ∉ dom f → (P x ∉ B)) → (f = lam_fun A B P) := sorry
theorem prop_then_lam_fun (P : Set → Set) : ∀ A B f, (f Fun A To B) → (∀ x ∈ A; (f⦅x⦆ = P x)) → (f = lam_fun A B P) := sorry




-- 24) Lambda function set with condition
noncomputable def lam_cond_fun (A B : Set) (P : Set → Prop) (c d : Set → Set) :=
  {z ∈ A × B | ∃ x, (P x → z = (x, c x)) ∧ (¬P x → z = (x, d x))}
theorem lam_cond_part_fun_prop : ∀ A B : Set, ∀ P : Set → Prop, ∀ c d : Set → Set,
  ((lam_cond_fun A B P c d) PartFun A To B) ∧
  (∀ x ∈ dom (lam_cond_fun A B P c d) ;
  (P x → (lam_cond_fun A B P c d)⦅x⦆ = c x) ∧ (¬P x → (lam_cond_fun A B P c d)⦅x⦆ = d x)) := sorry
theorem lam_cond_fun_prop : ∀ A B : Set, ∀ P : Set → Prop, ∀ c d : Set → Set,
  (∀ x ∈ A; (P x → c x ∈ B) ∧ (¬P x → d x ∈ B)) →
  ((lam_cond_fun A B P c d) Fun A To B) ∧
  (∀ x ∈ A ; (P x → (lam_cond_fun A B P c d)⦅x⦆ = c x) ∧ (¬P x → (lam_cond_fun A B P c d)⦅x⦆ = d x)) := sorry


-- 25) Partial function and function restrictions
noncomputable def fun_restriction (f A : Set) := f ∩ (A × rng f)
infix:50 (priority := high) "⨡" => fun_restriction
theorem part_fun_restriction_prop : ∀ A B X f, (f PartFun A To B) → (f ⨡ X) PartFun X To B := sorry
theorem part_fun_restriction_dom_subs_prop : ∀ A B X f, (X ⊆ dom f) →  (f PartFun A To B) → (f ⨡ X) Fun X To B := sorry
theorem fun_restriction_prop : ∀ A B X f, (f Fun A To B) → (f ⨡ X) Fun (A ∩ X) To B := sorry
theorem fun_restriction_val : ∀ A B f, (f Fun A To B) → ∀ x ∈ X; f⦅x⦆ = (f ⨡ X)⦅x⦆ := sorry
theorem inj_restriction_prop : ∀ X f, (is_injective f) → (is_injective (f ⨡ X)) := sorry
theorem surj_restriction_prop : ∀ Y f, (is_surjective f Y) → (is_surjective (f ⨡ X) (Y ∩ f.[X])) := sorry

-- 26) Partial function and function extension

def continues (f g) := (f = (g ⨡ (dom f)))
syntax term "Continues" term : term
macro_rules
| `($g Continues $f) => `(continues $f $g)

theorem partfun_cont_cond: ∀ A B C D f g, (f PartFun A To B) → (g PartFun C To D) →
((g Continues f) ↔ ((dom f ⊆ dom g) ∧ (∀ x ∈ dom f; f⦅x⦆ = g⦅x⦆))) := sorry
theorem partfun_cont_B : ∀ A B C D f g, (f PartFun A To B) → (g PartFun C To D) → (f PartFun A To D) := sorry
theorem fun_cont_cond: ∀ A B C D f g, (f Fun A To B) → (g Fun C To D) → ((g Continues f) ↔ ((A ⊆ C) ∧ (∀ x ∈ A; f⦅x⦆ = g⦅x⦆))) := sorry
theorem fun_cont_B : ∀ A B C D f g, (f Fun A To B) → (g Fun C To D) → (f Fun A To D) := sorry
theorem total_fun_cont_cond : ∀ A B f g, (f PartFun A To B) → (g Fun A To D) → ((g Continues f) ↔ (∀ x ∈ dom f; f⦅x⦆ = g⦅x⦆)) := sorry

-- 27) Monotonic operator fix point lemma
theorem monotonic_operator_fix_point : ∀ A F, (F Fun 𝒫 A To 𝒫 A) → (∀ X Y ∈ 𝒫 A; X ⊆ Y → F⦅X⦆ ⊆ F⦅Y⦆) → (∃ Z ∈ 𝒫 A; F⦅Z⦆ = Z) := sorry


-- 28) Injection, surjection and bijection
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


-- 29) id relation is bijection
theorem id_is_bij : ∀ A, (id_ A) Bij A To A := sorry
theorem id_val_prop : ∀ A x, (x ∈ A) → (id_ A⦅x⦆ = x) := sorry


-- 30) Bijection, injection and surjection relations
theorem bij_is_inj : ∀ A B f, (f Bij A To B) → (f Inj A To B) := sorry
theorem bij_is_surj : ∀ A B f, (f Bij A To B) → (f Surj A To B) := sorry
theorem inj_surj_is_bij : ∀ A B f, (f Inj A To B) → (f Surj A To B) → (f Bij A To B) := sorry


-- 31) Injection and surjection criteria for functions
theorem func_inj_prop : ∀ A B f, (f Fun A To B) → ((f Inj A To B) ↔ (∀ x y ∈ A; (f⦅x⦆ = f⦅y⦆) → x = y)) := sorry
theorem func_surj_prop : ∀ A B f, (f Fun A To B) → ((f Surj A To B) ↔ (∀ y ∈ B; ∃ x ∈ A; y = f⦅x⦆)) := sorry
theorem func_surj_crit : ∀ A B f, (f Fun A To B) → ((f Surj A To B) ↔ rng f = B) := sorry


-- 32) Composition of injection, surjection and bijection
theorem injection_composition : ∀ f g A B C, (f Inj A To B) → (g Inj B To C) → (((g ∘ f) Inj A To C)) := sorry
theorem surjection_composition : ∀ f g A B C, (f Surj A To B) → (g Surj B To C) → (((g ∘ f) Surj A To C)) := sorry
theorem bijection_composition : ∀ f g A B C, (f Bij A To B) → (g Bij B To C) → ((g ∘ f) Bij A To C) := sorry


-- 33) Reversed relation of bijection properties
theorem bijection_inv_mp : ∀ f A B, ((f Bij A To B) → (f⁻¹ Bij B To A)) := sorry
theorem bijection_inv : ∀ f A B, binary_relation f → ((f Bij A To B) ↔ (f⁻¹ Bij B To A)) := sorry



-- 34) Functionality, totality, injectivity, and surjectivity and bijection criteria with respect to composition, inverse, id
-- and ff⁻¹ val and image terms
theorem id_func_criterion : ∀ f A B, (f BinRelBtw A AND B) → ((is_functional f) ↔ (f ∘ f⁻¹ ⊆ id_ B)) := sorry
theorem id_tot_criterion : ∀ f A B, (f BinRelBtw A AND B) → ((is_total f A) ↔ (id_ A ⊆ f⁻¹ ∘ f)) := sorry
theorem id_inj_criterion : ∀ f A B, (f BinRelBtw A AND B) → ((is_injective f) ↔ (f⁻¹ ∘ f ⊆ id_ A)) := sorry
theorem id_surj_criterion : ∀ f A B, (f BinRelBtw A AND B) → ((is_surjective f B) ↔ (id_ B ⊆ f ∘ f⁻¹)) := sorry
theorem id_bijection_criterion :
∀ f A B, (f BinRelBtw A AND B) → ((f Bij A To B) ↔ ((f⁻¹ ∘ f = id_ A) ∧ (f ∘ f⁻¹ = id_ B))) := sorry
theorem bij_finv_f : ∀ f A B, (f Bij A To B) → (∀ x ∈ A; (f⁻¹⦅f⦅x⦆⦆) = x) := sorry
theorem bij_f_finv : ∀ f A B, (f Bij A To B) → (∀ x ∈ B; (f⦅f⁻¹⦅x⦆⦆) = x) := sorry
theorem bijimg_finv_f : ∀ f A B, (f Bij A To B) → (∀ X, (X ⊆ A) → (f⁻¹.[f.[X]] = X)) := sorry
theorem bijimg_f_finv : ∀ f A B, (f Bij A To B) → (∀ X, (X ⊆ B) → (f.[f⁻¹.[X]] = X)) := sorry



-- 35) Reversability, Left Reversability and Right Reversability and their criteria
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


theorem rev_criterion : ∀ f A B, (f Rev A To B) ↔ (f Bij A To B) := sorry
theorem leftrev_criterion: ∀ f A B, (f LeftRev A To B) ↔ ((f Inj A To B) ∧ (A ≠ ∅ ∨ B = ∅)) := sorry
theorem rightrev_criterion_AC_eq: choice_ax ↔ ∀ f A B, (f RightRev A To B) ↔ (f Surj A To B) := sorry


-- 36) Indexation with function, indexed famility, element of indexation, indexation· defintions
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
theorem fun_indexed_is_indexed :
∀ A I, (A IndxFun I) → (A Indx I) := sorry


-- 37) Indexed union and its properties
noncomputable def indexed_union (A I : Set) := ⋃ (A.[I])
syntax "⋃[" term "in" term "]" term "at" term : term
macro_rules
| `(⋃[ $i:term in $I:term ] $A:term at $i:term) => `(indexed_union $A $I)
theorem indexed_union_is_union :
∀ A I, (A Indx I) → ∀ x, (x ∈ (⋃[ i in I ] A at i)) ↔ (∃ i ∈ I; x ∈ (A _ i)) := sorry
theorem indexed_sub_indexed_union :
∀ A I, (A Indx I) → (∀ i ∈ I; (A _ i) ⊆ (⋃[ i in I ] A at i)) := sorry


-- 38) Indexed intersection and its properties
noncomputable def indexed_intersection (A I : Set) := ⋂ (A.[I])
syntax "⋂[" term "in" term "]" term "at" term : term
macro_rules
| `(⋂[ $i:term in $I:term ] $A:term at $i:term ) => `(indexed_intersection $A $I)
theorem indexed_intersection_is_intersection :
∀ A I, (I ≠ ∅) → (A IndxFun I) → ∀ x, (x ∈ (⋂[ i in I ] A at i)) ↔ (∀ i ∈ I; x ∈ (A _ i)) := sorry
theorem indexed_intersection_empty :
∀ A I, (I = ∅) → ((⋂[ i in I ] A at i) = ∅) := sorry
theorem indexed_intersection_sub_indexed:
∀ A I, (A IndxFun I) → (∀ i ∈ I; (⋂[ i in I ] A at i) ⊆ (A _ i)) := sorry




-- 39) Indexed disjoint union and its properties
noncomputable def indexed_disjoined_union (A I : Set) := {s ∈ ((⋃[ i in I ] A at i) × I) | ∃ i ∈ I; ∃ x ∈ (A _ i); s = (x, i)}
syntax "⨆[" term "in" term "]" term "at" term : term
macro_rules
| `( ⨆[$i:term in $I:term ] $A:term at $i:term) => `(indexed_disjoined_union $A $I)
theorem indexed_disjoined_union_is_disjoined_union :
∀ A I, (A IndxFun I) → (∀ s, (s ∈ ⨆[ i in I ] A at i) ↔ (∃ i ∈ I; ∃ x ∈ (A _ i); s = (x, i))) := sorry

theorem indexed_disjoined_union_pair_prop₁ :
∀ A I, (A IndxFun I) → (∀ x y, ((x, y) ∈ ⨆[ i in I ] A at i) ↔ (∃ i ∈ I; x ∈ (A _ i) ∧ y = i)) := sorry

theorem indexed_disjoined_union_pair_prop₂ :
∀ A I i, (A IndxFun I) → (i ∈ I) → (∀ x, ((x, i) ∈ ⨆[ i in I ] A at i) ↔ (x ∈ (A _ i))) := sorry

theorem indexed_disjoined_union_in :
∀ A I x i, (A IndxFun I) → (i ∈ I) → (x ∈ (A _ i)) → ((x, i) ∈ ⨆[ i in I ] A at i) := sorry

noncomputable def indexed_func (A) := lam_fun (dom A) (𝒫 (⋃ (rng A) × dom A)) (fun (i) => (A _ i) × {i})
syntax "DU" term : term
macro_rules
| `(DU $A) => `(indexed_func $A)


theorem DU_is_func : ∀ A I X, (A Fun I To X) → ((DU A) Fun I To (𝒫 (⋃ (rng A) × I))) ∧ (∀ i ∈ I; (DU A) _ i = (A _ i) × {i}) := sorry
theorem DU_indxfun : ∀ A I, (A IndxFun I) → ((DU A) IndxFun I) ∧ (∀ i ∈ I; (DU A) _ i = (A _ i) × {i}) := sorry


theorem indexed_disjoined_set_is_eq : ∀ A I i, (A IndxFun I) → (i ∈ I) → ((DU A) _ i) = {x ∈ ⨆[ i in I ] A at i | (π₂ x) = i} := sorry
theorem indexed_disjoined_set_subs : ∀ A I i, (A IndxFun I) → (i ∈ I) → ((DU A) _ i) ⊆ (⨆[ i in I ] A at i) := sorry
theorem indexed_disjoined_set_unin : ∀ A I i, (A IndxFun I) → (i ∈ I) → (x, i) ∈ ((DU A) _ i) := sorry
theorem indexed_disjoined_set_un : ∀ A I, (A IndxFun I) → (⨆[ i in I ] A at i) = (⋃[i in I] (DU A) at i) := sorry
theorem indexed_disjoined_set_int2 : ∀ A I i j, (A IndxFun I) → (i ∈ I) → (j ∈ I) → (i ≠ j) → ((DU A) _ i) ∩ ((DU A) _ j) = ∅ := sorry
theorem indexed_disjoined_set_int : ∀ A I, (∀ j, I ≠ {j}) → (A IndxFun I) → (⋂[i in I] (DU A) at i) = ∅ := sorry


-- 40) Indexed product and its properties
noncomputable def indexed_product (A I : Set) := {f ∈ ((⋃[ i in I ] A at i) ℙow (I)) | ∀ i ∈ I; f⦅i⦆ ∈ (A _ i)}
syntax "∏[" term "in" term "]" term "at" term : term
macro_rules
  |  `(∏[ $i:term in $I:term ] $A:term at $i:term ) => `(indexed_product $A $I)

theorem prod_pow : ∀ A I B, (A Indx I) → (∀ i ∈ I; (A _ i = B)) → (∏[ i in I ] A at i) = B ℙow I := sorry
theorem product_AC_eq : choice_ax ↔ (∀ A I, (A IndxFun I) → (∀ I ∈ I; (A _ I) ≠ ∅) → (∏[ i in I ] A at i) ≠ ∅) := sorry
