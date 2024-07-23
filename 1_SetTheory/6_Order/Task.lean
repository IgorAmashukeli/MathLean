import «Header»

-- Now we again consider arbitrary binary relations between A and B
-- But let A = B
-- (We consider binary relations on one set A)


-- 1) Some information about binary relations on one set
theorem bin_on_is_bin : ∀ A R, binary_relation_on A R → binary_relation R := sorry
theorem id_is_binon : ∀ A, ((id_ A) BinRelOn A) := sorry


-- 2) properties of binary relations on one set
def refl (R A : Set) : Prop := ∀ x ∈ A; (x . R . x)
def irrefl (R : Set) : Prop := ∀ x, ¬ (x . R . x)
def symm (R : Set) : Prop := ∀ x y, ((x . R . y) → (y . R . x))
def antisymm (R : Set) : Prop := ∀ x y, ((x . R . y) ∧ (y . R . x) → (x = y))
def asymm (R : Set) : Prop := ∀ x y, ((x . R . y) → ¬ (y . R . x))
def transit(R : Set) : Prop := ∀ x y z, (x . R . y) ∧ (y . R . z) → (x . R . z)
def str_conn (R A : Set) : Prop := ∀ x y ∈ A; ((x . R . y) ∨ (y . R . x))
def wkl_conn (R A : Set) : Prop := ∀ x y ∈ A; ((x ≠ y) → (x . R . y) ∨ (y . R . x))


-- 3) Criteria of the properties of binary relations on one sets
theorem refl_crit : ∀ A R, (R BinRelOn A) → ((refl R A) ↔ ((id_ A) ⊆ R)) := sorry
theorem irrefl_crit : ∀ A R, (R BinRelOn A) → ((irrefl R) ↔ (R ∩ (id_ A) = ∅)) := sorry
theorem symmetric_crit_sub_left : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R ⊆ R⁻¹)) := sorry
theorem symmetric_crit_sub_right : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R⁻¹ ⊆ R)) := sorry
theorem symmetric_crit_eq : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R = R⁻¹)) := sorry
theorem antisymmetric_crit : ∀ A R, (R BinRelOn A) → ((antisymm R) ↔ (R ∩ R⁻¹ ⊆ (id_ A))) := sorry
theorem asymmetric_crit : ∀ A R, (R BinRelOn A) → ((asymm R) ↔ (R ∩ R⁻¹ = ∅)) := sorry
theorem transitive_crit : ∀ A R, (R BinRelOn A) → ((transitR) ↔ (R ∘ R ⊆ R)) := sorry
theorem strongly_connected_crit : ∀ A R, (R BinRelOn A) → ((str_conn R A) ↔ ((A × A) ⊆ (R ∪ R⁻¹))) := sorry
theorem weakly_connected_crit : ∀ A R, (R BinRelOn A) → ((wkl_conn R A) ↔ (((A × A) \ (id_ A)) ⊆ (R ∪ R⁻¹))) := sorry


-- 4) Relations between properties
theorem assym_iff_antisymm_irrefl : ∀ A R, (R BinRelOn A) → ((asymm R) ↔ (antisymm R ∧ irrefl R)) := sorry
theorem strcon_iff_wkcon_refl : ∀ A R, (R BinRelOn A) → ((str_conn R A) ↔ (wkl_conn R A ∧ refl A R)) := sorry
theorem emp_refl_irrefl : ∀ A R, (R BinRelOn A) → ((A = ∅) ↔ (refl R A ∧ irrefl R)) := sorry
theorem emp_symm_asymm : ∀ A R, (R BinRelOn A) → ((R = ∅) ↔ (symm R ∧ asymm R)) := sorry
theorem trans_irrefl_antisymm : ∀ A R, (R BinRelOn A) → (transit R) → (irrefl R) → (antisymm R) := sorry
theorem trans_irrefl_asymm : ∀ A R, (R BinRelOn A) → (transit R) → (irrefl R) → (asymm R) := sorry
theorem refl_symm_antisymm : ∀ A R, (R BinRelOn A) → (((refl R A) ∧ (symm R) ∧ (antisymm R)) ↔ (R = (id_ A))) := sorry


-- 5) Inverse relation to the properties
theorem inv_binon : ∀ A R, (R BinRelOn A) → ((R⁻¹) BinRelOn A) := sorry
theorem refl_inv : ∀ A R, (R BinRelOn A) → ((refl R A) ↔ (refl (R⁻¹) A)) := sorry
theorem irrefl_inv : ∀ A R, (R BinRelOn A) → ((irrefl R) ↔ (irrefl (R⁻¹))) := sorry
theorem symm_inv : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (symm (R⁻¹))) := sorry
theorem antisymm_inv : ∀ A R, (R BinRelOn A) → ((antisymm R) ↔ (antisymm (R⁻¹))) := sorry
theorem asymm_inv : ∀ A R, (R BinRelOn A) → ((asymm R) ↔ (asymm (R⁻¹))) := sorry
theorem transit_inv : ∀ A R, (R BinRelOn A) → ((transit R) ↔ (transit (R⁻¹))) := sorry
theorem str_conn_inv : ∀ A R, (R BinRelOn A) → ((str_conn R A) ↔ (str_conn (R⁻¹) A)) := sorry
theorem wkl_conn_inv : ∀ A R, (R BinRelOn A) → ((wkl_conn R A) ↔ (wkl_conn (R⁻¹) A)) := sorry


-- 6) Composition relation to the properties
theorem compos_binon : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → ((P ∘ Q) BinRelOn A) := sorry
theorem refl_compos_char : ∀ A P Q, (refl P A) → (refl Q A) → (refl (P ∘ Q) A) := sorry
theorem refl_compos_prop : ∀ A P Q, (refl (P ∘ Q) A) → ((is_surjective P A) ∧ (is_total Q A)) := sorry
theorem symm_compos_prop : ∀ P Q, (P BinRelOn A) → (Q BinRelOn A) → (symm P) → (symm Q) → (((P ∘ Q)⁻¹) = (Q ∘ P)) := sorry


-- 7) Subset relation to the properties
theorem subs_binon : ∀ A P Q, (Q BinRelOn A) → (P ⊆ Q) → (P BinRelOn A) := sorry
theorem refl_subs : ∀ A P Q, (refl P A) → (P ⊆ Q) → (refl Q A) := sorry
theorem irrefl_subs : ∀ P Q, (irrefl Q) → (P ⊆ Q) → (irrefl P) := sorry
theorem antisymm_subs : ∀ P Q, (antisymm Q) → (P ⊆ Q) → (antisymm P) := sorry
theorem asymm_subs : ∀ P Q, (asymm Q) → (P ⊆ Q) → (asymm P) := sorry
theorem str_conn_subs : ∀ A P Q, (P ⊆ Q) → (str_conn P A) → (str_conn Q A) := sorry
theorem wkl_conn_subs : ∀ A P Q, (P ⊆ Q) → (wkl_conn P A) → (wkl_conn Q A) := sorry


-- 8) Union relations to the properties
theorem un_binon : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → ((P ∪ Q) BinRelOn A) := sorry
theorem refl_un_left : ∀ A P Q, (refl P A) → (refl (P ∪ Q) A) := sorry
theorem refl_un_right : ∀ A P Q, (refl Q A) → (refl (P ∪ Q) A) := sorry
theorem irrefl_un : ∀ P Q, (irrefl P) → (irrefl Q) → (irrefl (P ∪ Q)) := sorry
theorem symm_un : ∀ P Q, (symm P) → (symm Q) → (symm (P ∪ Q)) := sorry
theorem str_un : ∀ A P Q, (str_conn P A) → (str_conn Q A) → (str_conn (P ∪ Q) A) := sorry
theorem str_con_un_left : ∀ A P Q, (str_conn P A) → (str_conn (P ∪ Q) A) := sorry
theorem str_con_un_right : ∀ A P Q, (str_conn Q A) → (str_conn (P ∪ Q) A) := sorry
theorem wkl_con_un_left : ∀ A P Q, (wkl_conn P A) → (wkl_conn (P ∪ Q) A) := sorry
theorem wkl_con_un_right : ∀ A P Q, (wkl_conn Q A) → (wkl_conn (P ∪ Q) A) := sorry


-- 9) Intersection relation to the properties
theorem int_binon_left : ∀ A P Q, (P BinRelOn A) → ((P ∩ Q) BinRelOn A) := sorry
theorem int_binon_right : ∀ A P Q, (Q BinRelOn A) → ((P ∩ Q) BinRelOn A) := sorry
theorem refl_int_left : ∀ A P Q, (refl P A) → (refl Q A) → (refl (P ∩ Q) A) := sorry
theorem irrefl_inr_right : ∀ P Q, (irrefl Q) → (irrefl (P ∩ Q)) := sorry
theorem symm_inr : ∀ P Q, (symm P) → (symm Q) → (symm (P ∩ Q)) := sorry
theorem antisym_inr : ∀ P Q, (antisymm P) → (antisymm Q) → (antisymm (P ∩ Q)) := sorry
theorem antisym_inr_left : ∀ P Q, (antisymm P) → (antisymm (P ∩ Q)) := sorry
theorem antisym_inr_right : ∀ P Q, (antisymm Q) → (antisymm (P ∩ Q)) := sorry
theorem trans_inr : ∀ P Q, (transit P) → (transit Q) → (transit (P ∩ Q)) := sorry


-- 10) Difference relation to the properties
theorem diff_binon : ∀ A P Q, (P BinRelOn A) → ((P \ Q) BinRelOn A) := sorry
theorem irrefl_diff : ∀ P Q, (irrefl P) → (irrefl (P \ Q)) := sorry
theorem symm_diff : ∀ P Q, (symm P) → (symm Q) → (symm (P \ Q)) := sorry
theorem asymm_diff : ∀ P Q, (asymm P) → (asymm (P \ Q)) := sorry
theorem antisymm_diff : ∀ P Q, (antisymm P) → (antisymm (P \ Q)) := sorry


-- 11) Complement relation to the properties
theorem compl_binon : ∀ A P, ((comp A A P) BinRelOn A) := sorry
theorem symm_compl : ∀ A P, (symm P) → (symm (comp A A P)) := sorry


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
theorem spo_antisymm : ∀ A R, (R SPO A) → antisymm R := sorry
theorem spo_asymm : ∀ A R, (R SPO A) → asymm R := sorry

-- 15) relations between strict and non strict order
noncomputable def str (A R) := R \ (id_ A)
noncomputable def nonstr (A R) := R ∪ (id_ A)
theorem spo_then_nspo : ∀ A R, (R SPO A) → ((nonstr A R) NSPO A) := sorry
theorem nspo_then_spo : ∀ A R, (R NSPO A) → ((str A R) SPO A) := sorry
theorem str_nonstr_id : ∀ A R, (R SPO A) → ((str A (nonstr A R)) = R) := sorry
theorem nonstr_str_id : ∀ A R, (R NSPO A) → ((nonstr A (str A R)) = R) := sorry
noncomputable def SPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R SPO A) }
noncomputable def NSPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R NSPO A) }
theorem SPOS_NSPOS_equinum : ∀ A, (SPOS A) ~ (NSPOS A) := sorry


-- 16) partial order (strict and non strict) and its equivalent criteria
def is_partial_order (A R₁ R₂ : Set) : Prop := A ≠ ∅ ∧ (R₁ SPO A) ∧ (R₂ = nonstr A R₁)
syntax term "with" term "PO" term  : term
macro_rules
| `($R₁:term with $R₂:term PO $A:term) => `(is_partial_order $A $R₁ $R₂)
theorem part_ord_nspo_crit : ∀ A R₁ R₂, (R₁ with R₂ PO A) ↔ ((A ≠ ∅) ∧ (R₂ NSPO A) ∧ (R₁ = str A R₂)) := sorry
theorem part_ord_crit :
∀ A R₁ R₂, (R₁ with R₂ PO A) ↔ (A ≠ ∅ ∧ (R₁ SPO A) ∧ (R₂ NSPO A) ∧ (R₂ = nonstr A R₁) ∧ (R₁ = str A R₂)) := sorry


-- 17) inverse of a PO and intersection of two PO is a PO
theorem inv_is_PO : ∀ A R₁ R₂, (R₁ with R₂ PO A) → ((R₁⁻¹) with (R₂⁻¹) PO A) := sorry
theorem inter_is_PO : ∀ A P₁ P₂, (P₁ with P₂ PO A) → (Q₁ with Q₂ PO A) → ((P₁ ∩ Q₁) with (P₂ ∩ Q₂) PO A) := sorry


-- 18) partial order pair properties
def noncomparable (R x y : Set) : Prop := (¬ (x . R . y)) ∧ (¬ (y . R . x))
theorem part_ord_pair_prop :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y ∈ A; ((x . R₁ . y) ↔ ((x . R₂ . y) ∧ x ≠ y)) ∧ ((x . R₂ . y) ↔ ((x . R₁ . y) ∧ x = y))) := sorry
theorem part_ord_pair_prop_R₁_A :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₁ . y) → ((x ∈ A) ∧ (y ∈ A))) := sorry
theorem part_ord_pair_prop_R₂_A :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₂ . y) → ((x ∈ A) ∧ (y ∈ A))) := sorry
theorem part_ord_pair_prop_R₁R₂ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → ∀ x y, ((x . R₁ . y) → ((x . R₂ . y))) := sorry
theorem part_ord_pair_prop_R₁neq : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y ∈ A; (x . R₁ . y) → (x ≠ y)) := sorry
theorem part_ord_pair_prop_eqR₂ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y ∈ A; (x = y) → (x . R₂ . y)) := sorry
theorem part_ord_pair_prop_neqR₂R₁ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₂ . y) ∧ (x ≠ y)) → ((x . R₁ . y)) := sorry
theorem irrefl_R₁ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x, ¬ (x . R₁ . x)) := sorry
theorem assym_R₁ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₁ . y) → (¬ (y . R₁ . x))) := sorry
theorem refl_R₂ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x ∈ A; (x . R₂ . x)) := sorry
theorem antisymm_R₂ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₂ . y) → (y . R₂ . x) → (x = y)) := sorry
theorem trans_R₂ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y z, (x . R₂ . y) → (y . R₂ . z) → (x . R₂ . z)) := sorry
theorem stabil_R₂ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y z, (x . R₂ . y) → (y . R₂ . z) → (x = z) → ((x = y) ∧ (y = z))) := sorry
theorem no_symm_R₁_R₂ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, ¬ ((x . R₁ . y) ∧ (y . R₂ . x))) := sorry
theorem PO_noncomp : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y ∈ A; (noncomparable R₂ x y) ↔ (x ≠ y ∧ (noncomparable R₁ x y))) := sorry


-- 19) (𝒫 A, ⊊, ⊆) is a partial order
noncomputable def sub_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊆ C ∧ z = (B, C) }
noncomputable def subneq_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊊ C ∧ z = (B, C) }
theorem NSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (sub_binrel A) ↔ (B ⊆ C) := sorry
theorem SNSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (subneq_binrel A) ↔ (B ⊊ C) := sorry
theorem boolean_PO : ∀ A, ((subneq_binrel A) with ((sub_binrel A)) PO (𝒫 A)) := sorry


-- 20) maximal (minimal) and maximum (minimim) elements, maximal and minimal sets
def is_maximal (R x : Set) : Prop := ∀ y, ¬ (x . R . y)
def is_minimal (R x : Set) : Prop := ∀ y, ¬ (y . R . x)
def is_maximal_sub (R B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (x . R . y))
def is_minimal_sub (R B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (y . R . x))
def is_maximum (R A x : Set) : Prop := ∀ y ∈ A; (y . R . x)
def is_minimum (R A x : Set) : Prop := ∀ y ∈ A; (x . R . y)
def is_maximum_sub (R B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (y . R . x))
def is_minimum_sub (R B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (x . R . y))
noncomputable def max_set (A R) := {z ∈ A | is_maximal R z}
noncomputable def min_set (A R) := {z ∈ A | is_minimal R z}
noncomputable def max_set_sub (A B R) := {z ∈ A | is_maximal_sub R B z }
noncomputable def min_set_sub (A B R) := {z ∈ A | is_minimal_sub R B z }

-- 21) basic properties of maxsets and minsets
theorem max_set_is_max_set : ∀ A R x, ((x ∈ (max_set A R)) ↔ (x ∈ A ∧ is_maximal R x)) := sorry
theorem min_set_is_min_set : ∀ A R x, ((x ∈ (min_set A R)) ↔ (x ∈ A ∧ is_minimal R x)) := sorry
theorem max_set_sub_is_max_set_sub : ∀ A B R x, (B ⊆ A) → ((x ∈ (max_set_sub A B R)) ↔ (is_maximal_sub R B x)) := sorry
theorem min_set_sub_is_min_set_sub : ∀ A B R x, (B ⊆ A) → ((x ∈ (min_set_sub A B R)) ↔ (is_minimal_sub R B x)) := sorry
theorem max_sub_A_is_max_al : ∀ A R, ∀ x ∈ A; (is_maximal R x) ↔ (is_maximal_sub R A x) := sorry
theorem min_sub_A_is_min_al : ∀ A R, ∀ x ∈ A; (is_minimal R x) ↔ (is_minimal_sub R A x) := sorry
theorem max_sub_A_is_max_um : ∀ A R, ∀ x ∈ A; (is_maximum R A x) ↔ (is_maximum_sub R A x) := sorry
theorem min_sub_A_is_min_um : ∀ A R, ∀ x ∈ A; (is_minimum R A x) ↔ (is_minimum_sub R A x) := sorry
theorem max_set_sub_A_is_max_set : ∀ A R, (max_set_sub A A R = max_set A R) := sorry
theorem min_set_sub_A_is_min_set : ∀ A R, (max_set_sub A A R = max_set A R) := sorry


-- 22) properites of maximal/minimal, maximum/minimum, maxset/minset with respect to inverse
theorem min_max_inv_al : ∀ R x, (BinRel R) → ((is_minimal R x) ↔ (is_maximal (R⁻¹) x)) := sorry
theorem max_min_inv_al : ∀ R x, (BinRel R) → ((is_maximal R x) ↔ (is_minimal (R⁻¹) x)) := sorry
theorem min_max_sub_inv_al : ∀ R B x, (BinRel R) → ((is_minimal_sub R B x) ↔ (is_maximal_sub (R⁻¹) B x)) := sorry
theorem max_min_sub_inv_al : ∀ R B x, (BinRel R) → ((is_maximal_sub R B x) ↔ (is_minimal_sub (R⁻¹) B x)) := sorry
theorem min_max_inv_um : ∀ A R x, (BinRel R) → ((is_minimum R A x) ↔ (is_maximum (R⁻¹) A x)) := sorry
theorem max_min_inv_um : ∀ A R x, (BinRel R) → ((is_maximum R A x) ↔ (is_minimum (R⁻¹) A x)) := sorry
theorem min_max_sub_inv_um : ∀ R B x, (BinRel R) → ((is_minimum_sub R B x) ↔ (is_maximum_sub (R⁻¹) B x)) := sorry
theorem max_min_sub_inv_um : ∀ R B x, (BinRel R) → ((is_maximum_sub R B x) ↔ (is_minimum_sub (R⁻¹) B x)) := sorry
theorem min_max_set_inv_sub : ∀ A B R, (BinRel R) → (B ⊆ A) → (max_set_sub A B R = min_set_sub A B (R⁻¹)) := sorry
theorem max_min_set_inv_sub : ∀ A B R, (BinRel R) → (B ⊆ A) → (min_set_sub A B R = max_set_sub A B (R⁻¹)) := sorry
theorem min_max_set_inv : ∀ A R, (BinRel R) → (max_set A R = min_set A (R⁻¹)) := sorry
theorem max_min_set_inv : ∀ A R, (BinRel R) → (min_set A R = max_set A (R⁻¹)) := sorry


-- 23) main properties of maximal/minimal, maximum/minimum, maxset/minset in PO set
theorem max_um_is_al_sub : ∀ A R₁ R₂ B x, (R₁ with R₂ PO A) → (is_maximum_sub R₂ B x) → (is_maximal_sub R₁ B x) := sorry
theorem min_um_is_al_sub : ∀ A R₁ R₂ B x, (R₁ with R₂ PO A) → (is_minimum_sub R₂ B x) → (is_minimal_sub R₁ B x) := sorry
theorem max_um_is_al : ∀ A R₁ R₂ x, (R₁ with R₂ PO A) → (is_maximum R₂ A x) → (is_maximal R₁ x) := sorry
theorem min_um_is_al : ∀ A R₁ R₂ x, (R₁ with R₂ PO A) → (is_minimum R₂ A x) → (is_minimal R₁ x) := sorry
theorem max_um_unique_sub : ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_maximum_sub R₂ B x) → (is_maximum_sub R₂ B y) → (x = y) := sorry
theorem min_um_unique_sub : ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_minimum_sub R₂ B x) → (is_minimum_sub R₂ B y) → (x = y) := sorry
theorem max_um_unique : ∀ A R₁ R₂ x y, (R₁ with R₂ PO A) → (is_maximum R₂ A x) → (is_maximum R₂ A y) → (x = y) := sorry
theorem min_um_unique : ∀ A R₁ R₂ x y, (R₁ with R₂ PO A) → (is_minimum R₂ A x) → (is_minimum R₂ A y) → (x = y) := sorry
theorem max_um_maxset_singl_sub :
∀ A R₁ R₂ B x, (R₁ with R₂ PO A) → (B ⊆ A) → (is_maximum_sub R₂ B x) → (max_set_sub A B R₁ = {x}) := sorry
theorem min_um_minset_singl_sub :
∀ A R₁ R₂ B x, (R₁ with R₂ PO A) → (B ⊆ A) → (is_minimum_sub R₂ B x) → (min_set_sub A B R₁ = {x}) := sorry


-- 24) upper and lower bounds of a Set and their basic properties
def is_upper_bound (A B R x : Set) := x ∈ A ∧ ∀ y ∈ B; (y . R . x)
def is_lower_bound (A B R x : Set) := x ∈ A ∧ ∀ y ∈ B; (x . R . y)

noncomputable def lower_bounds (A B R) := {z ∈ A | is_lower_bound A B R z}
noncomputable def upper_bounds (A B R) := {z ∈ A | is_upper_bound A B R z}

syntax term "LowBou" term "in" term : term
syntax term "UppBou" term "in" term : term
macro_rules
| `($R:term LowBou $B:term in $A:term) => `(lower_bounds $A $B $R)
| `($R:term UppBou $B:term in $A:term) => `(upper_bounds $A $B $R)

theorem inv_low_upp_bou : ∀ A B R, (BinRel R) → ∀ x, (is_upper_bound A B R x) ↔ (is_lower_bound A B (R⁻¹) x) := sorry
theorem inv_upp_low_bou : ∀ A B R, (BinRel R) → ∀ x, (is_lower_bound A B R x) ↔ (is_upper_bound A B (R⁻¹) x) := sorry

theorem low_bou_set_is_low_bou : ∀ A B R, ∀ x, (x ∈ (R LowBou B in A) ↔ (is_lower_bound A B R x)) := sorry
theorem upp_bou_set_is_upp_bou : ∀ A B R, ∀ x, (x ∈ (R UppBou B in A) ↔ (is_upper_bound A B R x)) := sorry
