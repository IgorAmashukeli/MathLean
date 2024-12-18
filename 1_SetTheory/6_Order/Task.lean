import «Header»

-- Now we again consider arbitrary binary relations between A and B
-- But let A = B
-- (We consider binary relations on one set A)


-- 1) Some information about binary relations on one set and specification on binary relation
theorem bin_on_is_bin : ∀ A R, binary_relation_on A R → binary_relation R := sorry
theorem id_is_binon : ∀ A, ((id_ A) BinRelOn A) := sorry
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
theorem refl_crit : ∀ A R, (R BinRelOn A) → ((refl R A) ↔ ((id_ A) ⊆ R)) := sorry
theorem irrefl_crit : ∀ A R, (R BinRelOn A) → ((irrefl R) ↔ (R ∩ (id_ A) = ∅)) := sorry
theorem symmetric_crit_sub_left : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R ⊆ R⁻¹)) := sorry
theorem symmetric_crit_sub_right : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R⁻¹ ⊆ R)) := sorry
theorem symmetric_crit_eq : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (R = R⁻¹)) := sorry
theorem antisymmetric_crit : ∀ A R, (R BinRelOn A) → ((antisymm R) ↔ (R ∩ R⁻¹ ⊆ (id_ A))) := sorry
theorem asymmetric_crit : ∀ A R, (R BinRelOn A) → ((asymm R) ↔ (R ∩ R⁻¹ = ∅)) := sorry
theorem transitive_crit : ∀ A R, (R BinRelOn A) → ((transit R) ↔ (R ∘ R ⊆ R)) := sorry
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
theorem symm_compos_prop : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → (symm P) → (symm Q) → (((P ∘ Q)⁻¹) = (Q ∘ P)) := sorry


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
theorem irrefl_int_right : ∀ P Q, (irrefl Q) → (irrefl (P ∩ Q)) := sorry
theorem symm_int : ∀ P Q, (symm P) → (symm Q) → (symm (P ∩ Q)) := sorry
theorem antisym_int : ∀ P Q, (antisymm P) → (antisymm Q) → (antisymm (P ∩ Q)) := sorry
theorem antisym_int_left : ∀ P Q, (antisymm P) → (antisymm (P ∩ Q)) := sorry
theorem antisym_int_right : ∀ P Q, (antisymm Q) → (antisymm (P ∩ Q)) := sorry
theorem trans_int : ∀ P Q, (transit P) → (transit Q) → (transit (P ∩ Q)) := sorry


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

noncomputable def cartesian2_coordinate_part_ord (𝓐 𝓑) := ⁅setPO(𝓐) × setPO(𝓑); le_cart 𝓐 𝓑; leq_cart 𝓐 𝓑⁆
syntax term "Cart2CordPO" term : term
macro_rules
| `($𝓐 Cart2CordPO $𝓑) => `(cartesian2_coordinate_part_ord $𝓐 $𝓑)




theorem setPO_is_setPO : ∀ A R₁ R₂, (setPO(⁅A; R₁; R₂⁆) = A) := sorry
theorem lessPO_is_lessPO :  ∀ A R₁ R₂, (≺(⁅A; R₁; R₂⁆) = R₁) := sorry
theorem lesseqPO_is_lesseqPO : ∀ A R₁ R₂, (≼(⁅A; R₁; R₂⁆) = R₂) := sorry
theorem triple_po_is_po : ∀ 𝓐, (PartOrd 𝓐) → (is_partial_order setPO(𝓐) ≺(𝓐) ≼(𝓐)) := sorry
theorem po_is_triple_po : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (PartOrd (⁅A; R₁; R₂⁆)) := sorry
theorem po_less_more : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≺(𝓐)) . y) ↔ (y . ≻(𝓐) . x) := sorry
theorem po_lesseq_moreeq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≼(𝓐)) . y) ↔ (y . ≽(𝓐) . x) := sorry
theorem po_emp : ∀ 𝓐, (PartOrd 𝓐) → (setPO(𝓐) ≠ ∅) := sorry

-- 17) sub of PO, inverse of a PO, intersection of two PO, cartesian product of two PO
theorem inv_is_PO : ∀ 𝓐, (PartOrd 𝓐) → (PartOrd (invPO 𝓐) ) := sorry
theorem sub_is_PO : ∀ 𝓐 B, (B ≠ ∅) → (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (PartOrd (𝓐 SubsPO B)) := sorry
theorem inter_is_PO_PO :
∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (setPO(𝓐) = setPO(𝓑)) → (PartOrd (𝓐 InterPO 𝓑)) := sorry
theorem inv_PO_less : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≺(invPO 𝓐)) . y) ↔ (y . (≺(𝓐)) . x) := sorry
theorem inv_PO_lesseq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≼(invPO 𝓐)) . y) ↔ (y . (≼(𝓐)) . x)  := sorry
theorem cart_PO_PO : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (PartOrd (𝓐 Cart2CordPO 𝓑)) := sorry


-- 18) partial order pair properties
def noncomparable_nonstr (𝓐 x y : Set) : Prop := (¬ (x . (≼(𝓐)) . y)) ∧ (¬ (x . (≽(𝓐)) . y))
def noncomparable_str (𝓐 x y : Set) : Prop := (¬ (x . (≺(𝓐)) . y)) ∧ (¬ (x . (≻(𝓐)) . y))
theorem part_ord_pair_prop :
∀ 𝓐, (PartOrd 𝓐) → (∀ x y ∈ (setPO(𝓐)); ((x . (≺(𝓐)) . y) ↔ ((x . ≼(𝓐) . y) ∧ x ≠ y)) ∧
((x . (≼(𝓐)) . y) ↔ ((x . (≺(𝓐)) . y) ∨ x = y))) := sorry
theorem par_ord_pair_prop_R₁_A : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≺(𝓐)) . y) → ((x ∈ (setPO(𝓐))) ∧ (y ∈ (setPO(𝓐))))) := sorry
theorem par_ord_pair_prop_R₂_A : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≼(𝓐)) . y) → ((x ∈ (setPO(𝓐))) ∧ (y ∈ (setPO(𝓐))))) := sorry
theorem part_ord_pair_prop_R₁R₂ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . ≺(𝓐) . y) → (x . (≼(𝓐)) . y) := sorry
theorem part_ord_pair_prop_R₁neq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y ∈ (setPO(𝓐)); (x . ≺(𝓐) . y) → (x ≠ y) := sorry
theorem part_ord_pair_prop_eqR₂ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y ∈ (setPO(𝓐)); (x = y) → (x . (≼(𝓐)) . y) := sorry
theorem part_ord_pair_prop_neqR₂R₁ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, ((x . (≼(𝓐)) . y) ∧ (x ≠ y)) → (x . (≺(𝓐)) . y) := sorry
theorem irrefl_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x, ¬ (x . (≺(𝓐)) . x)) := sorry
theorem asymm_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≺(𝓐)) . y) → ¬ (y . (≺(𝓐)) . x)) := sorry
theorem refl_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x ∈ (setPO(𝓐)); (x . (≼(𝓐)) . x)) := sorry
theorem antisymm_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . x) → (x = y)) := sorry
theorem trans_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x . (≼(𝓐)) . z)) := sorry
theorem stabil_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x = z) → ((x = y) ∧ (y = z))) := sorry
theorem no_symm_R₁_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, ¬ ((x . (≺(𝓐)) . y) ∧ (y . (≼(𝓐)) . x))) := sorry
theorem PO_noncomp :
∀ 𝓐, (PartOrd 𝓐) → (∀ x y ∈ (setPO(𝓐)); (noncomparable_nonstr 𝓐 x y) ↔ (x ≠ y ∧ (noncomparable_str 𝓐 x y))) := sorry



-- 19) (𝒫 A, ⊊, ⊆) is a partial order



noncomputable def sub_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊆ C ∧ z = (B, C) }
noncomputable def subneq_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊊ C ∧ z = (B, C) }
noncomputable def boolean_PO_set (A) := ⁅(𝒫 A); (subneq_binrel A); (sub_binrel A)⁆
syntax "BoolPO" term : term
macro_rules
| `(BoolPO $A:term) => `(boolean_PO_set $A)

theorem NSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (sub_binrel A) ↔ (B ⊆ C) := sorry
theorem SNSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (subneq_binrel A) ↔ (B ⊊ C) := sorry
theorem boolean_PO : ∀ A, (PartOrd (BoolPO A)) := sorry


-- 20) maximal (minimal) and maximum (minimim) elements, maximal and minimal sets
def is_maximal (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (x . (≺(𝓐)) . y))
def is_minimal (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (y . (≺(𝓐)) . y))
def is_maximum (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (y . (≼(𝓐)) . x))
def is_minimum (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (x . (≼(𝓐)) . y))


noncomputable def max_set (𝓐 B) := {z ∈ B | is_maximal 𝓐 B z }
noncomputable def min_set (𝓐 B) := {z ∈ B | is_minimal 𝓐 B z }

-- 21) basic properties of maxsets and minsets
theorem max_set_is_max_set : ∀ 𝓐 B x, ((x ∈ max_set 𝓐 B) ↔ (is_maximal 𝓐 B x)) := sorry
theorem min_set_is_min_set : ∀ 𝓐 B x, ((x ∈ min_set 𝓐 B) ↔ (is_minimal 𝓐 B x)) := sorry


-- 22) properites of maximal/minimal, maximum/minimum, maxset/minset with respect to inverse
theorem min_max_inv_al : ∀ 𝓐 B x, ((is_minimal 𝓐 B x) ↔ (is_maximal (invPO 𝓐) B x)) := sorry
theorem max_min_inv_al : ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_maximal 𝓐 B x) ↔ (is_minimal (invPO 𝓐) B x)) := sorry
theorem min_max_inv_um :  ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_minimum 𝓐 B x) ↔ (is_maximum (invPO 𝓐) B x)) := sorry
theorem max_min_inv_um :  ∀ 𝓐 B x, ((is_maximum 𝓐 B x) ↔ (is_minimum (invPO 𝓐) B x)) := sorry
theorem min_max_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (max_set 𝓐 B = min_set (invPO 𝓐) B) := sorry
theorem max_min_set_inv : ∀ 𝓐 B, (min_set 𝓐 B = max_set (invPO 𝓐) B) := sorry

-- 23) maximal/minimal, maximum/minimum and subset
theorem max_al_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_maximal 𝓐 B x) → (x ∈ C) → (is_maximal 𝓐 C x) := sorry
theorem min_al_subsets_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_minimal 𝓐 B x) → (x ∈ C) → (is_minimal 𝓐 C x) := sorry
theorem max_um_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_maximum 𝓐 B x) → (x ∈ C) → (is_maximum 𝓐 C x) := sorry
theorem min_um_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_minimum 𝓐 B x) → (x ∈ C) → (is_minimum 𝓐 C x) := sorry
theorem min_um_sub_cmp : ∀ 𝓐 B C x y, (C ⊆ B) → (is_minimum 𝓐 B x) → (is_minimum 𝓐 C y) → (x . ≼(𝓐) . y) := sorry
theorem max_um_sub_cmp : ∀ 𝓐 B C x y, (C ⊆ B) → (is_maximum 𝓐 B x) → (is_maximum 𝓐 C y) → (y . ≼(𝓐) . x) := sorry


-- 24) maximal/minimal, maximum/minimum and intersection
theorem max_al_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_maximal 𝓐 (B _ i) x) → (is_maximal 𝓐 (⋂[ i in I ] B at i) x) := sorry
theorem min_al_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_minimal 𝓐 (B _ i) x) → (is_minimal 𝓐 (⋂[ i in I ] B at i) x) := sorry
theorem max_um_inter_prop :
∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_maximum 𝓐 (B _ i) x) → (is_maximum 𝓐 (⋂[ i in I ] B at i) x) := sorry
theorem min_um_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_minimum 𝓐 (B _ i) x) → (is_minimum 𝓐 (⋂[ i in I ] B at i) x) := sorry

theorem um_min_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (is_minimum 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_minimum 𝓐 ((B _ i)) y) → (y . ≼(𝓐) . x) := sorry
 theorem um_max_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (is_maximum 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_maximum 𝓐 ((B _ i)) y) → (x . ≼(𝓐) . y) := sorry


-- 25) maximal/minimal, maximum/minimum and union

theorem max_al_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_maximal 𝓐 (B _ i) x) → (is_maximal 𝓐 (⋃[i in I] B at i) x) := sorry
theorem min_al_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_minimal 𝓐 (B _ i) x) → (is_minimal 𝓐 (⋃[i in I] B at i) x) := sorry
theorem max_um_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_maximum 𝓐 (B _ i) x) → (is_maximum 𝓐 (⋃[i in I] B at i) x) := sorry
theorem min_um_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_minimum 𝓐 (B _ i) x) → (is_minimum 𝓐 (⋃[i in I] B at i) x) := sorry



-- 26) maximal/minimal, maximum/minimum properties in PO set
theorem max_um_is_al : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_maximum 𝓐 B x) → (is_maximal 𝓐 B x) := sorry
theorem min_um_is_al : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_minimum 𝓐 B x) → (is_minimal 𝓐 B x) := sorry
theorem max_um_unique_sub : ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_maximum R₂ B x) → (is_maximum R₂ B y) → (x = y) := sorry
theorem min_um_unique_sub : ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_minimum R₂ B x) → (is_minimum R₂ B y) → (x = y) := sorry
theorem max_um_maxset_singl : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_maximum 𝓐 B x) → (max_set 𝓐 B = {x}) := sorry
theorem min_um_minset_singl : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_minimum 𝓐 B x) → (min_set 𝓐 B = {x}) := sorry



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
theorem inv_low_upp_bou : ∀ 𝓐 B x, (is_upper_bound 𝓐 B x) ↔ (is_lower_bound (invPO 𝓐) B x) := sorry
theorem inv_upp_low_bou : ∀ 𝓐 B, (PartOrd 𝓐) → ∀ x, (is_lower_bound 𝓐 B x) ↔ (is_upper_bound (invPO 𝓐) B x) := sorry
theorem low_bou_set_is_low_bou : ∀ 𝓐 B, ∀ x, (x ∈ (𝓐 ▾ B) ↔ (is_lower_bound 𝓐 B x)) := sorry
theorem upp_bou_set_is_upp_bou : ∀ 𝓐 B, ∀ x, (x ∈ (𝓐 ▴ B) ↔ (is_upper_bound 𝓐 B x)) := sorry
theorem low_bou_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 ▾ B) = ((invPO 𝓐) ▴ B) := sorry
theorem upp_bou_set_inv :  ∀ 𝓐 B, (𝓐 ▴ B) = ((invPO 𝓐) ▾ B) := sorry
theorem max_um_upp_bou : ∀ 𝓐 B x, (B ⊆ (setPO(𝓐))) → (is_maximum 𝓐 B x) → (is_upper_bound 𝓐 B x) := sorry
theorem min_um_low_bou : ∀ 𝓐 B x, (B ⊆ (setPO(𝓐))) → (is_minimum 𝓐 B x) → (is_lower_bound 𝓐 B x) := sorry
theorem upp_bou_max_um : ∀ 𝓐 B x, (is_upper_bound 𝓐 B x) → (x ∈ B) → (is_maximum 𝓐 B x) := sorry
theorem low_bou_min_um : ∀ 𝓐 B x, (is_lower_bound 𝓐 B x) → (x ∈ B) → (is_minimum 𝓐 B x) := sorry
theorem upp_bou_subset : ∀ 𝓐 B C x, (B ⊆ C) → (is_upper_bound 𝓐 C x) → (is_upper_bound 𝓐 B x) := sorry
theorem low_bou_subset : ∀ 𝓐 B C x, (B ⊆ C) → (is_lower_bound 𝓐 C x) → (is_lower_bound 𝓐 B x) := sorry
theorem upp_bou_set_subset : ∀ 𝓐 B C, (B ⊆ C) → (𝓐 ▴ C) ⊆ (𝓐 ▴ B) := sorry
theorem low_bou_set_subset : ∀ 𝓐 B C, (B ⊆ C) → (𝓐 ▾ C) ⊆ (𝓐 ▾ B) := sorry
theorem sub_upp_low : ∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (B ⊆ (𝓐 ▴ (𝓐 ▾ B))) := sorry
theorem sub_low_upp :∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (B ⊆ (𝓐 ▾ (𝓐 ▴ B))) := sorry
theorem upp_low_upp_is_low : ∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (𝓐 ▴ (𝓐 ▾ (𝓐 ▴ B))) = (𝓐 ▴ B) := sorry
theorem low_upp_low_is_upp : ∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (𝓐 ▾ (𝓐 ▴ (𝓐 ▾ B))) = (𝓐 ▾ B) := sorry
theorem upp_bou_inter :
∀ 𝓐 B I x, (B IndxFun I) → (∃ i ∈ I; is_upper_bound 𝓐 (B _ i) x) → (is_upper_bound 𝓐 (⋂[ i in I ] B at i) x) := sorry
theorem low_bou_inter :
∀ 𝓐 B I x, (B IndxFun I) → (∃ i ∈ I; is_lower_bound 𝓐 (B _ i) x) → (is_lower_bound 𝓐 (⋂[ i in I ] B at i) x) := sorry
theorem upp_bou_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_upper_bound 𝓐 (B _ i) x) → (is_upper_bound 𝓐 (⋃[i in I] B at i) x) := sorry
theorem low_bou_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_lower_bound 𝓐 (B _ i) x) → (is_lower_bound 𝓐 (⋃[i in I] B at i) x) := sorry


-- 28) supremum and infimum
def is_supremum (𝓐 B x : Set) : Prop := is_minimum 𝓐 (𝓐 ▴ B) x
def is_infimum (𝓐 B x : Set) : Prop := is_maximum 𝓐 (𝓐 ▾ B) x
theorem sup_is_upp : ∀ 𝓐 B x, is_supremum 𝓐 B x → (is_upper_bound 𝓐 B x) := sorry
theorem inf_is_low : ∀ 𝓐 B x, is_infimum 𝓐 B x → (is_lower_bound 𝓐 B x) := sorry
theorem sup_is_sm_upp : ∀ 𝓐 B x, is_supremum 𝓐 B x → (∀ y, (is_upper_bound 𝓐 B y) → (x . (≼(𝓐)) . y)) := sorry
theorem inf_is_big_low : ∀ 𝓐 B x, is_infimum 𝓐 B x → (∀ y, (is_lower_bound 𝓐 B y) → (x . (≽(𝓐)) . y)) := sorry
theorem upp_and_sm_upp_sup :
∀ 𝓐 B x, (is_upper_bound 𝓐 B x) → (∀ y, (is_upper_bound 𝓐 B y) → (x . (≼(𝓐)) . y)) → (is_supremum 𝓐 B x) := sorry
theorem low_and_big_low_inf :
∀ 𝓐 B x, (is_lower_bound 𝓐 B x) → (∀ y, (is_lower_bound 𝓐 B y) → (x . (≽(𝓐)) . y)) → (is_infimum 𝓐 B x) := sorry
theorem sup_uni : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_supremum 𝓐 B x) → (is_supremum 𝓐 B y) → (x = y) := sorry
theorem inf_uni : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_infimum 𝓐 B x) → (is_infimum 𝓐 B y) → (x = y) := sorry
theorem inv_is_sup_inf : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_supremum 𝓐 B x) ↔ (is_infimum (invPO 𝓐) B x)) := sorry
theorem inv_is_inf_sup : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_infimum 𝓐 B x) ↔ (is_supremum (invPO 𝓐) B x)) := sorry
theorem max_um_is_sup : ∀ 𝓐 B x, (PartOrd 𝓐) → (B ⊆ setPO(𝓐)) → (is_maximum 𝓐 B x) → (is_supremum 𝓐 B x) := sorry
theorem min_um_is_inf :∀ 𝓐 B x, (PartOrd 𝓐) → (B ⊆ setPO(𝓐)) → (is_minimum 𝓐 B x) → (is_infimum 𝓐 B x)  := sorry
theorem sup_subset : ∀ 𝓐 B C x y, (PartOrd 𝓐) → (B ⊆ C) → (is_supremum 𝓐 C x) → (is_supremum 𝓐 B y) → (¬ (x . (≺(𝓐)) . y)) := sorry
theorem inf_subset : ∀ 𝓐 B C x y, (PartOrd 𝓐) → (B ⊆ C) → (is_infimum 𝓐 C x) → (is_infimum 𝓐 B y) → (¬ (x . (≻(𝓐)) . y)) := sorry
theorem sup_union :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_supremum 𝓐 (B _ i) x) → (is_supremum 𝓐 (⋃[i in I] B at i) x) := sorry
theorem inf_union :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_infimum 𝓐 (B _ i) x) → (is_infimum 𝓐 (⋃[i in I] B at i) x) := sorry


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


theorem partmin_um_un_prop : ∀ 𝓐 B I x, (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_minimum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_minimum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimum 𝓐 (B _ i) y} x)) := sorry
theorem partmax_um_un_prop : ∀ 𝓐 B I x, (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_maximum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_maximum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximum 𝓐 (B _ i) y} x)) := sorry


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

theorem max_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MaxExi B) → (is_maximum 𝓐 B (𝓐 Max B)) := sorry
theorem min_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MinExi B) → (is_minimum 𝓐 B (𝓐 Min B)) := sorry
theorem supr_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 SuprExi B) → (is_supremum 𝓐 B (𝓐 Supr B)) := sorry
theorem inf_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 InfmExi B) → (is_infimum 𝓐 B (𝓐 Infm B)) := sorry
theorem max_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 MaxExi B) → ((is_maximum 𝓐 B x) ↔ (x = 𝓐 Max B)) := sorry
theorem min_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 MinExi B) → ((is_minimum 𝓐 B x) ↔ (x = 𝓐 Min B)) := sorry
theorem supr_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 SuprExi B) → ((is_supremum 𝓐 B x) ↔ (x = 𝓐 Supr B)) := sorry
theorem infm_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 InfmExi B) → ((is_infimum 𝓐 B x) ↔ (x = 𝓐 Infm B)) := sorry
theorem sup_is_max :  ∀ 𝓐 B, (B ⊆ setPO(𝓐)) → (PartOrd 𝓐) → (𝓐 MaxExi B) → (𝓐 SuprExi B) ∧ ((𝓐 Supr B) = 𝓐 Max B) := sorry
theorem inf_is_min : ∀ 𝓐 B, (B ⊆ setPO(𝓐)) → (PartOrd 𝓐) → (𝓐 MinExi B) → (𝓐 InfmExi B) ∧ ((𝓐 Infm B) = 𝓐 Min B) := sorry
theorem max_min_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MaxExi B) → (((invPO 𝓐) MinExi B) ∧ ((𝓐 Max B) = (invPO(𝓐)) Min B)) := sorry
theorem min_max_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MinExi B) → (((invPO 𝓐) MaxExi B) ∧ ((𝓐 Min B) = (invPO(𝓐)) Max B)) := sorry
theorem max_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MaxExi B) → (((𝓐 Max B) ∈ C) ↔ ((𝓐 MaxExi C) ∧ ((𝓐 Max C) = 𝓐 Max B))) := sorry
theorem min_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MinExi B) → (((𝓐 Min B) ∈ C) ↔ ((𝓐 MinExi C) ∧ ((𝓐 Min C) = 𝓐 Min B))) := sorry
theorem po_max_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MaxExi B) → (𝓐 MaxExi C) → ((𝓐 Max C) . (≼(𝓐)) . (𝓐 Max B)) := sorry
theorem po_min_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MinExi B) → (𝓐 MinExi C) → ((𝓐 Min B) . (≼(𝓐)) . (𝓐 Min C)) := sorry
theorem max_inter_prop :
∀ 𝓐 B I i, i ∈ I → (PartOrd 𝓐) → (B IndxFun I) → ((𝓐 Max (B _ i)) ∈ (⋂[ i in I ] B at i)) →
(𝓐 MaxExi (B _ i)) → ((𝓐 MaxExi (⋂[ i in I ] B at i)) ∧ ((𝓐 Max (⋂[ i in I ] B at i)) = 𝓐 Max (B _ i))) := sorry
theorem min_inter_prop :
∀ 𝓐 B I i, i ∈ I → (PartOrd 𝓐) → (B IndxFun I) → ((𝓐 Min (B _ i)) ∈ (⋂[ i in I ] B at i)) →
(𝓐 MinExi (B _ i)) → ((𝓐 MinExi (⋂[ i in I ] B at i)) ∧ ((𝓐 Min (⋂[ i in I ] B at i)) = 𝓐 Min (B _ i))) := sorry
theorem max_un_prop :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) →
(∀ i j ∈ I; (𝓐 Max (B _ i)) = (𝓐 Max (B _ j))) → ((𝓐 MaxExi (⋃[ i in I ] B at i)) ∧
(∀ s ∈ I; (𝓐 Max ((⋃[ i in I ] B at i))) = (𝓐 Max (B _ s)))) := sorry
theorem min_un_prop :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) →
(∀ i j ∈ I; (𝓐 Min (B _ i)) = (𝓐 Min (B _ j))) → ((𝓐 MinExi (⋃[ i in I ] B at i)) ∧
(∀ s ∈ I; (𝓐 Min ((⋃[ i in I ] B at i))) = (𝓐 Min (B _ s)))) := sorry

theorem supr_subset : ∀ 𝓐 B C, (PartOrd 𝓐) →
 (B ⊆ C) → (𝓐 SuprExi C) → (𝓐 SuprExi B) → (¬ ((𝓐 Supr C) . (≺(𝓐)) . (𝓐 Supr B))) := sorry

theorem infm_subset : ∀ 𝓐 B C, (PartOrd 𝓐) → (B ⊆ C) → (𝓐 InfmExi C) → (𝓐 InfmExi B)
→ (¬ ((𝓐 Infm B) . (≺(𝓐)) . (𝓐 Infm C))) := sorry

theorem supr_union :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; 𝓐 SuprExi (B _ i))
→ (∀ i j ∈ I; (𝓐 Supr (B _ i)) = (𝓐 Supr (B _ j))) →
((𝓐 SuprExi (⋃[i in I] B at i)) ∧
(∀ s ∈ I; (𝓐 Supr (⋃[i in I] B at i)) = (𝓐 Supr (B _ s)))) := sorry

theorem infm_union :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; 𝓐 InfmExi (B _ i))
→ (∀ i j ∈ I; (𝓐 Infm (B _ i)) = (𝓐 Infm (B _ j))) →
((𝓐 InfmExi (⋃[i in I] B at i)) ∧
(∀ s ∈ I; (𝓐 Infm (⋃[i in I] B at i)) = (𝓐 Infm (B _ s)))) := sorry


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

theorem lro_sub_all : ∀ 𝓐 a b, ( ⦗ a ; b ⦘ of 𝓐 ) ⊆ setPO(𝓐) := sorry
theorem lcro_sub_all : ∀ 𝓐 a b, ( ⟦ a ; b ⦘ of 𝓐) ⊆ setPO(𝓐) := sorry
theorem lorc_sub_all : ∀ 𝓐 a b, ( ⦗ a ; b ⟧ of 𝓐) ⊆ setPO(𝓐) := sorry
theorem lrc_sub_all : ∀ 𝓐 a b, ( ⟦ a ; b ⟧ of 𝓐) ⊆ setPO(𝓐) := sorry
theorem lc_sub_all : ∀ 𝓐 a, ( ⟦ a ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐) := sorry
theorem rc_sub_all : ∀ 𝓐 b, ( ⦗ -∞ ; b ⟧ of 𝓐) ⊆ setPO(𝓐) := sorry
theorem lo_sub_all : ∀ 𝓐 a, ( ⦗ a ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐) := sorry
theorem ro_sub_all : ∀ 𝓐 b, ( ⦗ -∞ ; b ⦘ of 𝓐) ⊆ setPO(𝓐) := sorry
theorem f_sub_all :  ∀ 𝓐, (⦗ -∞ ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐) := sorry
theorem f_eq_all : ∀ 𝓐, (⦗ -∞ ; +∞  ⦘ of 𝓐) = setPO(𝓐) := sorry

theorem lro_is_lro : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; b ⦘ of 𝓐) ↔ ((a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)) := sorry
theorem lcro_is_lcro : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; b ⦘ of 𝓐) ↔ ((a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)) := sorry
theorem locr_is_locr : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; b ⟧ of 𝓐) ↔ ((a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)) := sorry
theorem lrc_is_lrc : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; b ⟧ of 𝓐) ↔ ((a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)) := sorry
theorem lc_is_lc : ∀ 𝓐 a, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; +∞ ⦘ of 𝓐) ↔ (a . (≼(𝓐)) . x) := sorry
theorem rc_is_rc : ∀ 𝓐 b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; b ⟧ of 𝓐) ↔ (x . (≼(𝓐)) . b) := sorry
theorem lo_is_lo : ∀ 𝓐 a, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; +∞ ⦘ of 𝓐) ↔ (a . (≺(𝓐)) . x) := sorry
theorem ro_is_ro : ∀ 𝓐 b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; b ⦘ of 𝓐) ↔ (x . (≺(𝓐)) . b) := sorry
theorem full_is_full : ∀ 𝓐, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; +∞ ⦘ of 𝓐) := sorry

theorem lrc_nemp : ∀ 𝓐, ∀ a ∈ setPO(𝓐); ∀ b, (PartOrd 𝓐) → ((⟦ a ; b ⟧ of 𝓐) ≠ ∅ ↔ (a . ≼(𝓐) . b)) := sorry
theorem lrc_min : ∀ 𝓐, ∀ a ∈ setPO(𝓐); ∀ b, (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_minimum 𝓐 (⟦ a ; b ⟧ of 𝓐) a) := sorry
theorem lrc_max : ∀ 𝓐 a, ∀ b ∈ setPO(𝓐); (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_maximum 𝓐 (⟦ a ; b ⟧ of 𝓐) b) := sorry


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

theorem boolean_Latt : ∀ A, (Latt (BoolPO A)) := sorry
theorem compl_latt_inf_crit : ∀ 𝓐, (CompLatt 𝓐) ↔ (∀ X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X)) := sorry
theorem compl_latt_is_latt : ∀ 𝓐, (CompLatt 𝓐) → (Latt 𝓐) := sorry
theorem boolean_CompLatt : ∀ A, (CompLatt (BoolPO A)) := sorry
theorem Knaster_Tarski_lemma₀ : ∀ 𝓐, ∀ a b ∈ setPO(𝓐); (a . ≼(𝓐) . b) → (CompLatt 𝓐) → (CompLatt (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐))) := sorry
theorem Knaster_Tarski_lemma₁ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (𝓐 MaxExi (f FixOn 𝓐)) := sorry
theorem Knaster_Tarski_lemma₂ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → ((f FixOn 𝓐) ≠ ∅) := sorry
theorem Knaster_Tarski_theorem : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (CompLatt (𝓐 SubsPO (f FixOn 𝓐))) := sorry


-- 33) linear order and it's main properties
def is_linear_order (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧ (str_conn (≼(𝓐)) setPO(𝓐))
syntax "LinOrd" term : term
macro_rules
| `(LinOrd $𝓐) => `(is_linear_order $𝓐)


theorem inv_is_LO : ∀ 𝓐, (LinOrd 𝓐) → (LinOrd (invPO 𝓐)) := sorry
theorem sub_is_LO : ∀ 𝓐 B, (B ≠ ∅) → (LinOrd 𝓐) → (B ⊆ setPO(𝓐)) → (LinOrd (𝓐 SubsPO B)) := sorry


theorem lin_ord_prop : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∨ (y . (≼(𝓐)) . x)) := sorry
theorem lin_ord_wk_prop : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (x ≠ y) → ((x . ≺(𝓐) . y) ∨ (y . (≺(𝓐)) . x))) := sorry
theorem lin_ord_nR₁ : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (¬ (x . (≺(𝓐)) . y)) → (y . (≼(𝓐)) . x)) := sorry
theorem lin_ord_nR₂ : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (¬ (x . (≼(𝓐)) . y)) → (y . (≺(𝓐)) . x)) := sorry


theorem linmin_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_minimal 𝓐 X x) ↔ (is_minimum 𝓐 X x)) := sorry
theorem linmax_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_maximal 𝓐 X x) ↔ (is_maximum 𝓐 X x)) := sorry

theorem linmin_al_sub_cmp : ∀ 𝓐 B C x y, (LinOrd 𝓐) →
(C ⊆ B) → (B ⊆ setPO(𝓐)) → (is_minimal 𝓐 B x) → (is_minimal 𝓐 C y) → (x . ≼(𝓐) . y) := sorry
theorem linmax_al_sub_cmp : ∀ 𝓐 B C x y, (LinOrd 𝓐) →
(C ⊆ B) → (B ⊆ setPO(𝓐)) → (is_maximal 𝓐 B x) → (is_maximal 𝓐 C y) → (y . ≼(𝓐) . x) := sorry
theorem lin_al_min_inter_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))
→ (B IndxFun I) → (is_minimal 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_minimal 𝓐 ((B _ i)) y) → (y . ≼(𝓐) . x) := sorry
theorem lin_al_max_inter_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B IndxFun I) → (is_maximal 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_maximal 𝓐 ((B _ i)) y) → (x . ≼(𝓐) . y) := sorry
theorem lin_partmin_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_minimal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_minimal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimal 𝓐 (B _ i) y} x)) := sorry
theorem lin_partmax_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_maximal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_maximal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximal 𝓐 (B _ i) y} x)) := sorry

theorem linsup_al : ∀ 𝓐 B x, (LinOrd 𝓐) → ((is_supremum 𝓐 B x) ↔ (is_minimal 𝓐 (𝓐 ▴ B) x)) := sorry
theorem lininf_al : ∀ 𝓐 B x, (LinOrd 𝓐) → ((is_infimum 𝓐 B x) ↔ (is_maximal 𝓐 (𝓐 ▾ B) x)) := sorry

theorem lin_supr_subset : ∀ 𝓐 B C, (LinOrd 𝓐) →
 (B ⊆ C) → (𝓐 SuprExi C) → (𝓐 SuprExi B) → (((𝓐 Supr B) . (≼(𝓐)) . (𝓐 Supr C))) := sorry
theorem lin_infm_subset : ∀ 𝓐 B C, (LinOrd 𝓐) →
 (B ⊆ C) → (𝓐 InfmExi C) → (𝓐 InfmExi B) → (((𝓐 Infm C) . (≼(𝓐)) . (𝓐 Infm B))) := sorry


theorem linsup_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 SuprExi (B _ i)))
 → ((is_supremum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_supremum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_supremum 𝓐 (B _ i) y} x)) := sorry

theorem lininf_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 InfmExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_infimum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_infimum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_infimum 𝓐 (B _ i) y} x)) := sorry


theorem lin_latt : ∀ 𝓐, (LinOrd 𝓐) → (Latt 𝓐) := sorry


-- 34) Well founded order and Well ordered set definition


def is_well_found_order 𝓐 := (PartOrd 𝓐) ∧ (∀ X, ( (X ⊆ setPO(𝓐)) →  (X ≠ ∅) → (𝓐 MinExi X)))
syntax "WellFoundOrd" term : term
macro_rules
| `(WellFoundOrd $𝓐) => `(is_well_found_order $𝓐)

def is_well_order 𝓐 := (LinOrd 𝓐) ∧ ∀ X, (X ⊆ setPO(𝓐)) →  (X ≠ ∅) → (𝓐 MinExi X)
syntax "WellOrd" term : term
macro_rules
| `(WellOrd $𝓐) => `(is_well_order $𝓐)


theorem wellord_wellfoundcrit : ∀ 𝓐, (WellOrd 𝓐) ↔ ((LinOrd 𝓐) ∧ (WellFoundOrd 𝓐)) := sorry


-- 35) chain and anti chain and some of their properties

def is_chain (𝓐 B) := (PartOrd 𝓐) ∧ (B ⊆ setPO(𝓐)) ∧ (LinOrd (𝓐 SubsPO B))
syntax term "Chain" term : term
macro_rules
| `($𝓐 Chain $B) => `(is_chain $𝓐 $B)

def anti_chain (𝓐 B) := (PartOrd 𝓐) ∧ (B ⊆ setPO(𝓐)) ∧ (∀ x y ∈ B; noncomparable_str 𝓐 x y)
syntax term "AntiChain" term : term
macro_rules
| `($𝓐 AntiChain $B) => `(anti_chain $𝓐 $B)

theorem lin_chain : ∀ 𝓐 B, (B ≠ ∅) → (B ⊆ setPO(𝓐)) → (LinOrd 𝓐) → (𝓐 Chain B) := sorry
theorem antichain : ∀ 𝓐 𝓑 A B, (𝓐 AntiChain A) → (𝓑 AntiChain B) → ((𝓐 Cart2CordPO 𝓑) AntiChain (A × B)) := sorry


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


theorem iso_equin : ∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (setPO(𝓐) ~ setPO(𝓑)) := sorry
theorem iso_refl : ∀ 𝓐, (𝓐 ≃O 𝓐) := sorry
theorem iso_symm : ∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (𝓑 ≃O 𝓐) := sorry
theorem iso_trans : ∀ 𝓐 𝓑 𝓒, (𝓐 ≃O 𝓑) → (𝓑 ≃O 𝓒) → (𝓐 ≃O 𝓒) := sorry


-- 38) Simple properties that doesn't change through isomorphism in different partial ordered set

theorem iso_in₀ : ∀ 𝓐 𝓑 f x, (f PO_ISO 𝓐 To 𝓑) → (x ∈ setPO(𝓐)) → ((f⦅x⦆)) ∈ setPO(𝓑) := sorry
theorem iso_in₁ : ∀ 𝓐 𝓑 f x, (f PO_ISO 𝓐 To 𝓑) → (x ∈ setPO(𝓐)) → ((x ∈ setPO(𝓐)) ↔ ((f⦅x⦆)) ∈ setPO(𝓑)) := sorry
theorem iso_in₂ : ∀ 𝓐 𝓑 T f x, (x ∈ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → ((x ∈ T) ↔ (f⦅x⦆) ∈ f.[T]) := sorry

theorem iso_R₂ : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → ∀ x y ∈ setPO(𝓐); (x . ≼(𝓐) . y) ↔ ((f⦅x⦆) . (≼(𝓑)) . (f⦅y⦆)) := sorry
theorem iso_eq : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → ∀ x y ∈ setPO(𝓐); (x = y) ↔ ((f⦅x⦆) = (f⦅y⦆)) := sorry
theorem iso_R₁ : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (PartOrd 𝓐) → (PartOrd 𝓑) → (∀ x y ∈ setPO(𝓐); (x . ≺(𝓐) . y) ↔ ((f⦅x⦆) . (≺(𝓑)) . (f⦅y⦆))) := sorry


-- 39) Logical properties that doesn't change through isomorphism in different partial ordered set


theorem poiso_not_equiv (φ₁ φ₂ : Set → Prop) : ∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((¬(φ₁ x)) ↔ (¬φ₂ (f⦅x⦆))) := sorry
theorem poiso_and_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ∧ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ∧ (φ₄ (f⦅x⦆)))) := sorry
theorem poiso_or_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ∨ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ∨ (φ₄ (f⦅x⦆)))) := sorry
theorem poiso_if_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) → ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) → (φ₄ (f⦅x⦆)))) := sorry
theorem poiso_iff_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ↔ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ↔ (φ₄ (f⦅x⦆)))) := sorry


theorem poiso_all_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ X; ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∀ x ∈ X; (φ₁ x)) ↔ (∀ x ∈ f.[X]; (φ₂ x))) := sorry

theorem poiso_exi_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ X; ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∃ x ∈ X; (φ₁ x)) ↔ (∃ x ∈ f.[X]; (φ₂ x))) := sorry


theorem poiso_allin_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ setPO(𝓐); ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∀ x ∈ setPO(𝓐); (φ₁ x)) ↔ (∀ x ∈ setPO(𝓑); (φ₂ x))) := sorry

theorem posio_exiin_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ setPO(𝓐); ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∃ x ∈ setPO(𝓐); (φ₁ x)) ↔ (∃ x ∈ setPO(𝓑); (φ₂ x))) := sorry


-- 40) Using the above theorems about isomorphism for particular properties

theorem poiso_minal : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_minimal 𝓐 X x) ↔ (is_minimal 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_maxal : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_maximal 𝓐 X x) ↔ (is_maximal 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_minum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_minimum 𝓐 X x) ↔ (is_minimum 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_maxum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_maximum 𝓐 X x) ↔ (is_maximum 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_lowbou : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_lower_bound 𝓐 X x) ↔ (is_lower_bound 𝓑 (f.[X]) (f⦅x⦆)) ) := sorry
theorem poiso_uppbou : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_upper_bound 𝓐 X x) ↔ (is_upper_bound 𝓑 (f.[X]) (f⦅x⦆)) ) := sorry
theorem poiso_minexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 MinExi X) ↔ (𝓑 MinExi f.[X])) := sorry
theorem poiso_maxexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 MaxExi X) ↔ (𝓑 MaxExi f.[X])) := sorry


-- 41) Theorems about equal subsets because of isomorphism and its application for particular subsets

theorem poiso_subs_eq (φ : Set → Set → Set → Prop) (ψ : Set → Set → Set) : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 X x, (x ∈ ψ 𝓧 X ↔ φ 𝓧 X x)) →
(∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (ψ 𝓧 X) ⊆ setPO(𝓧)) → (∀ X, (∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆)))) →
(f.[ψ 𝓐 X] = ψ 𝓑 (f.[X]))) := sorry

theorem poiso_interv_eq (c d : Set) (φ : Set → Set → Set → Set → Prop) (ψ : Set → Set → Set → Set)
 : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 x, ∀ a b, (x ∈ ψ 𝓧 a b ↔ φ 𝓧 a b x)) →
 (∀ 𝓧 a b, (ψ 𝓧 a b) ⊆ setPO(𝓧)) → ((∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 c d x) ↔ (φ 𝓑 (f⦅c⦆) (f⦅d⦆) (f⦅x⦆)))) → (
  f.[ψ 𝓐 c d] = ψ 𝓑 (f⦅c⦆) (f⦅d⦆)
 )) := sorry


 theorem poiso_interv_eq₂ (c : Set) (φ : Set → Set → Set → Prop) (ψ : Set → Set → Set)
 : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 x, ∀ a, (x ∈ ψ 𝓧 a ↔ φ 𝓧 a x)) →
 (∀ 𝓧 a, (ψ 𝓧 a) ⊆ setPO(𝓧)) → ((∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 c x) ↔ (φ 𝓑 (f⦅c⦆) (f⦅x⦆)))) → (
  f.[ψ 𝓐 c] = ψ 𝓑 (f⦅c⦆)
 )) := sorry

theorem poiso_minset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[min_set 𝓐 X] = min_set 𝓑 (f.[X])) := sorry
theorem poiso_maxset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[max_set 𝓐 X] = max_set 𝓑 (f.[X])) := sorry
theorem poiso_lowset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[𝓐 ▾ X] = 𝓑 ▾ (f.[X])) := sorry
theorem poiso_uppset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[𝓐 ▴ X] = 𝓑 ▴ (f.[X])) := sorry
theorem poiso_sup : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_supremum 𝓐 X x) ↔ (is_supremum 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_inf : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_infimum 𝓐 X x) ↔ (is_infimum 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_supexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 SuprExi X) ↔ (𝓑 SuprExi (f.[X]))) := sorry
theorem poiso_infexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 InfmExi X) ↔ (𝓑 InfmExi (f.[X]))) := sorry



theorem poiso_lro : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐))
 → (f.[⦗ a ; b ⦘ of 𝓐] = ⦗ f⦅a⦆ ; f⦅b⦆ ⦘ of 𝓑) := sorry
theorem poiso_lcro : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐))
→ (f.[⟦ a ; b ⦘ of 𝓐] = ⟦ f⦅a⦆ ; f⦅b⦆ ⦘ of 𝓑) := sorry
theorem poiso_locr : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐))
→ (f.[⦗ a ; b ⟧ of 𝓐] = ⦗ f⦅a⦆ ; f⦅b⦆ ⟧ of 𝓑) := sorry
theorem poiso_lrc : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐))
→ (f.[⟦ a ; b ⟧ of 𝓐] = ⟦ f⦅a⦆ ; f⦅b⦆ ⟧ of 𝓑) := sorry
theorem poiso_lc : ∀ 𝓐 𝓑 f a, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (f.[⟦ a ; +∞ ⦘ of 𝓐] = ⟦ f⦅a⦆ ; +∞ ⦘ of 𝓑) := sorry
theorem poiso_rc : ∀ 𝓐 𝓑 f b, (f PO_ISO_PO 𝓐 To 𝓑) → (b ∈ setPO(𝓐)) → (f.[ ⦗ -∞ ; b ⟧ of 𝓐] = ⦗  -∞  ; f⦅b⦆ ⟧ of 𝓑) := sorry
theorem poiso_lo : ∀ 𝓐 𝓑 f a, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (f.[ ⦗  a ; +∞ ⦘ of 𝓐] = ⦗ f⦅a⦆ ; +∞ ⦘ of 𝓑) := sorry
theorem poiso_ro : ∀ 𝓐 𝓑 f b, (f PO_ISO_PO 𝓐 To 𝓑) → (b ∈ setPO(𝓐)) → (f.[⦗ -∞ ; b ⦘ of 𝓐] = ⦗ -∞ ; f⦅b⦆ ⦘ of 𝓑) := sorry
theorem poiso_full : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (f.[⦗ -∞ ; +∞  ⦘ of 𝓐] = ⦗ -∞ ; +∞  ⦘ of 𝓑) := sorry



-- 42) Theorem about equal element constructions because of isomorphism and its applications

theorem poiso_elconstr  (φ : Set → Set → Set → Prop ) (ψ : Set → Set → Set) (cond : Set → Set → Prop)  :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (cond 𝓐 X) → (cond 𝓑 (f.[X])) → (f PO_ISO_PO 𝓐 To 𝓑) →
(∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (PartOrd 𝓧) → (cond 𝓧 X) → ψ 𝓧 X ∈ setPO(𝓧)) →
(∀ 𝓧 X t, (PartOrd 𝓧) → (cond 𝓧 X) →  ((φ 𝓧 X (t) ↔ (t = ψ 𝓧 X)))) →
(∀ X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆)))) →
(f⦅ψ 𝓐 X⦆ = ψ 𝓑 (f.[X])) := sorry



theorem poiso_minumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 MinExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Min X⦆ = 𝓑 Min (f.[X])) := sorry
theorem poiso_maxumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 MaxExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Max X⦆ = 𝓑 Max (f.[X])) := sorry
theorem poiso_supel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 SuprExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Supr X⦆ = 𝓑 Supr (f.[X])) := sorry
theorem poiso_infel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Infm X⦆ = 𝓑 Infm (f.[X])) := sorry


-- 43 ) Properties about partial order itself also doesn't change through isomorphism


theorem poiso_if_then_iff (φ : Set → Prop) :
(∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → (φ 𝓐) → (φ 𝓑)) → (∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((φ 𝓐) ↔ (φ 𝓑))) := sorry

theorem poiso_subset_prop (φ : Set → Set → Prop) :
(∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X) ↔ (φ 𝓑 (f.[X])))) →
(∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((∀ X, (X ⊆ setPO(𝓐)) → (φ 𝓐 X)) ↔ (∀ X, (X ⊆ setPO(𝓑)) → (φ 𝓑 X)))) := sorry

theorem poiso_latt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((Latt 𝓐) ↔ (Latt 𝓑)) := sorry
theorem poiso_complatt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((CompLatt 𝓐) ↔ (CompLatt 𝓑)) := sorry
theorem poiso_linord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((LinOrd 𝓐) ↔ (LinOrd 𝓑)) := sorry
theorem poiso_wellfo : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((WellFoundOrd 𝓐) ↔ (WellFoundOrd 𝓑)) := sorry
theorem poiso_welord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((WellOrd 𝓐) ↔ (WellOrd 𝓑)) := sorry


-- 44) Partial order isomorphism translates through different partial order constructions

theorem poiso_inv : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((inv_PO 𝓐) P≃O (inv_PO 𝓑)) := sorry
theorem poiso_subs : ∀ 𝓐 𝓑 f X, (X ≠ ∅) → (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 SubsPO X) P≃O (𝓑 SubsPO (f.[X]))) := sorry
theorem poiso_inter : ∀ 𝓐 𝓑 𝓒 𝓓 f, (setPO(𝓐) = setPO(𝓒)) →
(setPO(𝓑) = setPO(𝓓)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f PO_ISO_PO 𝓒 To 𝓓) → (f PO_ISO_PO (𝓐 InterPO 𝓒) To (𝓑 InterPO 𝓓)) := sorry
theorem poiso_cart : ∀ 𝓐 𝓑 𝓒 𝓓, (𝓐 P≃O 𝓑) → (𝓒 P≃O 𝓓) → ((𝓐 Cart2CordPO 𝓒) P≃O (𝓑 Cart2CordPO 𝓓)) := sorry


-- 45) induced order with order function saving creates isomorphic partial order

noncomputable def induced_R₂ (𝓐 f: Set) := {s ∈ (rng f) × (rng f) | ∃ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∧ s = (f⦅x⦆, f⦅y⦆)}
noncomputable def induced_order (𝓐 f: Set) := ⁅rng f; str (rng f) (induced_R₂ 𝓐 f); (induced_R₂ 𝓐 f)⁆

theorem poiso_induced : ∀ 𝓐 f X, (PartOrd 𝓐) → (f Inj (setPO(𝓐)) To X) → (f PO_ISO_PO 𝓐 To (induced_order 𝓐 f)) := sorry
