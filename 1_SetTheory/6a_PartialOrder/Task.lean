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
theorem irrefl_int_left : ∀ P Q, (irrefl P) → (irrefl (P ∩ Q)) := sorry
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

-- 14) relations between strict and non strict order
noncomputable def str (A R) := R \ (id_ A)
noncomputable def nonstr (A R) := R ∪ (id_ A)
theorem spo_then_nspo : ∀ A R, (R SPO A) → ((nonstr A R) NSPO A) := sorry
theorem nspo_then_spo : ∀ A R, (R NSPO A) → ((str A R) SPO A) := sorry
theorem str_nonstr_id : ∀ A R, (R SPO A) → ((str A (nonstr A R)) = R) := sorry
theorem nonstr_str_id : ∀ A R, (R NSPO A) → ((nonstr A (str A R)) = R) := sorry
noncomputable def SPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R SPO A) }
noncomputable def NSPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R NSPO A) }
theorem SPOS_NSPOS_equinum : ∀ A, (SPOS A) ~ (NSPOS A) := sorry


-- 15) Strict and non strict partial order relations and equivalent criteria
def is_partial_order (A R₁ R₂ : Set) : Prop := A ≠ ∅ ∧ (R₁ SPO A) ∧ (R₂ = nonstr A R₁)
syntax term "with" term "PO" term  : term
macro_rules
| `($R₁:term with $R₂:term PO $A:term) => `(is_partial_order $A $R₁ $R₂)
theorem part_ord_nspo_crit : ∀ A R₁ R₂, (R₁ with R₂ PO A) ↔ ((A ≠ ∅) ∧ (R₂ NSPO A) ∧ (R₁ = str A R₂)) := sorry
theorem part_ord_crit :
∀ A R₁ R₂, (R₁ with R₂ PO A) ↔ (A ≠ ∅ ∧ (R₁ SPO A) ∧ (R₂ NSPO A) ∧ (R₂ = nonstr A R₁) ∧ (R₁ = str A R₂)) := sorry


-- 16) Partial Order as a triple (setPO, ≺, ≼)
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


noncomputable def PO_from_str (A R₁) := ⁅A; R₁; nonstr A R₁⁆
noncomputable def PO_from_nonstr (A R₂) := ⁅A; str A R₂; R₂⁆
syntax term "StrIntro" term : term
syntax term "NoNStrIntro" term : term
macro_rules
| `($A StrIntro $R₁:term) => `(PO_from_str $A $R₁)
| `($A NoNStrIntro $R₂:term) => `(PO_from_nonstr $A $R₂)


theorem po_from_str_is_po : ∀ A R₁, (A ≠ ∅) → (R₁ SPO A) → (PartOrd (A StrIntro R₁)) := sorry
theorem po_from_non_str_is_po : ∀ A R₂, (A ≠ ∅) → (R₂ NSPO A) → (PartOrd (A NoNStrIntro R₂)) := sorry
theorem prec_SPO : ∀ 𝓐, (PartOrd 𝓐) → ((≺(𝓐)) SPO (setPO(𝓐))) := sorry
theorem preceq_NSPO : ∀ 𝓐, (PartOrd 𝓐) → ((≼(𝓐)) NSPO (setPO(𝓐))) := sorry
theorem setPO_is_setPO : ∀ A R₁ R₂, (setPO(⁅A; R₁; R₂⁆) = A) := sorry
theorem lessPO_is_lessPO :  ∀ A R₁ R₂, (≺(⁅A; R₁; R₂⁆) = R₁) := sorry
theorem lesseqPO_is_lesseqPO : ∀ A R₁ R₂, (≼(⁅A; R₁; R₂⁆) = R₂) := sorry
theorem triple_po_is_po : ∀ 𝓐, (PartOrd 𝓐) → (is_partial_order setPO(𝓐) ≺(𝓐) ≼(𝓐)) := sorry
theorem po_is_triple_po : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (PartOrd (⁅A; R₁; R₂⁆)) := sorry
theorem po_less_more : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≺(𝓐)) . y) ↔ (y . ≻(𝓐) . x) := sorry
theorem po_lesseq_moreeq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≼(𝓐)) . y) ↔ (y . ≽(𝓐) . x) := sorry
theorem po_emp : ∀ 𝓐, (PartOrd 𝓐) → (setPO(𝓐) ≠ ∅) := sorry



-- 17) partial order pair properties
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
theorem trans_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≺(𝓐)) . y) → (y . (≺(𝓐)) . z) → (x . (≺(𝓐)) . z)) := sorry
theorem trans_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x . (≼(𝓐)) . z)) := sorry
theorem trans_R₁_R₂_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≺(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x . (≼(𝓐)) . z)) := sorry
theorem trans_R₁_R₂_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≺(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x . (≺(𝓐)) . z)) := sorry
theorem trans_R₂_R₁_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≺(𝓐)) . z) → (x . (≼(𝓐)) . z)) := sorry
theorem trans_R₂_R₁_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≺(𝓐)) . z) → (x . (≺(𝓐)) . z)) := sorry
theorem stabil_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x = z) → ((x = y) ∧ (y = z))) := sorry
theorem no_symm_R₁_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, ¬ ((x . (≺(𝓐)) . y) ∧ (y . (≼(𝓐)) . x))) := sorry
theorem PO_noncomp :
∀ 𝓐, (PartOrd 𝓐) → (∀ x y ∈ (setPO(𝓐)); (noncomparable_nonstr 𝓐 x y) ↔ (x ≠ y ∧ (noncomparable_str 𝓐 x y))) := sorry
theorem bin_R₁ : ∀ 𝓐, (PartOrd 𝓐) → BinRel (≺(𝓐)) := sorry
theorem bin_R₂ : ∀ 𝓐, (PartOrd 𝓐) → BinRel (≼(𝓐)) := sorry
theorem binA_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (≺(𝓐)) BinRelOn (setPO(𝓐)) := sorry
theorem binA_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (≼(𝓐)) BinRelOn (setPO(𝓐)) := sorry



--18) maximal/minimal, greatest/lowest properties, maxset, minset
def is_maximal (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (x . (≺(𝓐)) . y))
def is_minimal (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (y . (≺(𝓐)) . x))
def is_greatest (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (y . (≼(𝓐)) . x))
def is_lowest (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (x . (≼(𝓐)) . y))


noncomputable def max_set (𝓐 B) := {z ∈ B | is_maximal 𝓐 B z }
noncomputable def min_set (𝓐 B) := {z ∈ B | is_minimal 𝓐 B z }

theorem max_set_is_max_set : ∀ 𝓐 B x, ((x ∈ max_set 𝓐 B) ↔ (is_maximal 𝓐 B x)) := sorry
theorem min_set_is_min_set : ∀ 𝓐 B x, ((x ∈ min_set 𝓐 B) ↔ (is_minimal 𝓐 B x)) := sorry


-- 19) maximal/minimal, greatest/lowest and subset
theorem max_al_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_maximal 𝓐 B x) → (x ∈ C) → (is_maximal 𝓐 C x) := sorry
theorem min_al_subsets_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_minimal 𝓐 B x) → (x ∈ C) → (is_minimal 𝓐 C x) := sorry
theorem max_um_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_greatest 𝓐 B x) → (x ∈ C) → (is_greatest 𝓐 C x) := sorry
theorem min_um_subset_prop :
∀ 𝓐 B C x, (C ⊆ B) → (is_lowest 𝓐 B x) → (x ∈ C) → (is_lowest 𝓐 C x) := sorry
theorem min_um_sub_cmp : ∀ 𝓐 B C x y, (C ⊆ B) → (is_lowest 𝓐 B x) → (is_lowest 𝓐 C y) → (x . ≼(𝓐) . y) := sorry
theorem max_um_sub_cmp : ∀ 𝓐 B C x y, (C ⊆ B) → (is_greatest 𝓐 B x) → (is_greatest 𝓐 C y) → (y . ≼(𝓐) . x) := sorry


-- 20) maximal/minimal, greatest/lowest and intersection
theorem max_al_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_maximal 𝓐 (B _ i) x) → (is_maximal 𝓐 (⋂[ i in I ] B at i) x) := sorry
theorem min_al_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_minimal 𝓐 (B _ i) x) → (is_minimal 𝓐 (⋂[ i in I ] B at i) x) := sorry
theorem max_um_inter_prop :
∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_greatest 𝓐 (B _ i) x) → (is_greatest 𝓐 (⋂[ i in I ] B at i) x) := sorry
theorem min_um_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) →
(∃ i ∈ I; is_lowest 𝓐 (B _ i) x) → (is_lowest 𝓐 (⋂[ i in I ] B at i) x) := sorry

theorem um_min_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (is_lowest 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_lowest 𝓐 ((B _ i)) y) → (y . ≼(𝓐) . x) := sorry
 theorem um_max_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (is_greatest 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_greatest 𝓐 ((B _ i)) y) → (x . ≼(𝓐) . y) := sorry


-- 21) maximal/minimal, greatest/lowest and union

theorem max_al_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_maximal 𝓐 (B _ i) x) → (is_maximal 𝓐 (⋃[i in I] B at i) x) := sorry
theorem min_al_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_minimal 𝓐 (B _ i) x) → (is_minimal 𝓐 (⋃[i in I] B at i) x) := sorry
theorem max_um_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_greatest 𝓐 (B _ i) x) → (is_greatest 𝓐 (⋃[i in I] B at i) x) := sorry
theorem min_um_un_prop :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_lowest 𝓐 (B _ i) x) → (is_lowest 𝓐 (⋃[i in I] B at i) x) := sorry



-- 22) maximal/minimal, greatest/lowest properties in PO set
theorem max_um_is_al : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_greatest 𝓐 B x) → (is_maximal 𝓐 B x) := sorry
theorem min_um_is_al : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_lowest 𝓐 B x) → (is_minimal 𝓐 B x) := sorry
theorem max_um_unique_sub : ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_greatest R₂ B x) → (is_greatest R₂ B y) → (x = y) := sorry
theorem min_um_unique_sub : ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_lowest R₂ B x) → (is_lowest R₂ B y) → (x = y) := sorry
theorem max_um_maxset_singl : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_greatest 𝓐 B x) → (max_set 𝓐 B = {x}) := sorry
theorem min_um_minset_singl : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_lowest 𝓐 B x) → (min_set 𝓐 B = {x}) := sorry
theorem max_um_unique : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_greatest 𝓐 B x) → (is_greatest 𝓐 B y) → (x = y) := sorry
theorem min_um_unique : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_lowest 𝓐 B x) → (is_lowest 𝓐 B y) → (x = y) := sorry



-- 23) upper and lower bounds of a Set and their basic properties
def is_upper_bound (𝓐 B x : Set) := x ∈ setPO(𝓐) ∧ ∀ y ∈ B; (y . (≼(𝓐)) . x)
def is_lower_bound (𝓐 B x : Set) := x ∈ setPO(𝓐) ∧ ∀ y ∈ B; (x . (≼(𝓐)) . y)
noncomputable def lower_bounds (𝓐 B) := {z ∈ setPO(𝓐) | is_lower_bound 𝓐 B z}
noncomputable def upper_bounds (𝓐 B) := {z ∈ setPO(𝓐) | is_upper_bound 𝓐 B z}
syntax term "▴" term : term
syntax term "▾" term : term
macro_rules
| `($𝓐:term ▾ $B:term) => `(lower_bounds $𝓐 $B)
| `($𝓐:term ▴ $B:term) => `(upper_bounds $𝓐 $B)
theorem low_bou_set_is_low_bou : ∀ 𝓐 B, ∀ x, (x ∈ (𝓐 ▾ B) ↔ (is_lower_bound 𝓐 B x)) := sorry
theorem upp_bou_set_is_upp_bou : ∀ 𝓐 B, ∀ x, (x ∈ (𝓐 ▴ B) ↔ (is_upper_bound 𝓐 B x)) := sorry
theorem max_um_upp_bou : ∀ 𝓐 B x, (B ⊆ (setPO(𝓐))) → (is_greatest 𝓐 B x) → (is_upper_bound 𝓐 B x) := sorry
theorem min_um_low_bou : ∀ 𝓐 B x, (B ⊆ (setPO(𝓐))) → (is_lowest 𝓐 B x) → (is_lower_bound 𝓐 B x) := sorry
theorem upp_bou_max_um : ∀ 𝓐 B x, (is_upper_bound 𝓐 B x) → (x ∈ B) → (is_greatest 𝓐 B x) := sorry
theorem low_bou_min_um : ∀ 𝓐 B x, (is_lower_bound 𝓐 B x) → (x ∈ B) → (is_lowest 𝓐 B x) := sorry
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


-- 24) supremum and infimum properties
def is_supremum (𝓐 B x : Set) : Prop := is_lowest 𝓐 (𝓐 ▴ B) x
def is_infimum (𝓐 B x : Set) : Prop := is_greatest 𝓐 (𝓐 ▾ B) x
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
theorem max_um_is_sup : ∀ 𝓐 B x, (PartOrd 𝓐) → (B ⊆ setPO(𝓐)) → (is_greatest 𝓐 B x) → (is_supremum 𝓐 B x) := sorry
theorem min_um_is_inf :∀ 𝓐 B x, (PartOrd 𝓐) → (B ⊆ setPO(𝓐)) → (is_lowest 𝓐 B x) → (is_infimum 𝓐 B x)  := sorry
theorem sup_subset : ∀ 𝓐 B C x y, (PartOrd 𝓐) → (B ⊆ C) → (is_supremum 𝓐 C x) → (is_supremum 𝓐 B y) → (¬ (x . (≺(𝓐)) . y)) := sorry
theorem inf_subset : ∀ 𝓐 B C x y, (PartOrd 𝓐) → (B ⊆ C) → (is_infimum 𝓐 C x) → (is_infimum 𝓐 B y) → (¬ (x . (≻(𝓐)) . y)) := sorry
theorem sup_union :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_supremum 𝓐 (B _ i) x) → (is_supremum 𝓐 (⋃[i in I] B at i) x) := sorry
theorem inf_union :
∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_infimum 𝓐 (B _ i) x) → (is_infimum 𝓐 (⋃[i in I] B at i) x) := sorry


-- 25) minimum, maximum, supremum and infimum existence properties
def greatest_exists (𝓐 B : Set) : Prop := ∃ x, is_greatest 𝓐 B x
def lowest_exists (𝓐 B : Set) : Prop := ∃ x, is_lowest 𝓐 B x
def supremum_exists (𝓐 B : Set) : Prop := ∃ x, is_supremum 𝓐 B x
def infimum_exists (𝓐 B : Set) : Prop := ∃ x, is_infimum 𝓐 B x
syntax term "GrtExi" term : term
syntax term "LowExi" term : term
syntax term "SuprExi" term : term
syntax term "InfmExi" term : term
macro_rules
| `($𝓐:term GrtExi $B:term) => `(greatest_exists $𝓐 $B)
| `($𝓐:term LowExi $B:term) => `(lowest_exists $𝓐 $B)
| `($𝓐:term SuprExi $B:term) => `(supremum_exists $𝓐 $B)
| `($𝓐:term InfmExi $B:term) => `(infimum_exists $𝓐 $B)


theorem LowExi_constr : ∀ 𝓐 X, (X ⊆ setPO(𝓐)) → ((𝓐 LowExi X) ↔ (∃ x ∈ setPO(𝓐); is_lowest 𝓐 X x)) := sorry
theorem GrtExi_constr : ∀ 𝓐 X, (X ⊆ setPO(𝓐)) → ((𝓐 GrtExi X) ↔ (∃ x ∈ setPO(𝓐); is_greatest 𝓐 X x)) := sorry
theorem supexi_constr : ∀ 𝓐 X, ((𝓐 SuprExi X) ↔ (∃ x ∈ setPO(𝓐); is_supremum 𝓐 X x)) := sorry
theorem infexi_constr : ∀ 𝓐 X, ((𝓐 InfmExi X) ↔ (∃ x ∈ setPO(𝓐); is_infimum 𝓐 X x)) := sorry


theorem partmin_um_un_prop : ∀ 𝓐 B I x, (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 LowExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_lowest 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_lowest 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_lowest 𝓐 (B _ i) y} x)) := sorry
theorem partmax_um_un_prop : ∀ 𝓐 B I x, (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 GrtExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_greatest 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_greatest 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_greatest 𝓐 (B _ i) y} x)) := sorry


-- 26) minimum, maximum, supremum and infimum objects themselves
noncomputable def greatest (𝓐 B) := ⋃ {b ∈ B | is_greatest 𝓐 B b}
noncomputable def lowest (𝓐 B) := ⋃ {b ∈ B | is_lowest 𝓐 B b}
noncomputable def supremum (𝓐 B) := ⋃ {a ∈ setPO(𝓐) | is_supremum 𝓐 B a}
noncomputable def infimum (𝓐 B) := ⋃ {a ∈ setPO(𝓐) | is_infimum 𝓐 B a}
syntax term "Grt" term : term
syntax term "Low" term : term
syntax term "Supr" term : term
syntax term "Infm" term : term
macro_rules
| `($𝓐:term Grt $B:term) => `(greatest $𝓐 $B)
| `($𝓐:term Low $B:term) => `(lowest $𝓐 $B)
| `($𝓐:term Supr $B:term) => `(supremum $𝓐 $B)
| `($𝓐:term Infm $B:term) => `(infimum $𝓐 $B)

theorem max_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 GrtExi B) → (is_greatest 𝓐 B (𝓐 Grt B)) := sorry
theorem min_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 LowExi B) → (is_lowest 𝓐 B (𝓐 Low B)) := sorry
theorem supr_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 SuprExi B) → (is_supremum 𝓐 B (𝓐 Supr B)) := sorry
theorem inf_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 InfmExi B) → (is_infimum 𝓐 B (𝓐 Infm B)) := sorry
theorem max_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 GrtExi B) → ((is_greatest 𝓐 B x) ↔ (x = 𝓐 Grt B)) := sorry
theorem min_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 LowExi B) → ((is_lowest 𝓐 B x) ↔ (x = 𝓐 Low B)) := sorry
theorem supr_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 SuprExi B) → ((is_supremum 𝓐 B x) ↔ (x = 𝓐 Supr B)) := sorry
theorem infm_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 InfmExi B) → ((is_infimum 𝓐 B x) ↔ (x = 𝓐 Infm B)) := sorry
theorem sup_is_max :  ∀ 𝓐 B, (B ⊆ setPO(𝓐)) → (PartOrd 𝓐) → (𝓐 GrtExi B) → (𝓐 SuprExi B) ∧ ((𝓐 Supr B) = 𝓐 Grt B) := sorry
theorem inf_is_min : ∀ 𝓐 B, (B ⊆ setPO(𝓐)) → (PartOrd 𝓐) → (𝓐 LowExi B) → (𝓐 InfmExi B) ∧ ((𝓐 Infm B) = 𝓐 Low B) := sorry
theorem max_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 GrtExi B) → (((𝓐 Grt B) ∈ C) ↔ ((𝓐 GrtExi C) ∧ ((𝓐 Grt C) = 𝓐 Grt B))) := sorry
theorem min_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 LowExi B) → (((𝓐 Low B) ∈ C) ↔ ((𝓐 LowExi C) ∧ ((𝓐 Low C) = 𝓐 Low B))) := sorry
theorem po_max_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 GrtExi B) → (𝓐 GrtExi C) → ((𝓐 Grt C) . (≼(𝓐)) . (𝓐 Grt B)) := sorry
theorem po_min_subset_prop :
∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 LowExi B) → (𝓐 LowExi C) → ((𝓐 Low B) . (≼(𝓐)) . (𝓐 Low C)) := sorry
theorem max_inter_prop :
∀ 𝓐 B I i, i ∈ I → (PartOrd 𝓐) → (B IndxFun I) → ((𝓐 Grt (B _ i)) ∈ (⋂[ i in I ] B at i)) →
(𝓐 GrtExi (B _ i)) → ((𝓐 GrtExi (⋂[ i in I ] B at i)) ∧ ((𝓐 Grt (⋂[ i in I ] B at i)) = 𝓐 Grt (B _ i))) := sorry
theorem min_inter_prop :
∀ 𝓐 B I i, i ∈ I → (PartOrd 𝓐) → (B IndxFun I) → ((𝓐 Low (B _ i)) ∈ (⋂[ i in I ] B at i)) →
(𝓐 LowExi (B _ i)) → ((𝓐 LowExi (⋂[ i in I ] B at i)) ∧ ((𝓐 Low (⋂[ i in I ] B at i)) = 𝓐 Low (B _ i))) := sorry
theorem max_un_prop :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 GrtExi (B _ i))) →
(∀ i j ∈ I; (𝓐 Grt (B _ i)) = (𝓐 Grt (B _ j))) → ((𝓐 GrtExi (⋃[ i in I ] B at i)) ∧
(∀ s ∈ I; (𝓐 Grt ((⋃[ i in I ] B at i))) = (𝓐 Grt (B _ s)))) := sorry
theorem min_un_prop :
∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 LowExi (B _ i))) →
(∀ i j ∈ I; (𝓐 Low (B _ i)) = (𝓐 Low (B _ j))) → ((𝓐 LowExi (⋃[ i in I ] B at i)) ∧
(∀ s ∈ I; (𝓐 Low ((⋃[ i in I ] B at i))) = (𝓐 Low (B _ s)))) := sorry

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
