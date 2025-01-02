
import «Header»


-- 1) semilattice
def is_semilattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧ (∀ x y ∈ (setPO(𝓐)); (𝓐 InfmExi ({x, y})))
syntax "SemiLatt" term : term
macro_rules
| `(SemiLatt $𝓐) => `(is_semilattice $𝓐)


-- 2) semilattice on different structures
theorem sum_semilatt : ∀ 𝓐 𝓑, (SemiLatt 𝓐) → (SemiLatt 𝓑) → (SemiLatt (𝓐 P⨁O 𝓑)) := sorry


-- 3) any impodent associative commutative operations creates a semilattice
def is_operation (A f : Set) : Prop := f Fun (A × A) To A
def is_impodent_op (A f : Set) : Prop := ∀ x ∈ A; f⦅x; x⦆ = x
def is_commut_op (A f : Set) : Prop := ∀ x y ∈ A; f⦅x; y⦆ = f⦅y ; x⦆
def is_assoc_op (A f : Set) : Prop := ∀ x y z ∈ A; f⦅f⦅x; y⦆; z⦆ = f⦅x; f⦅y;z⦆⦆
def is_semilattfunc (A f : Set) : Prop := (f Fun (A × A) To A) ∧ is_impodent_op A f ∧ is_commut_op A f ∧ is_assoc_op A f
syntax term "SemLatFunOn" term : term
macro_rules
| `($f SemLatFunOn $A) => `(is_semilattfunc $A $f)
noncomputable def leq_semifunclatt (A f) := {(x, y) ∈ A × A | f⦅x; y⦆ = x}
noncomputable def fun_semilat (A f) := ⁅A; str A (leq_semifunclatt A f); (leq_semifunclatt A f)⁆
syntax term "SemLatF" term : term
macro_rules
| `($A SemLatF $f) => `(fun_semilat $A $f)

theorem semilatt_op : ∀ A f, (f SemLatFunOn A) → (SemiLatt (A SemLatF f)) ∧ (∀ x y ∈ A; f⦅x; y⦆ = (A SemLatF f) Infm {x, y}) := sorry

-- 4) lattice
def is_lattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ x y ∈ (setPO(𝓐)); (𝓐 SuprExi ({x, y})) ∧ (𝓐 InfmExi ({x, y})))
syntax "Latt" term : term
macro_rules
| `(Latt $𝓐:term) => `(is_lattice $𝓐)

-- 6) lattice criterion
theorem latt_is_semilatt : ∀ 𝓐, (Latt 𝓐) → (SemiLatt 𝓐) := sorry
theorem latt_as_semilatts : ∀ 𝓐, (Latt 𝓐) ↔ ((SemiLatt 𝓐) ∧ (SemiLatt (invPO 𝓐))) := sorry

-- 7) lattice on different structures
theorem latt_inv : ∀ 𝓐, (PartOrd 𝓐) → ((Latt 𝓐) ↔ (Latt (invPO 𝓐))) := sorry
theorem sum_latt : ∀ 𝓐 𝓑, (Latt 𝓐) → (Latt 𝓑) → (Latt (𝓐 P⨁O 𝓑)) := sorry

-- 8) boolean partial order with subset relation is lattice (and therefore semilattice)
theorem boolean_Latt : ∀ A, (Latt (BoolPO A)) := sorry
theorem boolean_semiLatt : ∀ A, (SemiLatt (BoolPO A)) := sorry




-- 9) Complete lattice
def is_complete_lattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ X, (X ⊆ setPO(𝓐)) → (𝓐 SuprExi X))
syntax "CompLatt" term : term
macro_rules
| `(CompLatt $𝓐) => `(is_complete_lattice $𝓐)

-- 10) another complete lattice criterion
theorem compl_latt_inf_crit : ∀ 𝓐, (CompLatt 𝓐) ↔ (∀ X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X)) := sorry

-- 11) complete lattice on different structures
theorem compl_latt_is_latt : ∀ 𝓐, (CompLatt 𝓐) → (Latt 𝓐) := sorry
theorem compllatt_inv : ∀ 𝓐, (PartOrd 𝓐) → ((CompLatt 𝓐) ↔ (CompLatt (invPO 𝓐))) := sorry
theorem sum_complatt : ∀ 𝓐 𝓑, (CompLatt 𝓐) → (CompLatt 𝓑) → (CompLatt (𝓐 P⨁O 𝓑)) := sorry
theorem Knaster_Tarski_lemma₀ : ∀ 𝓐, ∀ a b ∈ setPO(𝓐); (a . ≼(𝓐) . b) → (CompLatt 𝓐) → (CompLatt (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐))) := sorry


-- 12) boolean partial order with subset relation is complete lattice
theorem boolean_CompLatt : ∀ A, (CompLatt (BoolPO A)) := sorry


-- 13) Knaster Tarski theorem about fixpoint set of monotonic function on complete lattice
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


theorem Knaster_Tarski_lemma₁ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (𝓐 GrtExi (f FixOn 𝓐)) := sorry
theorem Knaster_Tarski_lemma₂ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → ((f FixOn 𝓐) ≠ ∅) := sorry
theorem Knaster_Tarski_theorem : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (CompLatt (𝓐 SubsPO (f FixOn 𝓐))) := sorry



-- 14) linear order and it's obvious properties
def is_linear_order (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧ (str_conn (≼(𝓐)) setPO(𝓐))
syntax "LinOrd" term : term
macro_rules
| `(LinOrd $𝓐) => `(is_linear_order $𝓐)

theorem lin_ord_prop : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∨ (y . (≼(𝓐)) . x)) := sorry
theorem lin_ord_wk_prop : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (x ≠ y) → ((x . ≺(𝓐) . y) ∨ (y . (≺(𝓐)) . x))) := sorry
theorem lin_ord_nR₁ : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (¬ (x . (≺(𝓐)) . y)) → (y . (≼(𝓐)) . x)) := sorry
theorem lin_ord_nR₂ : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (¬ (x . (≼(𝓐)) . y)) → (y . (≺(𝓐)) . x)) := sorry


-- 15) linear order properties with min/max/low/grt/inf/sup
theorem linmin_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_minimal 𝓐 X x) ↔ (is_lowest 𝓐 X x)) := sorry
theorem linmax_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_maximal 𝓐 X x) ↔ (is_greatest 𝓐 X x)) := sorry
theorem linmin_al_sub_cmp : ∀ 𝓐 B C x y, (LinOrd 𝓐) →
(C ⊆ B) → (B ⊆ setPO(𝓐)) → (is_minimal 𝓐 B x) → (is_minimal 𝓐 C y) → (x . ≼(𝓐) . y) := sorry
theorem linmax_al_sub_cmp : ∀ 𝓐 B C x y, (LinOrd 𝓐) →
(C ⊆ B) → (B ⊆ setPO(𝓐)) → (is_maximal 𝓐 B x) → (is_maximal 𝓐 C y) → (y . ≼(𝓐) . x) := sorry
theorem lin_al_min_inter_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))
→ (B IndxFun I) → (is_minimal 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_minimal 𝓐 ((B _ i)) y) → (y . ≼(𝓐) . x) := sorry
theorem lin_al_max_inter_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B IndxFun I) → (is_maximal 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_maximal 𝓐 ((B _ i)) y) → (x . ≼(𝓐) . y) := sorry
theorem lin_partmin_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 LowExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_minimal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_minimal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimal 𝓐 (B _ i) y} x)) := sorry
theorem lin_partmax_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 GrtExi (B _ i))) →
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


-- 16) linear order on different structures
theorem inv_is_LO : ∀ 𝓐, (LinOrd 𝓐) → (LinOrd (invPO 𝓐)) := sorry
theorem sub_is_LO : ∀ 𝓐 B, (B ≠ ∅) → (LinOrd 𝓐) → (B ⊆ setPO(𝓐)) → (LinOrd (𝓐 SubsPO B)) := sorry
theorem sum_is_LO : ∀ 𝓐 𝓑, (LinOrd 𝓐) → (LinOrd 𝓑) → (LinOrd (𝓐 P⨁O 𝓑)) := sorry

-- 17) any linear order is lattice
theorem lin_latt : ∀ 𝓐, (LinOrd 𝓐) → (Latt 𝓐) := sorry


-- 18) Well founded order and well ordered set definition


def is_well_found_order 𝓐 := (PartOrd 𝓐) ∧ (∀ X, ( (X ⊆ setPO(𝓐)) → (X ≠ ∅) → (𝓐 LowExi X)))
syntax "WellFoundOrd" term : term
macro_rules
| `(WellFoundOrd $𝓐) => `(is_well_found_order $𝓐)
def is_well_order 𝓐 := (LinOrd 𝓐) ∧ ∀ X, (X ⊆ setPO(𝓐)) → (X ≠ ∅) → (𝓐 LowExi X)
syntax "WellOrd" term : term
macro_rules
| `(WellOrd $𝓐) => `(is_well_order $𝓐)

theorem wellord_wellfoundcrit : ∀ 𝓐, (WellOrd 𝓐) ↔ ((LinOrd 𝓐) ∧ (WellFoundOrd 𝓐)) := sorry


-- 19) well order and well foundedness on different structures
theorem well_found : ∀ 𝓐 𝓑, (WellFoundOrd 𝓐) → (WellFoundOrd 𝓑) → (WellFoundOrd (𝓐 P⨁O 𝓑)) := sorry
theorem well_ord : ∀ 𝓐 𝓑, (WellOrd 𝓐) → (WellOrd 𝓑) → (WellOrd (𝓐 P⨁O 𝓑)) := sorry


-- 20) chain and anti chain and some of their properties

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
