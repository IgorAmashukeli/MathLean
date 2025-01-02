import «Header»


-- 0) intervals and their obvious properties
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
theorem lrc_min : ∀ 𝓐, ∀ a ∈ setPO(𝓐); ∀ b, (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_lowest 𝓐 (⟦ a ; b ⟧ of 𝓐) a) := sorry
theorem lrc_max : ∀ 𝓐 a, ∀ b ∈ setPO(𝓐); (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_greatest 𝓐 (⟦ a ; b ⟧ of 𝓐) b) := sorry



-- 1) inverse order
noncomputable def inv_PO (𝓐) := ⁅setPO(𝓐); ≻(𝓐); ≽(𝓐)⁆
syntax "invPO" term : term
macro_rules
| `(invPO $𝓐:term) => `(inv_PO $𝓐)


theorem inv_is_PO : ∀ 𝓐, (PartOrd 𝓐) → (PartOrd (invPO 𝓐) ) := sorry
theorem invinv_po_is_po : ∀ 𝓐, (PartOrd 𝓐) → ( invPO (invPO 𝓐)) = 𝓐 := sorry
theorem inv_PO_less : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≺(invPO 𝓐)) . y) ↔ (y . (≺(𝓐)) . x) := sorry
theorem inv_PO_lesseq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≼(invPO 𝓐)) . y) ↔ (y . (≼(𝓐)) . x)  := sorry

-- 2) min/max/grt/low/sup/inf in inverse order
theorem min_max_inv_al : ∀ 𝓐 B x, ((is_minimal 𝓐 B x) ↔ (is_maximal (invPO 𝓐) B x)) := sorry
theorem max_min_inv_al : ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_maximal 𝓐 B x) ↔ (is_minimal (invPO 𝓐) B x)) := sorry
theorem min_max_inv_um :  ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_lowest 𝓐 B x) ↔ (is_greatest (invPO 𝓐) B x)) := sorry
theorem max_min_inv_um :  ∀ 𝓐 B x, ((is_greatest 𝓐 B x) ↔ (is_lowest (invPO 𝓐) B x)) := sorry
theorem min_max_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (max_set 𝓐 B = min_set (invPO 𝓐) B) := sorry
theorem max_min_set_inv : ∀ 𝓐 B, (min_set 𝓐 B = max_set (invPO 𝓐) B) := sorry
theorem inv_low_upp_bou : ∀ 𝓐 B x, (is_upper_bound 𝓐 B x) ↔ (is_lower_bound (invPO 𝓐) B x) := sorry
theorem inv_upp_low_bou : ∀ 𝓐 B, (PartOrd 𝓐) → ∀ x, (is_lower_bound 𝓐 B x) ↔ (is_upper_bound (invPO 𝓐) B x) := sorry
theorem low_bou_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 ▾ B) = ((invPO 𝓐) ▴ B) := sorry
theorem upp_bou_set_inv :  ∀ 𝓐 B, (𝓐 ▴ B) = ((invPO 𝓐) ▾ B) := sorry
theorem inv_is_sup_inf : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_supremum 𝓐 B x) ↔ (is_infimum (invPO 𝓐) B x)) := sorry
theorem inv_is_inf_sup : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_infimum 𝓐 B x) ↔ (is_supremum (invPO 𝓐) B x)) := sorry
theorem max_min_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 GrtExi B) → (((invPO 𝓐) LowExi B) ∧ ((𝓐 Grt B) = (invPO(𝓐)) Low B)) := sorry
theorem min_max_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 LowExi B) → (((invPO 𝓐) GrtExi B) ∧ ((𝓐 Low B) = (invPO(𝓐)) Grt B)) := sorry


-- 3) Order, defined on some subset
noncomputable def subs_part_ord (𝓐 X) := ⁅X; ≺(𝓐) spec X; ≼(𝓐) spec X⁆
syntax term "SubsPO" term : term
macro_rules
| `($𝓐 SubsPO $X) => `(subs_part_ord $𝓐 $X)
theorem sub_is_PO : ∀ 𝓐 B, (B ≠ ∅) → (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (PartOrd (𝓐 SubsPO B)) := sorry


-- 4) Intersection of two orders
noncomputable def setintpo (𝓐 𝓑) := setPO(𝓐) ∩ setPO(𝓑)
noncomputable def le_int (𝓐 𝓑) := (≺(𝓐) spec (setintpo 𝓐 𝓑)) ∩ (≺(𝓑) spec (setintpo 𝓐 𝓑))
noncomputable def leq_int (𝓐 𝓑) := (≼(𝓐) spec (setintpo 𝓐 𝓑)) ∩ (≼(𝓑) spec (setintpo 𝓐 𝓑))
noncomputable def inter_part_ord (𝓐 𝓑) := (setintpo 𝓐 𝓑) StrIntro (le_int 𝓐 𝓑)
syntax term "InterPO" term : term
macro_rules
| `($𝓐 InterPO $𝓑) => `(inter_part_ord $𝓐 $𝓑)

theorem inter_is_PO_PO :∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (setPO(𝓐) ∩ setPO(𝓑) ≠ ∅) → (PartOrd (𝓐 InterPO 𝓑)) := sorry
theorem inter_leq : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (setPO(𝓐) ∩ setPO(𝓑) ≠ ∅) →
∀ x y ∈ setPO(𝓐 InterPO 𝓑); (x . ≼(𝓐 InterPO 𝓑) . y) ↔ (x . (leq_int 𝓐 𝓑) . y) := sorry


-- 5) Sum of two orders
noncomputable def setpo_disj2 (𝓐 𝓑) := setPO(𝓐) ⊔ setPO(𝓑)
def disj_pred2_R₁ (𝓐 𝓑) := fun (x : Set) => fun (y : Set) => ((π₂ x) = l2 ∧ (π₂ y) = l2 ∧ ((π₁ x) . ≺(𝓐) . (π₁ y))) ∨
  ((π₂ x) = r2 ∧ (π₂ y) = r2 ∧ ((π₁ x) . ≺(𝓑) . (π₁ y))) ∨
  ((π₁ x) ∈ setPO(𝓐) ∧ (π₁ y) ∈ setPO(𝓑) ∧ (π₂ x) = l2 ∧ (π₂ y) = r2)
def disj_pred2_R₂ (𝓐 𝓑) := fun (x : Set) => fun (y : Set) => ((π₂ x) = l2 ∧ (π₂ y) = l2 ∧ ((π₁ x) . ≼(𝓐) . (π₁ y))) ∨
  ((π₂ x) = r2 ∧ (π₂ y) = r2 ∧ ((π₁ x) . ≼(𝓑) . (π₁ y))) ∨
  ((π₁ x) ∈ setPO(𝓐) ∧ (π₁ y) ∈ setPO(𝓑) ∧ (π₂ x) = l2 ∧ (π₂ y) = r2)
noncomputable def le_disj2 (𝓐 𝓑) := {(x, y) ∈ (setpo_disj2 𝓐 𝓑) × (setpo_disj2 𝓐 𝓑) | disj_pred2_R₁ 𝓐 𝓑 x y }

noncomputable def po_disj2 (𝓐 𝓑) := ((setpo_disj2 𝓐 𝓑) StrIntro (le_disj2 𝓐 𝓑))
syntax term "P⨁O" term : term
macro_rules
| `($𝓐 P⨁O $𝓑) => `(po_disj2 $𝓐 $𝓑)


theorem sum_is_PO : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (PartOrd (𝓐 P⨁O 𝓑)) := sorry
theorem sum_PO_less : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (∀ x y ∈ setPO(𝓐 P⨁O 𝓑); ((x . ≺(𝓐 P⨁O 𝓑) . y) ↔ (disj_pred2_R₁ 𝓐 𝓑 x y))) := sorry
theorem sum_PO_lesseq : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (∀ x y ∈ setPO(𝓐 P⨁O 𝓑); ((x . ≼(𝓐 P⨁O 𝓑) . y) ↔ (disj_pred2_R₂ 𝓐 𝓑 x y))) := sorry



-- 6) Coordinate cartesian order
noncomputable def po_set_cart (𝓐 𝓑) := setPO(𝓐) × setPO(𝓑)
def po_set_prop (𝓐 𝓑) := fun (s) => ∃ x₁ ∈ setPO(𝓐); ∃ y₁ ∈ setPO(𝓑); ∃ x₂ ∈ setPO(𝓐); ∃ y₂ ∈ setPO(𝓑);
(s = ((x₁, y₁), (x₂, y₂))) ∧ (x₁ . ≼(𝓐) . x₂) ∧ (y₁ . ≼(𝓑) . y₂)

noncomputable def leq_cart (𝓐 𝓑) := {s ∈ (po_set_cart 𝓐 𝓑) × (po_set_cart 𝓐 𝓑) | po_set_prop 𝓐 𝓑 s}

noncomputable def le_cart (𝓐 𝓑) := str (setPO(𝓐) × setPO(𝓑)) (leq_cart 𝓐 𝓑)

noncomputable def cartesian2_coordinate_part_ord (𝓐 𝓑) := ⁅setPO(𝓐) × setPO(𝓑); le_cart 𝓐 𝓑; leq_cart 𝓐 𝓑⁆
syntax term "Cart2CordPO" term : term
macro_rules
| `($𝓐 Cart2CordPO $𝓑) => `(cartesian2_coordinate_part_ord $𝓐 $𝓑)

theorem poset_cart_prop₁ : ∀ 𝓐 𝓑, ∀ s ∈ po_set_cart 𝓐 𝓑; (π₁ s) ∈ (setPO(𝓐)) := sorry
theorem poset_cart_prop₂ : ∀ 𝓐 𝓑, ∀ s ∈ po_set_cart 𝓐 𝓑; (π₂ s) ∈ (setPO(𝓑)) := sorry
theorem leq_cart_prop : ∀ 𝓐 𝓑, ∀ s₁ s₂ ∈ po_set_cart 𝓐 𝓑; ((s₁ . (leq_cart 𝓐 𝓑) . s₂) ↔ (((π₁ s₁) . ≼(𝓐) . (π₁ s₂)) ∧ ((π₂ s₁) . ≼(𝓑) . (π₂ s₂)))) := sorry
theorem cart_PO_PO : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (PartOrd (𝓐 Cart2CordPO 𝓑)) := sorry





-- 7) Boolean set with subset relation is (𝒫 A, ⊊, ⊆) a partial order

noncomputable def sub_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊆ C ∧ z = (B, C) }
noncomputable def subneq_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊊ C ∧ z = (B, C) }
noncomputable def boolean_PO_set (A) := ⁅(𝒫 A); (subneq_binrel A); (sub_binrel A)⁆
syntax "BoolPO" term : term
macro_rules
| `(BoolPO $A:term) => `(boolean_PO_set $A)

theorem NSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (sub_binrel A) ↔ (B ⊆ C) := sorry
theorem SNSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (subneq_binrel A) ↔ (B ⊊ C) := sorry
theorem NSPO_bool_pair_prop_pa : ∀ A B C, (B, C) ∈ (sub_binrel A) ↔ (B ⊆ C ∧ B ∈ 𝒫 A ∧ C ∈ 𝒫 A) := sorry
theorem SPO_bool_pair_prop_pa : ∀ A B C, (B, C) ∈ (subneq_binrel A) ↔ (B ⊊ C ∧ B ∈ 𝒫 A ∧ C ∈ 𝒫 A) := sorry
theorem boolean_PO : ∀ A, (PartOrd (BoolPO A)) := sorry
