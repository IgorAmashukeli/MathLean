import «Header»


-- 1) Isomorphism of orders
def ispo_iso (𝓐 𝓑 f : Set) := (f Bij setPO(𝓐) To setPO(𝓑)) ∧ (∀ x y ∈ setPO(𝓐); (x . ≼(𝓐) . y) ↔ ((f⦅x⦆) . (≼(𝓑)) . (f⦅y⦆)))
syntax term "PO_ISO" term "To" term : term
macro_rules
| `($f PO_ISO $𝓐 To $𝓑) => `(ispo_iso $𝓐 $𝓑 $f)

-- 2) Isomorphism of partial orders
def ispo_iso_po (𝓐 𝓑 f : Set) := (PartOrd 𝓐) ∧ (PartOrd 𝓑) ∧ (f PO_ISO 𝓐 To 𝓑)
syntax term "PO_ISO_PO" term "To" term : term
macro_rules
| `($f PO_ISO_PO $𝓐 To $𝓑) => `(ispo_iso_po $𝓐 $𝓑 $f)

-- 3) Isomorphic orders
def pos_iso (𝓐 𝓑 : Set) := ∃ f, (f PO_ISO 𝓐 To 𝓑)
syntax term "≃O" term : term
macro_rules
| `($𝓐 ≃O $𝓑) => `(pos_iso $𝓐 $𝓑)

-- 4) Isomorphic partial orders
def pos_iso_po (𝓐 𝓑 : Set) := (PartOrd 𝓐) ∧ (PartOrd 𝓑) ∧ (𝓐 ≃O 𝓑)
syntax term "P≃O" term : term
macro_rules
| `($𝓐 P≃O $𝓑) => `(pos_iso_po $𝓐 $𝓑)



--- 5) Main properties of isomorphis reflexivity, symmetry, transitivity, equinumerosity of sets
theorem iso_equin : ∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (setPO(𝓐) ~ setPO(𝓑)) := sorry
theorem iso_refl : ∀ 𝓐, (𝓐 ≃O 𝓐) := sorry
theorem iso_symm : ∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (𝓑 ≃O 𝓐) := sorry
theorem iso_trans : ∀ 𝓐 𝓑 𝓒, (𝓐 ≃O 𝓑) → (𝓑 ≃O 𝓒) → (𝓐 ≃O 𝓒) := sorry


-- 6) Simple properties that doesn't change through isomorphism in different partial ordered set
theorem iso_in₀ : ∀ 𝓐 𝓑 f x, (f PO_ISO 𝓐 To 𝓑) → (x ∈ setPO(𝓐)) → ((f⦅x⦆)) ∈ setPO(𝓑) := sorry
theorem iso_in₁ : ∀ 𝓐 𝓑 f x, (f PO_ISO 𝓐 To 𝓑) → (x ∈ setPO(𝓐)) → ((x ∈ setPO(𝓐)) ↔ ((f⦅x⦆)) ∈ setPO(𝓑)) := sorry
theorem iso_in₂ : ∀ 𝓐 𝓑 T f x, (x ∈ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → ((x ∈ T) ↔ (f⦅x⦆) ∈ f.[T]) := sorry
theorem iso_R₂ : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → ∀ x y ∈ setPO(𝓐); (x . ≼(𝓐) . y) ↔ ((f⦅x⦆) . (≼(𝓑)) . (f⦅y⦆)) := sorry
theorem iso_eq : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → ∀ x y ∈ setPO(𝓐); (x = y) ↔ ((f⦅x⦆) = (f⦅y⦆)) := sorry
theorem iso_R₁ : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (PartOrd 𝓐) → (PartOrd 𝓑) → (∀ x y ∈ setPO(𝓐); (x . ≺(𝓐) . y) ↔ ((f⦅x⦆) . (≺(𝓑)) . (f⦅y⦆))) := sorry


-- 7) Logical properties that doesn't change through isomorphism in different partial ordered sets
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


-- 8) Using the above theorems about isomorphism for particular properties
theorem poiso_minal : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_minimal 𝓐 X x) ↔ (is_minimal 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_maxal : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_maximal 𝓐 X x) ↔ (is_maximal 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_minum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_lowest 𝓐 X x) ↔ (is_lowest 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_maxum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_greatest 𝓐 X x) ↔ (is_greatest 𝓑 (f.[X]) (f⦅x⦆))) := sorry
theorem poiso_lowbou : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_lower_bound 𝓐 X x) ↔ (is_lower_bound 𝓑 (f.[X]) (f⦅x⦆)) ) := sorry
theorem poiso_uppbou : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_upper_bound 𝓐 X x) ↔ (is_upper_bound 𝓑 (f.[X]) (f⦅x⦆)) ) := sorry
theorem poiso_minexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 LowExi X) ↔ (𝓑 LowExi f.[X])) := sorry
theorem poiso_maxexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 GrtExi X) ↔ (𝓑 GrtExi f.[X])) := sorry


-- 9) Theorems about equal subsets because of isomorphism and its application for particular subsets
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



-- 10) Theorem about equal element constructions because of isomorphism and its applications
theorem poiso_elconstr  (φ : Set → Set → Set → Prop ) (ψ : Set → Set → Set) (cond : Set → Set → Prop)  :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (cond 𝓐 X) → (cond 𝓑 (f.[X])) → (f PO_ISO_PO 𝓐 To 𝓑) →
(∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (PartOrd 𝓧) → (cond 𝓧 X) → ψ 𝓧 X ∈ setPO(𝓧)) →
(∀ 𝓧 X t, (PartOrd 𝓧) → (cond 𝓧 X) →  ((φ 𝓧 X (t) ↔ (t = ψ 𝓧 X)))) →
(∀ X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆)))) →
(f⦅ψ 𝓐 X⦆ = ψ 𝓑 (f.[X])) := sorry



theorem poiso_minumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 LowExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Low X⦆ = 𝓑 Low (f.[X])) := sorry
theorem poiso_maxumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 GrtExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Grt X⦆ = 𝓑 Grt (f.[X])) := sorry
theorem poiso_supel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 SuprExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Supr X⦆ = 𝓑 Supr (f.[X])) := sorry
theorem poiso_infel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Infm X⦆ = 𝓑 Infm (f.[X])) := sorry


-- 11 ) Properties about partial order itself also doesn't change through isomorphism

theorem poiso_if_then_iff (φ : Set → Prop) :
(∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → (φ 𝓐) → (φ 𝓑)) → (∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((φ 𝓐) ↔ (φ 𝓑))) := sorry
theorem poiso_subset_prop (φ : Set → Set → Prop) :
(∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X) ↔ (φ 𝓑 (f.[X])))) →
(∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((∀ X, (X ⊆ setPO(𝓐)) → (φ 𝓐 X)) ↔ (∀ X, (X ⊆ setPO(𝓑)) → (φ 𝓑 X)))) := sorry

theorem poiso_semilatt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((SemiLatt 𝓐) ↔ (SemiLatt 𝓑)) := sorry
theorem poiso_latt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((Latt 𝓐) ↔ (Latt 𝓑)) := sorry
theorem poiso_complatt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((CompLatt 𝓐) ↔ (CompLatt 𝓑)) := sorry
theorem poiso_linord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((LinOrd 𝓐) ↔ (LinOrd 𝓑)) := sorry
theorem poiso_wellfo : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((WellFoundOrd 𝓐) ↔ (WellFoundOrd 𝓑)) := sorry
theorem poiso_welord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((WellOrd 𝓐) ↔ (WellOrd 𝓑)) := sorry


-- 12) Partial order isomorphism translates through different partial order constructions

theorem poiso_inv : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((inv_PO 𝓐) P≃O (inv_PO 𝓑)) := sorry
theorem poiso_subs : ∀ 𝓐 𝓑 f X, (X ≠ ∅) → (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 SubsPO X) P≃O (𝓑 SubsPO (f.[X]))) := sorry
theorem poiso_inter : ∀ 𝓐 𝓑 𝓒 𝓓 f, (setPO(𝓐) ∩ setPO(𝓒) ≠ ∅) →
(setPO(𝓑) ∩ setPO(𝓓) ≠ ∅) → (f PO_ISO_PO 𝓐 To 𝓑) → (f PO_ISO_PO 𝓒 To 𝓓) → (f PO_ISO_PO (𝓐 InterPO 𝓒) To (𝓑 InterPO 𝓓)) := sorry
theorem poiso_cart : ∀ 𝓐 𝓑 𝓒 𝓓, (𝓐 P≃O 𝓑) → (𝓒 P≃O 𝓓) → ((𝓐 Cart2CordPO 𝓒) P≃O (𝓑 Cart2CordPO 𝓓)) := sorry


-- 13) induced order with order function saving creates isomorphic partial order

noncomputable def induced_R₂ (𝓐 f: Set) := {s ∈ (rng f) × (rng f) | ∃ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∧ s = (f⦅x⦆, f⦅y⦆)}
noncomputable def induced_order (𝓐 f: Set) := ⁅rng f; str (rng f) (induced_R₂ 𝓐 f); (induced_R₂ 𝓐 f)⁆
theorem poiso_induced : ∀ 𝓐 f X, (PartOrd 𝓐) → (f Inj (setPO(𝓐)) To X) → (f PO_ISO_PO 𝓐 To (induced_order 𝓐 f)) := sorry
