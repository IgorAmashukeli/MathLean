import «Header»



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


theorem lro_sub_all : ∀ 𝓐 a b, ( ⦗ a ; b ⦘ of 𝓐 ) ⊆ setPO(𝓐) :=
  fun (𝓐 a b) =>
    let P := fun (x) => (a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)
    let A := setPO(𝓐)
    specification_set_subset P A
theorem lcro_sub_all : ∀ 𝓐 a b, ( ⟦ a ; b ⦘ of 𝓐) ⊆ setPO(𝓐) :=
  fun (𝓐 a b) =>
    let P := fun (x) => (a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)
    let A := setPO(𝓐)
    specification_set_subset P A
theorem lorc_sub_all : ∀ 𝓐 a b, ( ⦗ a ; b ⟧ of 𝓐) ⊆ setPO(𝓐) :=
  fun (𝓐 a b) =>
    let P := fun (x) => (a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)
    let A := setPO(𝓐)
    specification_set_subset P A
theorem lrc_sub_all : ∀ 𝓐 a b, ( ⟦ a ; b ⟧ of 𝓐) ⊆ setPO(𝓐) :=
  fun (𝓐 a b) =>
    let P := fun (x) => (a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)
    let A := setPO(𝓐)
    specification_set_subset P A
theorem lc_sub_all : ∀ 𝓐 a, ( ⟦ a ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐) :=
  fun (𝓐 a) =>
    let P := fun (x) => (a . (≼(𝓐)) . x)
    let A := setPO(𝓐)
    specification_set_subset P A
theorem rc_sub_all : ∀ 𝓐 b, ( ⦗ -∞ ; b ⟧ of 𝓐) ⊆ setPO(𝓐) :=
  fun (𝓐 b) =>
    let P := fun (x) => (x . (≼(𝓐)) . b)
    let A := setPO(𝓐)
    specification_set_subset P A
theorem lo_sub_all : ∀ 𝓐 a, ( ⦗ a ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐) :=
  fun (𝓐 a) =>
    let P := fun (x) => (a . (≺(𝓐)) . x)
    let A := setPO(𝓐)
    specification_set_subset P A
theorem ro_sub_all : ∀ 𝓐 b, ( ⦗ -∞ ; b ⦘ of 𝓐) ⊆ setPO(𝓐) :=
  fun (𝓐 b) =>
    let P := fun (x) => (x . (≺(𝓐)) . b)
    let A := setPO(𝓐)
    specification_set_subset P A
theorem f_sub_all :  ∀ 𝓐, (⦗ -∞ ; +∞ ⦘ of 𝓐) ⊆ setPO(𝓐) :=
  fun (𝓐) =>
    subset_refl (setPO(𝓐))
theorem f_eq_all : ∀ 𝓐, (⦗ -∞ ; +∞  ⦘ of 𝓐) = setPO(𝓐) :=
  fun (𝓐) =>
    Eq.refl (setPO(𝓐))


theorem lro_is_lro : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; b ⦘ of 𝓐) ↔ ((a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)) :=
  fun (𝓐 a b) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let P := fun (x) => (a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)
        let A := setPO(𝓐)
        let u := spec_is_spec P A x
        Iff.intro
        (
          fun (hxi : x ∈ ⦗ a ; b ⦘ of 𝓐) =>
            And.right (Iff.mp u hxi)
        )
        (
          fun (hxpr : (a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)) =>
            Iff.mpr u (And.intro (hx) (hxpr))
        )


theorem lcro_is_lcro : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; b ⦘ of 𝓐) ↔ ((a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)) :=
  fun (𝓐 a b) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let P := fun (x) => (a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)
        let A := setPO(𝓐)
        let u := spec_is_spec P A x
        Iff.intro
        (
          fun (hxi : x ∈ ⟦ a ; b ⦘ of 𝓐) =>
            And.right (Iff.mp u hxi)
        )
        (
          fun (hxpr : (a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)) =>
            Iff.mpr u (And.intro (hx) (hxpr))
        )


theorem locr_is_locr : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; b ⟧ of 𝓐) ↔ ((a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)) :=
  fun (𝓐 a b) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let P := fun (x) => (a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)
        let A := setPO(𝓐)
        let u := spec_is_spec P A x
        Iff.intro
        (
          fun (hxi : x ∈ ⦗ a ; b ⟧ of 𝓐) =>
            And.right (Iff.mp u hxi)
        )
        (
          fun (hxpr : (a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)) =>
            Iff.mpr u (And.intro (hx) (hxpr))
        )


theorem lrc_is_lrc : ∀ 𝓐 a b, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; b ⟧ of 𝓐) ↔ ((a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)) :=
  fun (𝓐 a b) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let P := fun (x) => (a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)
        let A := setPO(𝓐)
        let u := spec_is_spec P A x
        Iff.intro
        (
          fun (hxi : x ∈ ⟦ a ; b ⟧ of 𝓐) =>
            And.right (Iff.mp u hxi)
        )
        (
          fun (hxpr : (a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)) =>
            Iff.mpr u (And.intro (hx) (hxpr))
        )


theorem lc_is_lc : ∀ 𝓐 a, ∀ x ∈ setPO(𝓐); (x ∈ ⟦ a ; +∞ ⦘ of 𝓐) ↔ (a . (≼(𝓐)) . x) :=
  fun (𝓐 a) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let P := fun (x) => (a . (≼(𝓐)) . x)
        let A := setPO(𝓐)
        let u := spec_is_spec P A x
        Iff.intro
        (
          fun (hxi : x ∈ ⟦ a ; +∞ ⦘ of 𝓐) =>
            And.right (Iff.mp u hxi)
        )
        (
          fun (hxpr : (a . (≼(𝓐)) . x)) =>
            Iff.mpr u (And.intro (hx) (hxpr))
        )


theorem rc_is_rc : ∀ 𝓐 b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; b ⟧ of 𝓐) ↔ (x . (≼(𝓐)) . b) :=
  fun (𝓐 b) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let P := fun (x) => (x . (≼(𝓐)) . b)
        let A := setPO(𝓐)
        let u := spec_is_spec P A x
        Iff.intro
        (
          fun (hxi : x ∈ ⦗ -∞ ; b ⟧ of 𝓐) =>
            And.right (Iff.mp u hxi)
        )
        (
          fun (hxpr : (x . (≼(𝓐)) . b)) =>
            Iff.mpr u (And.intro (hx) (hxpr))
        )


theorem lo_is_lo : ∀ 𝓐 a, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ a ; +∞ ⦘ of 𝓐) ↔ (a . (≺(𝓐)) . x) :=
  fun (𝓐 a) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let P := fun (x) => (a . (≺(𝓐)) . x)
        let A := setPO(𝓐)
        let u := spec_is_spec P A x
        Iff.intro
        (
          fun (hxi : x ∈ ⦗ a ; +∞ ⦘ of 𝓐) =>
            And.right (Iff.mp u hxi)
        )
        (
          fun (hxpr : (a . (≺(𝓐)) . x)) =>
            Iff.mpr u (And.intro (hx) (hxpr))
        )


theorem ro_is_ro : ∀ 𝓐 b, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; b ⦘ of 𝓐) ↔ (x . (≺(𝓐)) . b) :=
  fun (𝓐 b) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let P := fun (x) => (x . (≺(𝓐)) . b)
        let A := setPO(𝓐)
        let u := spec_is_spec P A x
        Iff.intro
        (
          fun (hxi : x ∈ ⦗ -∞ ; b ⦘ of 𝓐) =>
            And.right (Iff.mp u hxi)
        )
        (
          fun (hxpr : (x . (≺(𝓐)) . b)) =>
            Iff.mpr u (And.intro (hx) (hxpr))
        )


theorem full_is_full : ∀ 𝓐, ∀ x ∈ setPO(𝓐); (x ∈ ⦗ -∞ ; +∞ ⦘ of 𝓐) :=
  fun (𝓐) =>
    fun (x) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        hx


theorem lrc_nemp : ∀ 𝓐, ∀ a ∈ setPO(𝓐); ∀ b, (PartOrd 𝓐) → ((⟦ a ; b ⟧ of 𝓐) ≠ ∅ ↔ (a . ≼(𝓐) . b)) :=
  fun (𝓐) =>
    fun (a) =>
      fun (ha : (a ∈ setPO(𝓐))) =>
        fun (b) =>
            fun (h𝓐 : (PartOrd 𝓐)) =>
                Iff.intro
                (
                  fun (hnemp : (⟦ a ; b ⟧ of 𝓐) ≠ ∅) =>
                    let u := Iff.mp (set_non_empty_iff_non_empty (⟦ a ; b ⟧ of 𝓐)) hnemp
                    Exists.elim u
                    (
                      fun (x) =>
                        fun (hx : x ∈ (⟦ a ; b ⟧ of 𝓐)) =>
                          let v₀ := lrc_sub_all 𝓐 a b x hx
                          let v := Iff.mp (lrc_is_lrc 𝓐 a b x v₀) hx
                          trans_R₂ 𝓐 h𝓐 a x b (And.left v) (And.right v)

                    )
                )
                (
                  fun (hab : (a . ≼(𝓐) . b)) =>
                    fun (hemp : (⟦ a ; b ⟧ of 𝓐) = ∅) =>
                      Iff.mp (set_empty_iff_empty (⟦ a ; b ⟧ of 𝓐)) hemp a (
                        Iff.mpr (lrc_is_lrc 𝓐 a b a ha) (
                          And.intro (refl_R₂ 𝓐 h𝓐 a ha) (hab)
                        )
                      )
                )


theorem lrc_min : ∀ 𝓐, ∀ a ∈ setPO(𝓐); ∀ b, (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_lowest 𝓐 (⟦ a ; b ⟧ of 𝓐) a) :=
  fun (𝓐) =>
    fun (a) =>
      fun (ha : a ∈ setPO(𝓐)) =>
        fun (b) =>
            fun (h𝓐 : (PartOrd 𝓐)) =>
              fun (hab : (a . ≼(𝓐) . b)) =>
                And.intro (Iff.mpr (lrc_is_lrc 𝓐 a b a ha) (And.intro (refl_R₂ 𝓐 h𝓐 a ha) (hab))) (
                  fun (x) =>
                    fun (hx : x ∈ (⟦ a ; b ⟧ of 𝓐)) =>
                      let u := lrc_sub_all 𝓐 a b x hx
                      And.left (Iff.mp (lrc_is_lrc 𝓐 a b x u) hx)
                )


theorem lrc_max : ∀ 𝓐 a, ∀ b ∈ setPO(𝓐); (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_greatest 𝓐 (⟦ a ; b ⟧ of 𝓐) b) :=
  fun (𝓐) =>
    fun (a) =>
        fun (b) =>
          fun (hb : b ∈ setPO(𝓐)) =>
            fun (h𝓐 : (PartOrd 𝓐)) =>
              fun (hab : (a . ≼(𝓐) . b)) =>
                And.intro (Iff.mpr (lrc_is_lrc 𝓐 a b b hb) (And.intro (hab) (refl_R₂ 𝓐 h𝓐 b hb))) (
                  fun (x) =>
                    fun (hx : x ∈ (⟦ a ; b ⟧ of 𝓐)) =>
                      let u := lrc_sub_all 𝓐 a b x hx
                      And.right (Iff.mp (lrc_is_lrc 𝓐 a b x u) hx)
                )



noncomputable def inv_PO (𝓐) := ⁅setPO(𝓐); ≻(𝓐); ≽(𝓐)⁆
syntax "invPO" term : term
macro_rules
| `(invPO $𝓐:term) => `(inv_PO $𝓐)



theorem inv_is_PO : ∀ 𝓐, (PartOrd 𝓐) → (PartOrd (invPO 𝓐) ) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := setPO(𝓐)
      let R₁ := ≺(𝓐)
      let R₂ := ≼(𝓐)
      let hAR := triple_po_is_po 𝓐 h𝓐
      po_is_triple_po A (R₁⁻¹) (R₂⁻¹) (
        let s := And.right (And.right hAR)
        let u := And.left (And.left (And.right hAR))
        let v := And.right (And.left (And.right hAR))
        And.intro (And.left hAR) (
          And.intro (And.intro (inv_binon A R₁ (u)) (
            And.intro (Iff.mp (irrefl_inv A R₁ u) (And.left v)) (
              Iff.mp (transit_inv A R₁ u) (And.right v)
            )
          )) (
              let first := inv_union_prop R₁ (id_ A) (bin_on_is_bin A R₁ (u)) (id_is_rel A)
              let second := eq_subst (fun (t) => (t⁻¹) = (R₁⁻¹) ∪ ((id_ A)⁻¹)) (R₁ ∪ (id_ A)) R₂ (Eq.symm (s

              )) (first)
              Eq.trans (second) (
                let third := inv_id A

                eq_subst (fun (t) => (R₁⁻¹) ∪ t = nonstr A (R₁⁻¹)) (id_ A) ((id_ A)⁻¹) (Eq.symm third) (
                  Eq.refl ((R₁⁻¹) ∪ (id_ A))
                )
              )

          )
        )
      )
theorem inv_PO_less : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≺(invPO 𝓐)) . y) ↔ (y . (≺(𝓐)) . x) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
    fun (x y) =>
      let u := lessPO_is_lessPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
      eq_subst (fun (t) => (x . t . y) ↔ (y . (≺(𝓐)) . x)) (≻(𝓐)) (≺(invPO 𝓐)) (Eq.symm u) (
        let t := And.left (And.left (And.right (triple_po_is_po 𝓐 h𝓐)))
        let s := inv_pair_prop (≺(𝓐)) (bin_on_is_bin (setPO(𝓐)) (≺(𝓐)) t) y x
        Iff.intro (Iff.mpr s) (Iff.mp s)
      )
theorem inv_PO_lesseq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≼(invPO 𝓐)) . y) ↔ (y . (≼(𝓐)) . x) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x y) =>
        let u := lesseqPO_is_lesseqPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
        eq_subst (fun (t) => (x . t . y) ↔ (y . (≼(𝓐)) . x)) (≽(𝓐)) (≼(invPO 𝓐)) (Eq.symm u) (
          let t := And.left (And.left (And.right (Iff.mp (part_ord_nspo_crit (setPO(𝓐)) (≺(𝓐)) (≼(𝓐))) (
            triple_po_is_po (𝓐) (h𝓐)))))
          let s := inv_pair_prop (≼(𝓐)) (bin_on_is_bin (setPO(𝓐)) (≼(𝓐)) t) y x
          Iff.intro (Iff.mpr s) (Iff.mp s)
        )


theorem invinv_po_is_po : ∀ 𝓐, (PartOrd 𝓐) → (invPO (invPO 𝓐)) = 𝓐 :=
  fun (𝓐 h𝓐) =>
    Exists.elim h𝓐 (
      fun (A hA) =>
        Exists.elim hA (
          fun (R₁ hR₁) =>
            Exists.elim hR₁ (
              fun (R₂ hR₂) =>
                eq_subst (fun (t) => ( invPO (invPO 𝓐)) = t) (⁅A; R₁; R₂⁆) (𝓐) (Eq.symm (And.left hR₂)) (
                  Iff.mpr (ordered_pair_set_prop (setPO(invPO 𝓐), ≻(invPO 𝓐)) (≽(invPO 𝓐)) (A, R₁) (R₂) ) (
                    And.intro (
                      let u₀ := (And.left (prec_SPO 𝓐 h𝓐))

                      let u₀₀ := bin_on_is_bin setPO(𝓐) (≺(𝓐)) u₀

                      let u₁ : setPO(invPO 𝓐) = setPO(𝓐) := setPO_is_setPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
                      let u₂ := eq_subst (fun (t) => setPO(t) = A) (⁅A; R₁; R₂⁆) (𝓐) (Eq.symm (And.left hR₂)) (
                        setPO_is_setPO A R₁ R₂
                      )
                      let u₃ : ≺(invPO 𝓐) = ≻(𝓐) := lessPO_is_lessPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
                      let u₄ : ≻(invPO 𝓐) = ≺(𝓐) := eq_subst (fun (t) => (t⁻¹) = ≺(𝓐)) (≻(𝓐)) (≺(invPO 𝓐)) (Eq.symm u₃) (
                        inv_prop (≺(𝓐)) (u₀₀)
                      )

                      let u₅ := eq_subst (fun (t) => ≺(t) = R₁) (⁅A; R₁; R₂⁆) (𝓐) (Eq.symm (And.left hR₂)) (
                        lessPO_is_lessPO A R₁ R₂
                      )
                      Iff.mpr (ordered_pair_set_prop (setPO(invPO 𝓐)) (≻(invPO 𝓐)) (A) (R₁)) (
                        And.intro (Eq.trans (u₁) (u₂)) (Eq.trans (u₄) (u₅))
                      )

                    ) (
                      let u₆ : ≼(invPO 𝓐) = ≽(𝓐) := lesseqPO_is_lesseqPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
                      let u₀₀₀ := (And.left (preceq_NSPO 𝓐 h𝓐))
                      let u₀₁ := bin_on_is_bin setPO(𝓐) (≼(𝓐)) u₀₀₀
                      let u₇ : ≽(invPO 𝓐) = ≼(𝓐) := eq_subst (fun (t) => (t⁻¹) = ≼(𝓐)) (≽(𝓐)) (≼(invPO 𝓐)) (Eq.symm u₆) (
                        inv_prop (≼(𝓐)) (u₀₁)
                      )
                      let u₈ := eq_subst (fun (t) => ≼(t) = R₂) (⁅A; R₁; R₂⁆) (𝓐) (Eq.symm (And.left hR₂)) (
                        lesseqPO_is_lesseqPO A R₁ R₂
                      )

                      Eq.trans (u₇) (u₈))
                  )



                )
            )
        )
    )




theorem min_max_inv_al : ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_minimal 𝓐 B x) ↔ (is_maximal (invPO 𝓐) B x)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      Iff.intro
      (
        fun (hmin : (is_minimal 𝓐 B x)) =>
          And.intro (And.left hmin) (
            fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hxy : (x, y) ∈ ≺((invPO 𝓐))) =>

                  And.right hmin y hyB (Iff.mp (inv_PO_less 𝓐 h𝓐 x y) (hxy))
          )
      )
      (
        fun (hmax : (is_maximal (invPO 𝓐) B x)) =>
          And.intro (And.left hmax) (
            fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hxy : (y . (≺(𝓐)) . x)) =>
                  And.right hmax y hyB (Iff.mpr (inv_PO_less 𝓐 h𝓐 x y) hxy)
          )
      )


theorem max_min_inv_al : ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_maximal 𝓐 B x) ↔ (is_minimal (invPO 𝓐) B x)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      Iff.intro
      (
        fun (hmax : (is_maximal 𝓐 B x)) =>
          And.intro (And.left hmax) (
            fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hxy : (y, x) ∈ ≺((invPO 𝓐))) =>
                  And.right hmax y hyB (Iff.mp (inv_PO_less 𝓐 h𝓐 y x) hxy)

          )
      )
      (
        fun (hmax : (is_minimal (invPO 𝓐) B x)) =>
          And.intro (And.left hmax) (
            fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hxy : (x . (≺(𝓐)) . y)) =>
                  And.right hmax y hyB (Iff.mpr (inv_PO_less 𝓐 h𝓐 y x) hxy)

          )

      )
theorem min_max_inv_um :  ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_lowest 𝓐 B x) ↔ (is_greatest (invPO 𝓐) B x)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : ((PartOrd 𝓐))) =>
      Iff.intro
        (
          fun (hmin : (is_lowest 𝓐 B x)) =>
            And.intro (And.left hmin) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  let u := And.right hmin y hyB
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 y x) u


            )
        )
        (
          fun (hmax : (is_greatest (invPO 𝓐) B x)) =>
            And.intro (And.left hmax) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  let u := And.right hmax y hyB
                  Iff.mp (inv_PO_lesseq 𝓐 h𝓐 y x) u
            )

        )
theorem max_min_inv_um :  ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_greatest 𝓐 B x) ↔ (is_lowest (invPO 𝓐) B x)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      Iff.intro
        (
          fun (hmax : (is_greatest 𝓐 B x)) =>
            And.intro (And.left hmax) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  let u := And.right hmax y hyB
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 x y) u


            )
        )
        (
          fun (hmin : (is_lowest (invPO 𝓐) B x)) =>
            And.intro (And.left hmin) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  let u := And.right hmin y hyB
                  Iff.mp (inv_PO_lesseq 𝓐 h𝓐 x y) u
            )

        )
theorem min_max_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (max_set 𝓐 B = min_set (invPO 𝓐) B) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      extensionality (max_set 𝓐 B) (min_set (invPO 𝓐) B) (
        fun (t) =>
          Iff.intro
          (
            fun (ht : t ∈ (max_set 𝓐 B)) =>
              let u := Iff.mp (max_set_is_max_set 𝓐 B t) ht
              let v := Iff.mp (max_min_inv_al 𝓐 B t h𝓐) u
              Iff.mpr (min_set_is_min_set (invPO 𝓐) B t) v
          )
          (
            fun (ht : t ∈ (min_set (invPO 𝓐) B)) =>
              let u := Iff.mp (min_set_is_min_set (invPO 𝓐) B t) ht
              let v := Iff.mpr (max_min_inv_al 𝓐 B t h𝓐) u
              Iff.mpr (max_set_is_max_set 𝓐 B t) v
          )
      )
theorem max_min_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (min_set 𝓐 B = max_set (invPO 𝓐) B) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      extensionality (min_set 𝓐 B) (max_set (invPO 𝓐) B) (
        fun (t) =>
          Iff.intro
          (
            fun (ht : t ∈ (min_set 𝓐 B)) =>
              let u := Iff.mp (min_set_is_min_set 𝓐 B t) ht
              let v := Iff.mp (min_max_inv_al 𝓐 B t h𝓐) u
              Iff.mpr (max_set_is_max_set (invPO 𝓐) B t) v
          )
          (
            fun (ht : t ∈ (max_set (invPO 𝓐) B)) =>
              let u := Iff.mp (max_set_is_max_set (invPO 𝓐) B t) ht
              let v := Iff.mpr (min_max_inv_al 𝓐 B t h𝓐) u
              Iff.mpr (min_set_is_min_set 𝓐 B t) v
          )
      )
















theorem inv_low_upp_bou : ∀ 𝓐 B, (PartOrd 𝓐) → ∀ x, (is_upper_bound 𝓐 B x) ↔ (is_lower_bound (invPO 𝓐) B x) :=
  fun (𝓐 B) =>
    fun (h𝓐 :(PartOrd 𝓐) ) =>
      fun (x) =>
        Iff.intro
        (
          fun (hx : (is_upper_bound 𝓐 B x)) =>
            let u := And.left hx
            let u₁ := setPO_is_setPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
            let u₂ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐)) (setPO(inv_PO 𝓐)) (Eq.symm u₁) (u)
            And.intro (u₂) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  let u₀ := And.right hx y hyB
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 x y) u₀

            )
        )
        (
          fun (hx : (is_lower_bound (invPO 𝓐) B x)) =>
            let u := And.left hx
            let u₁ := setPO_is_setPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
            let u₂ := eq_subst (fun (t) => x ∈ t) (setPO(inv_PO 𝓐)) (setPO(𝓐)) (u₁) (u)
            And.intro (u₂) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  Iff.mp (inv_PO_lesseq 𝓐 h𝓐 x y) (
                    And.right hx y hyB
                  )
            )
        )
theorem inv_upp_low_bou : ∀ 𝓐 B, (PartOrd 𝓐) → ∀ x, (is_lower_bound 𝓐 B x) ↔ (is_upper_bound (invPO 𝓐) B x) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x) =>
        Iff.intro
        (
          fun (hx : (is_lower_bound 𝓐 B x)) =>
            let u := And.left hx
            let u₁ := setPO_is_setPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
            let u₂ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐)) (setPO(inv_PO 𝓐)) (Eq.symm u₁) (u)
            And.intro (u₂) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 y x) (And.right hx y hyB)
            )
        )
        (
          fun (hx : (is_upper_bound (invPO 𝓐) B x)) =>
            let u := And.left hx
            let u₁ := setPO_is_setPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
            let u₂ := eq_subst (fun (t) => x ∈ t) (setPO(inv_PO 𝓐)) (setPO(𝓐)) (u₁) (u)
            And.intro (u₂) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  Iff.mp (inv_PO_lesseq 𝓐 h𝓐 y x) (And.right hx y hyB)
            )
        )

theorem low_bou_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 ▾ B) = ((invPO 𝓐) ▴ B) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      extensionality (𝓐 ▾ B) ((invPO 𝓐) ▴ B) (
        fun (x) =>
          Iff.intro
          (
            fun (hx : (x ∈ (𝓐 ▾ B))) =>
              Iff.mpr (upp_bou_set_is_upp_bou (invPO 𝓐) B x) (
                Iff.mp (inv_upp_low_bou 𝓐 B h𝓐 x) (
                  Iff.mp (low_bou_set_is_low_bou 𝓐 B x) (
                    hx
                  )
                )
              )
          )
          (
            fun (hx : x ∈ ((invPO 𝓐) ▴ B)) =>
              Iff.mpr (low_bou_set_is_low_bou 𝓐 B x) (
                Iff.mpr (inv_upp_low_bou 𝓐 B h𝓐 x) (
                  Iff.mp (upp_bou_set_is_upp_bou (invPO 𝓐) B x) (
                    hx
                  )
                )
              )
          )
      )
theorem upp_bou_set_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 ▴ B) = ((invPO 𝓐) ▾ B) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      extensionality (𝓐 ▴ B) ((invPO 𝓐) ▾ B) (
        fun (x) =>
          Iff.intro
          (
            fun (hx : (x ∈ (𝓐 ▴ B))) =>
              Iff.mpr (low_bou_set_is_low_bou (invPO 𝓐) B x) (
                Iff.mp (inv_low_upp_bou 𝓐 B h𝓐 x) (
                  Iff.mp (upp_bou_set_is_upp_bou 𝓐 B x) (
                    hx
                  )
                )
              )
          )
          (
            fun (hx : x ∈ ((invPO 𝓐) ▾ B)) =>
              Iff.mpr (upp_bou_set_is_upp_bou 𝓐 B x) (
                Iff.mpr (inv_low_upp_bou 𝓐 B h𝓐 x) (
                  Iff.mp (low_bou_set_is_low_bou (invPO 𝓐) B x) (
                    hx
                  )
                )
              )
          )
      )






theorem inv_is_sup_inf : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_supremum 𝓐 B x) ↔ (is_infimum (invPO 𝓐) B x)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x) =>
        Iff.intro
        (
          fun (hsupx : (is_supremum 𝓐 B x)) =>
            let u := And.left hsupx
            let res₁ := upp_bou_set_inv 𝓐 B h𝓐
            let res₂ := eq_subst (fun (t) => x ∈ t) (upper_bounds 𝓐 B) (lower_bounds (inv_PO 𝓐) B) res₁ u
            And.intro (res₂) (

              fun (y) =>
                fun (hy : y ∈ ((inv_PO 𝓐) ▾ B)) =>
                  let v := upp_bou_set_inv 𝓐 B h𝓐
                  let v₂ := eq_subst (fun (t) => y ∈ t) ((inv_PO 𝓐) ▾ B) (𝓐 ▴ B) (Eq.symm v) hy
                  let v₃ := And.right hsupx y v₂
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 y x) v₃

            )
        )
        (
          fun (hinfinvx : (is_infimum (invPO 𝓐) B x)) =>
            let u := And.left hinfinvx
            let res₁ := upp_bou_set_inv 𝓐 B h𝓐
            let res₂ := eq_subst (fun (t) => x ∈ t) (lower_bounds (inv_PO 𝓐) B) (upper_bounds 𝓐 B) (Eq.symm res₁) u
            And.intro (res₂) (
              fun (y) =>
                fun (hy : y ∈ (𝓐 ▴ B)) =>
                  let v := upp_bou_set_inv 𝓐 B h𝓐
                  let v₂ := eq_subst (fun (t) => y ∈ t)  (𝓐 ▴ B) ((inv_PO 𝓐) ▾ B) v hy
                  let v₃ := And.right hinfinvx y v₂
                  Iff.mp (inv_PO_lesseq 𝓐 h𝓐 y x) v₃
            )
        )

theorem inv_is_inf_sup : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_infimum 𝓐 B x) ↔ (is_supremum (invPO 𝓐) B x)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐) ) =>
      fun (x) =>
        Iff.intro
        (
          fun (hinfx : (is_infimum 𝓐 B x)) =>
            let u := And.left hinfx
            let res₁ := low_bou_set_inv 𝓐 B h𝓐
            let res₂ := eq_subst (fun (t) => x ∈ t) (lower_bounds 𝓐 B) (upper_bounds (inv_PO 𝓐) B) res₁ u
            And.intro (res₂) (

              fun (y) =>
                fun (hy : y ∈ ((inv_PO 𝓐) ▴ B)) =>
                  let v := low_bou_set_inv 𝓐 B h𝓐
                  let v₂ := eq_subst (fun (t) => y ∈ t) ((inv_PO 𝓐) ▴ B) (𝓐 ▾ B) (Eq.symm v) hy
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 x y) (

                    And.right hinfx y v₂


                  )
            )
        )
        (
          fun (hsupinvx : (is_supremum (invPO 𝓐) B x)) =>
            let u := And.left hsupinvx
            let res₁ := low_bou_set_inv 𝓐 B h𝓐
            let res₂ := eq_subst (fun (t) => x ∈ t) (upper_bounds (inv_PO 𝓐) B) (lower_bounds 𝓐 B) (Eq.symm res₁) u
            And.intro (res₂) (
              fun (y) =>
                fun (hy : y ∈ (𝓐 ▾ B)) =>
                  let v := low_bou_set_inv 𝓐 B h𝓐
                  let v₂ := eq_subst (fun (t) => y ∈ t)  (𝓐 ▾ B) ((inv_PO 𝓐) ▴ B) v hy
                  Iff.mp (inv_PO_lesseq 𝓐 h𝓐 x y) (
                    And.right hsupinvx y v₂
                  )
            )
        )





theorem max_min_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 GrtExi B) → (((invPO 𝓐) LowExi B) ∧ ((𝓐 Grt B) = (invPO(𝓐)) Low B)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 GrtExi B)) =>
        Exists.elim hexi (
          fun (x) =>
            fun (hx : is_greatest 𝓐 B x) =>
              let u := Iff.mp (max_min_inv_um 𝓐 B x h𝓐) hx
              let v₂ := Exists.intro x u
              And.intro (v₂) (
                Iff.mp (min_po_crit (invPO(𝓐)) B (𝓐 Grt B) (inv_is_PO 𝓐 h𝓐) v₂)
                (
                  Iff.mp ((max_min_inv_um (𝓐) B (𝓐 Grt B) h𝓐)) (max_po_prop 𝓐 B h𝓐 (
                    Exists.intro x hx
                  ))
                )
              )
          )
theorem min_max_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 LowExi B) → (((invPO 𝓐) GrtExi B) ∧ ((𝓐 Low B) = (invPO(𝓐)) Grt B)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 LowExi B)) =>
        Exists.elim hexi (
          fun (x) =>
            fun (hx : is_lowest 𝓐 B x) =>
              let u := Iff.mp (min_max_inv_um 𝓐 B x h𝓐) hx
              let v₂ := Exists.intro x u
              And.intro (v₂) (
                Iff.mp (max_po_crit (invPO(𝓐)) B (𝓐 Low B) (inv_is_PO 𝓐 h𝓐) v₂)
                (
                  Iff.mp ((min_max_inv_um (𝓐) B (𝓐 Low B)) h𝓐 ) (min_po_prop 𝓐 B h𝓐 (
                    Exists.intro x hx
                  ))
                )
              )
          )




noncomputable def subs_part_ord (𝓐 X) := ⁅X; ≺(𝓐) spec X; ≼(𝓐) spec X⁆
syntax term "SubsPO" term : term
macro_rules
| `($𝓐 SubsPO $X) => `(subs_part_ord $𝓐 $X)


theorem sub_is_PO : ∀ 𝓐 B, (B ≠ ∅) → (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (PartOrd (𝓐 SubsPO B)) :=
  fun (𝓐 B) =>
    fun (hBemp : (B ≠ ∅)) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hB𝓐 : (B ⊆ (setPO(𝓐)))) =>
          let A := setPO(𝓐)
          let R₁ := ≺(𝓐)
          let R₂ := ≼(𝓐)
          let hR := triple_po_is_po 𝓐 h𝓐
          po_is_triple_po B (R₁ ∩ (B × B)) (R₂ ∩ (B × B)) (
              And.intro (hBemp) (
              And.intro (
                let u := And.right (And.left (And.right hR))
                And.intro (int_binon_right B R₁ (B × B) (subset_refl (B × B))) (
                  And.intro (irrefl_int_left R₁ (B × B) (And.left u)) (
                    trans_int R₁ (B × B) (And.right u) (
                      fun (x y z) =>
                        fun (hxyz : (x . (B × B) . y) ∧ (y . (B × B) . z)) =>
                          Iff.mpr (cartesian_product_pair_prop B B x z) (
                            let fr := Iff.mp (cartesian_product_pair_prop B B x y) (And.left hxyz)
                            let sr := Iff.mp (cartesian_product_pair_prop B B y z) (And.right hxyz)
                            And.intro (And.left fr) (And.right sr)
                          )
                    )
                  )
                )

              ) (

                extensionality (R₂ ∩ (B × B)) (nonstr B (R₁ ∩ (B × B))) (
                  fun (k) =>
                    Iff.intro
                    (
                      fun (hk : k ∈ R₂ ∩ (B × B)) =>
                        let u := Iff.mp (intersect_2sets_prop R₂ (B × B) k) hk
                        let v := And.right (And.right hR)
                        let v₂ := eq_subst (fun (m) => k ∈ m) (R₂) (nonstr A R₁) v (And.left u)
                        let v₃ := Iff.mp (union2sets_prop (R₁) (id_ A) k) v₂
                        Or.elim v₃ (
                          fun (hk₂ : k ∈ R₁) =>
                            Iff.mpr (union2sets_prop (R₁ ∩ (B × B)) (id_ B) k) (
                              Or.inl (Iff.mpr (intersect_2sets_prop R₁ (B × B) k) (And.intro (hk₂) (And.right u)))
                            )
                        )
                        (
                          fun (hk₂ : k ∈ (id_ A)) =>
                            Iff.mpr (union2sets_prop (R₁ ∩ (B × B)) (id_ B) k) (
                              Or.inr (
                                let a := Iff.mp (cartesian_product_is_cartesian B B k) (And.right u)
                                Exists.elim a (
                                  fun (x) =>
                                    fun (hx) =>
                                      Exists.elim (And.right hx) (
                                        fun (y) =>
                                          fun (hy : y ∈ B ∧ k = (x, y)) =>
                                            let prop₁ := eq_subst (fun (m) => m ∈ (id_ A)) k (x, y) (And.right hy) (hk₂)
                                            eq_subst (fun (m) => m ∈ (id_ B)) (x, y) k (Eq.symm (And.right hy)) (
                                              let u := id_prop A x y prop₁
                                              eq_subst (fun (n) => (x, n) ∈ (id_ B)) x y (And.left (And.left u)) (
                                                prop_then_id B x (And.left hx)
                                              )
                                            )
                                      )
                                )
                              )
                            )
                        )

                    )
                    (
                      fun (hk : k ∈ (nonstr B (R₁ ∩ (B × B)))) =>
                        let u := Iff.mp (union2sets_prop (R₁ ∩ (B × B)) (id_ B) k) hk
                        Or.elim u
                        (
                          fun (hk₂ : k ∈ (R₁ ∩ (B × B))) =>
                            let u := Iff.mp (intersect_2sets_prop R₁ (B × B) k) hk₂
                            Iff.mpr (intersect_2sets_prop (R₂) (B × B) k) (
                              And.intro (
                                Exists.elim (Iff.mp (cartesian_product_is_cartesian B B k) (And.right u)) (
                                  fun (x) =>
                                    fun (hx) =>
                                      Exists.elim (And.right hx) (
                                        fun (y) =>
                                          fun (hy : y ∈ B ∧ k = (x, y)) =>
                                            eq_subst (fun (m) => m ∈ R₂) (x, y) k (Eq.symm (And.right hy)) (
                                              part_ord_pair_prop_R₁R₂ 𝓐 h𝓐 x y (
                                                eq_subst (fun (n) => n ∈ R₁) k (x, y) (And.right hy) (And.left u)
                                              )
                                            )
                                      )
                                )
                              ) (And.right u)
                            )
                        )
                        (
                          fun (hk₂ : k ∈ (id_ B)) =>
                            let u := id_is_binon B k hk₂
                            Exists.elim (Iff.mp (cartesian_product_is_cartesian B B k) u) (
                              fun (x) =>
                                fun (hx) =>
                                  Exists.elim (And.right hx) (
                                    fun (y) =>
                                      fun (hy : y ∈ B ∧ k = (x, y)) =>
                                        let u := eq_subst (fun (m) => m ∈ (id_ B)) k (x, y) (And.right hy) hk₂
                                        eq_subst (fun (m) => m ∈ (R₂ ∩ (B × B))) (x, y) k (Eq.symm (And.right hy)) (
                                          Iff.mpr (intersect_2sets_prop (R₂) (B × B) (x, y)) (
                                            And.intro (
                                              part_ord_pair_prop_eqR₂ 𝓐 h𝓐 x (hB𝓐 x (And.left hx)) y (hB𝓐 y (And.left hy)) (
                                                And.left (And.left (id_prop B x y u))
                                              )
                                            ) (Iff.mpr (cartesian_product_pair_prop B B x y) (
                                              And.intro (And.left hx) (And.left hy)
                                            ))
                                          )
                                        )
                                  )

                            )

                        )
                    )
                )
              )
            )
          )

noncomputable def setintpo (𝓐 𝓑) := setPO(𝓐) ∩ setPO(𝓑)
noncomputable def le_int (𝓐 𝓑) := (≺(𝓐) spec (setintpo 𝓐 𝓑)) ∩ (≺(𝓑) spec (setintpo 𝓐 𝓑))
noncomputable def leq_int (𝓐 𝓑) := (≼(𝓐) spec (setintpo 𝓐 𝓑)) ∩ (≼(𝓑) spec (setintpo 𝓐 𝓑))
noncomputable def inter_part_ord (𝓐 𝓑) := (setintpo 𝓐 𝓑) StrIntro (le_int 𝓐 𝓑)
syntax term "InterPO" term : term
macro_rules
| `($𝓐 InterPO $𝓑) => `(inter_part_ord $𝓐 $𝓑)




theorem inter_is_PO_PO :∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (setPO(𝓐) ∩ setPO(𝓑) ≠ ∅) → (PartOrd (𝓐 InterPO 𝓑)) :=
    fun (𝓐 𝓑) =>
      fun (h𝓐 : (PartOrd 𝓐) ) =>
        fun (h𝓑 : (PartOrd 𝓑)) =>
          fun (hnemp) =>
            let A := setPO(𝓐)
            let B := setPO(𝓑)
            let AB := A ∩ B
            let AB₂ := (AB × AB)
            let AR₁ := ≺(𝓐)
            let AspR₁ := (≺(𝓐) spec (setintpo 𝓐 𝓑))
            let BR₁ := ≺(𝓑)
            let BspR₁ := (≺(𝓑) spec (setintpo 𝓐 𝓑))
            let R₁ := AspR₁ ∩ BspR₁
            po_from_str_is_po AB R₁ hnemp (
              And.intro (subset_trans R₁ AspR₁ AB₂ (And.left (interset2sets_subset_prop AspR₁ BspR₁)) (
                And.right (interset2sets_subset_prop AR₁ AB₂)
              )) (And.intro (
                fun (x hx) =>
                  let u₁ := And.left (Iff.mp (intersect_2sets_prop AspR₁ BspR₁ (x, x)) hx)
                  let u₂ := And.left (Iff.mp (intersect_2sets_prop AR₁ AB₂ (x, x)) u₁)
                  irrefl_R₁ 𝓐 h𝓐 x (u₂)
              ) (
                fun (x y z hxyz) =>
                  let u₁ := Iff.mp (intersect_2sets_prop AspR₁ BspR₁ (x, y) ) (And.left hxyz)
                  let u₂ := Iff.mp (intersect_2sets_prop AspR₁ BspR₁ (y, z) ) (And.right hxyz)
                  let u₃ := Iff.mp (intersect_2sets_prop AR₁ AB₂ (x, y)) (And.left u₁)
                  let u₄ := Iff.mp (intersect_2sets_prop BR₁ AB₂ (x, y)) (And.right u₁)
                  let u₅ := Iff.mp (intersect_2sets_prop AR₁ AB₂ (y, z)) (And.left u₂)
                  let u₆ := Iff.mp (intersect_2sets_prop BR₁ AB₂ (y, z)) (And.right u₂)
                  let u₇ := Iff.mp (cartesian_product_pair_prop AB AB x y) (And.right u₃)
                  let u₈ := Iff.mp (cartesian_product_pair_prop AB AB y z) (And.right u₅)
                  let u₉ := Iff.mpr (cartesian_product_pair_prop AB AB x z) (
                    And.intro (And.left u₇) (And.right u₈)
                  )

                  Iff.mpr (intersect_2sets_prop AspR₁ BspR₁ (x, z)) (
                    And.intro (Iff.mpr (intersect_2sets_prop AR₁ AB₂ (x, z)) (And.intro (trans_R₁ 𝓐 h𝓐 x y z (And.left u₃) (And.left u₅)) (u₉))) (
                      Iff.mpr (intersect_2sets_prop BR₁ AB₂ (x, z)) (And.intro (trans_R₁ 𝓑 h𝓑 x y z (And.left u₄) (And.left u₆)) (u₉))
                    )
                  )

              ))
            )




theorem inter_leq : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (setPO(𝓐) ∩ setPO(𝓑) ≠ ∅) →
∀ x y ∈ setPO(𝓐 InterPO 𝓑); (x . ≼(𝓐 InterPO 𝓑) . y) ↔ (x . (leq_int 𝓐 𝓑) . y) :=
  fun (𝓐 𝓑) =>
    fun (h𝓐 h𝓑) =>
      fun (hnemp) =>
        fun (x hx y hy) =>
          let 𝓒 := 𝓐 InterPO 𝓑
          let h𝓒 := inter_is_PO_PO 𝓐 𝓑 h𝓐 h𝓑 hnemp
          let A := setPO(𝓐)
          let B := setPO(𝓑)
          let AB := A ∩ B
          let AB₂ := (AB × AB)
          let AR₁ := ≺(𝓐)
          let AspR₁ := (≺(𝓐) spec AB)
          let BR₁ := ≺(𝓑)
          let BspR₁ := (≺(𝓑) spec AB)
          let AR₂ := ≼(𝓐)
          let BR₂ := ≼(𝓑)
          let AspR₂ := (AR₂ spec AB)
          let BspR₂ := (BR₂ spec AB)
          let R₁ := AspR₁ ∩ BspR₁
          let R₂ := nonstr AB R₁
          let u₀ := lesseqPO_is_lesseqPO AB R₁ R₂
          let u₀₀ := lessPO_is_lessPO AB R₁ R₂
          let u₁ := setPO_is_setPO AB R₁ R₂
          let u₂ := eq_subst (fun (t) => x ∈ t) (setPO(𝓒)) (AB) (u₁) hx
          let u₃ := eq_subst (fun (t) => y ∈ t) (setPO(𝓒)) (AB) (u₁) hy
          let uxy := Iff.mpr (cartesian_product_pair_prop AB AB x y) (And.intro (u₂) (u₃))
          let uxin := Iff.mp (intersect_2sets_prop A B x) u₂
          let uyin := Iff.mp (intersect_2sets_prop A B y) u₃

          Iff.intro
          (
            fun (hxy) =>
              Or.elim (Iff.mp (And.right (part_ord_pair_prop 𝓒 h𝓒 x hx y hy)) hxy)
              (
                fun (hlxy) =>
                  let u₅ := eq_subst (fun (t) => (x . t . y)) (≺(𝓒)) (R₁) (u₀₀) (hlxy)
                  let u₆ := Iff.mp (intersect_2sets_prop AspR₁ BspR₁ (x, y) ) (u₅)
                  let u₇ := Iff.mp (intersect_2sets_prop AR₁ AB₂ (x, y)) (And.left u₆)
                  let u₈ := Iff.mp (intersect_2sets_prop BR₁ AB₂ (x, y)) (And.right u₆)
                  let u₉ := part_ord_pair_prop_R₁R₂ 𝓐 h𝓐 x y (And.left u₇)
                  let u₁₀ := part_ord_pair_prop_R₁R₂ 𝓑 h𝓑 x y (And.left u₈)

                  Iff.mpr (intersect_2sets_prop AspR₂ BspR₂ (x, y)) (
                    And.intro (Iff.mpr (intersect_2sets_prop AR₂ AB₂ (x, y)) (And.intro (u₉) (And.right u₇))) (
                      Iff.mpr (intersect_2sets_prop BR₂ AB₂ (x, y)) (And.intro (u₁₀) (And.right u₇))
                    )
                  )
              )
              (
                fun (hexy) =>
                  let u₁₁ := eq_subst (fun (t) => (x . AR₂ . t)) x y (hexy) (refl_R₂ 𝓐 h𝓐 x (And.left uxin))
                  let u₁₂ := eq_subst (fun (t) => (x . BR₂ . t)) x y (hexy) (refl_R₂ 𝓑 h𝓑 x (And.right uxin))
                  Iff.mpr (intersect_2sets_prop AspR₂ BspR₂ (x, y)) (
                    And.intro (Iff.mpr (intersect_2sets_prop AR₂ AB₂ (x, y)) (And.intro (u₁₁) (uxy))) (
                      Iff.mpr (intersect_2sets_prop BR₂ AB₂ (x, y)) (And.intro (u₁₂) (uxy))
                    )
                  )
              )
          )
          (
            fun (hxy) =>
              Or.elim (Classical.em (x = y))
              (
                fun (hexy) =>
                  eq_subst (fun (t) => (x . ≼(𝓒) . t)) x y (hexy) (refl_R₂ 𝓒 h𝓒 x hx)
              )
              (
                fun (hnexy) =>
                  let u₅ := Iff.mp (intersect_2sets_prop AspR₂ BspR₂ (x, y)) (hxy)
                  let u₆ := Iff.mp (intersect_2sets_prop AR₂ AB₂ (x, y)) (And.left u₅)
                  let u₇ := Iff.mp (intersect_2sets_prop BR₂ AB₂ (x, y)) (And.right u₅)
                  let u₈ := part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 x y (And.intro (And.left u₆) (hnexy))
                  let u₉ := part_ord_pair_prop_neqR₂R₁ 𝓑 h𝓑 x y (And.intro (And.left u₇) (hnexy))
                  part_ord_pair_prop_R₁R₂ 𝓒 h𝓒 x y (
                    eq_subst (fun (t) => (x . t . y)) (R₁) (≺(𝓒)) (Eq.symm u₀₀) (
                      Iff.mpr (intersect_2sets_prop AspR₁ BspR₁ (x, y)) (
                        And.intro (Iff.mpr (intersect_2sets_prop AR₁ AB₂ (x, y)) (And.intro (u₈) (uxy))) (
                          Iff.mpr (intersect_2sets_prop BR₁ AB₂ (x, y)) (And.intro (u₉) (uxy))
                        )
                      )
                    )
                  )
              )
          )




noncomputable def setpo_disj2 (𝓐 𝓑) := setPO(𝓐) ⊔ setPO(𝓑)
def disj_pred2_R₁ (𝓐 𝓑) := fun (x : Set) => fun (y : Set) => ((π₂ x) = l2 ∧ (π₂ y) = l2 ∧ ((π₁ x) . ≺(𝓐) . (π₁ y))) ∨
  ((π₂ x) = r2 ∧ (π₂ y) = r2 ∧ ((π₁ x) . ≺(𝓑) . (π₁ y))) ∨
  ((π₁ x) ∈ setPO(𝓐) ∧ (π₁ y) ∈ setPO(𝓑) ∧ (π₂ x) = l2 ∧ (π₂ y) = r2)
def disj_pred2_R₂ (𝓐 𝓑) := fun (x : Set) => fun (y : Set) => ((π₂ x) = l2 ∧ (π₂ y) = l2 ∧ ((π₁ x) . ≼(𝓐) . (π₁ y))) ∨
  ((π₂ x) = r2 ∧ (π₂ y) = r2 ∧ ((π₁ x) . ≼(𝓑) . (π₁ y))) ∨
  ((π₁ x) ∈ setPO(𝓐) ∧ (π₁ y) ∈ setPO(𝓑) ∧ (π₂ x) = l2 ∧ (π₂ y) = r2)

noncomputable def le_disj2 (𝓐 𝓑) := {(x, y) ∈ (setpo_disj2 𝓐 𝓑) × (setpo_disj2 𝓐 𝓑) | disj_pred2_R₁ 𝓐 𝓑 x y}

noncomputable def po_disj2 (𝓐 𝓑) := ((setpo_disj2 𝓐 𝓑) StrIntro (le_disj2 𝓐 𝓑))
syntax term "P⨁O" term : term
macro_rules
| `($𝓐 P⨁O $𝓑) => `(po_disj2 $𝓐 $𝓑)




theorem sum_is_PO : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (PartOrd (𝓐 P⨁O 𝓑)) :=
  fun (𝓐 𝓑 h𝓐 h𝓑) =>
    let A := setpo_disj2 𝓐 𝓑
    let R₁ := le_disj2 𝓐 𝓑
    let u₁ := po_emp 𝓐 h𝓐
    let prop₁ := bin_spec_is_spec (disj_pred2_R₁ 𝓐 𝓑) (setpo_disj2 𝓐 𝓑) (setpo_disj2 𝓐 𝓑)
    Exists.elim (Iff.mp (set_non_empty_iff_non_empty (setPO(𝓐))) u₁) (
      fun (x hx) =>
        po_from_str_is_po A R₁ (Iff.mpr (set_non_empty_iff_non_empty (setpo_disj2 𝓐 𝓑)) (
          Exists.intro (x, ∅) (disj_in_left setPO(𝓐) setPO(𝓑) x hx)
        )) (
          And.intro (bin_spec_is_binAB (disj_pred2_R₁ 𝓐 𝓑) (setpo_disj2 𝓐 𝓑) (setpo_disj2 𝓐 𝓑)) (
            And.intro (
              fun (x hx) =>
                let u₁ := Iff.mp (prop₁ x x) hx

                Or.elim (And.right u₁)
                (
                  fun (hpr₁) =>
                    irrefl_R₁ 𝓐 h𝓐 (π₁ x) (And.right (And.right (hpr₁)))
                )
                (
                  fun (hpr₂) =>
                    Or.elim (hpr₂)
                    (
                      fun (hpr₃) =>
                        irrefl_R₁ 𝓑 h𝓑 (π₁ x) (And.right (And.right hpr₃))
                    )
                    (
                      fun (hpr₄) =>
                        let u₂ := Eq.trans (Eq.symm (And.left (And.right (And.right (hpr₄))))) (And.right (And.right (And.right hpr₄)))
                        empty_set_is_empty l2 (
                          eq_subst (fun (t) => l2 ∈ t) r2 l2 (Eq.symm u₂) (elem_in_singl l2)
                        )
                    )
                )
            ) (
              fun (x y z hxyz) =>
                let u₁ := Iff.mp (prop₁ x y) (And.left hxyz)
                let u₂ := Iff.mp (prop₁ y z) (And.right hxyz)
                let hx := And.left (And.left u₁)
                let hz := And.right (And.left u₂)

                Or.elim (And.right u₁)
                (
                  fun (hpr₁) =>
                    let xl2 := (And.left hpr₁)
                    let x𝓐 := And.right (And.right hpr₁)
                    let xin𝓐 := par_ord_pair_prop_R₁_A 𝓐 h𝓐 (π₁ x) (π₁ y) x𝓐
                    let yl2 := (And.left (And.right hpr₁))

                    Or.elim (And.right u₂)
                    (
                      fun (hpr₅) =>
                        let zl2 := (And.left (And.right hpr₅))

                        let u₁ := trans_R₁ 𝓐 h𝓐 (π₁ x) (π₁ y) (π₁ z) (And.right (And.right hpr₁)) (And.right (And.right hpr₅))
                        Iff.mpr (prop₁ x z) (
                          And.intro (And.intro (hx) (hz)) (Or.inl (
                            And.intro (xl2) (And.intro zl2 (u₁))
                          ))
                        )

                    )
                    (
                      fun (hpr₆) =>
                        (Or.elim hpr₆)
                        (
                          fun (hpr₇) =>
                            let yr2 := And.left hpr₇
                            let u₂ := Eq.trans (Eq.symm yl2) (yr2)
                            False.elim (
                              empty_set_is_empty l2 (
                                eq_subst (fun (t) => l2 ∈ t) (r2) (l2) (Eq.symm u₂) (elem_in_singl l2)
                              )
                            )
                        )
                        (
                          fun (hpr₈) =>
                            let zr2 := (And.right hpr₈)
                            Iff.mpr (prop₁ x z) (
                              And.intro (And.intro (hx) (hz)) (Or.inr (Or.inr (
                                And.intro (And.left xin𝓐) (And.intro (And.left zr2) (And.intro (xl2) (And.right (And.right zr2))))
                              )))
                            )
                        )
                    )
                )
                (
                  fun (hpr₂) =>
                    Or.elim (hpr₂)
                    (
                      fun (hpr₃) =>
                        let xr2 := (And.left hpr₃)
                        let yr2 := (And.left (And.right hpr₃))


                        Or.elim (And.right u₂)
                        (
                          fun (hpr₅) =>

                            let yl2 := And.left hpr₅
                            let l2r2 := Eq.trans (Eq.symm yr2) (yl2)

                            False.elim (
                              empty_set_is_empty l2 (
                                eq_subst (fun (t) => l2 ∈ t) (r2) (l2) (l2r2) (elem_in_singl l2)
                              )
                            )
                        )
                        (
                          fun (hpr₆) =>
                            Or.elim (hpr₆)
                            (
                              fun (hpr₇) =>
                                let zr2 := (And.left (And.right hpr₇))
                                let utr := trans_R₁ 𝓑 h𝓑 (π₁ x) (π₁ y) (π₁ z) (And.right (And.right hpr₃)) (And.right (And.right hpr₇))
                                Iff.mpr (prop₁ x z) (
                                And.intro (And.intro (hx) (hz)) (Or.inr (Or.inl (
                                  And.intro (xr2) (And.intro zr2 (utr))
                                  )))
                                )

                            )
                            (
                              fun (hpr₈) =>
                                let yl2 := And.left (And.right (And.right hpr₈))
                                let l2r2 := Eq.trans (Eq.symm yr2) (yl2)
                                False.elim (
                                  empty_set_is_empty l2 (
                                    eq_subst (fun (t) => l2 ∈ t) (r2) (l2) (l2r2) (elem_in_singl l2)
                                )
                              )
                            )
                        )
                    )
                    (
                      fun (hpr₄) =>
                        let xl2 := And.left hpr₄
                        let xl₂ :=And.left (And.right (And.right hpr₄))
                        let yr2 := And.right (And.right (And.right hpr₄))
                        Or.elim (And.right u₂)
                        (

                          fun (hpr₅) =>
                            let yl2 := (And.left hpr₅)
                            let u₂ := Eq.trans (Eq.symm yr2) yl2


                            False.elim (
                                  empty_set_is_empty l2 (
                                    eq_subst (fun (t) => l2 ∈ t) (r2) (l2) (u₂) (elem_in_singl l2)
                                )
                              )

                        )
                        (
                          fun (hpr₆) =>
                            (Or.elim hpr₆)
                            (
                              fun (hpr₇) =>
                                let zr₂ := And.left (And.right hpr₇)
                                let z𝓑 := par_ord_pair_prop_R₁_A 𝓑 h𝓑 (π₁ y) (π₁ z) (And.right (And.right hpr₇))
                                Iff.mpr (prop₁ x z) (
                                And.intro (And.intro (hx) (hz)) (
                                  Or.inr (Or.inr (
                                    And.intro (xl2) (And.intro (And.right z𝓑) (And.intro (xl₂) (zr₂)))
                                  ))
                                ) )
                            )
                            (
                              fun (hpr₈) =>
                                let u₂ := Eq.trans (Eq.symm (And.left (And.right (And.right hpr₈)))) (yr2)
                                False.elim (
                                  empty_set_is_empty l2 (
                                    eq_subst (fun (t) => l2 ∈ t) (r2) (l2) (Eq.symm u₂) (elem_in_singl l2)
                                )
                              )
                            )
                        )
                    )
                )
            )
          )
        )
    )


theorem sum_PO_less : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (∀ x y ∈ setPO(𝓐 P⨁O 𝓑); ((x . ≺(𝓐 P⨁O 𝓑) . y) ↔ (disj_pred2_R₁ 𝓐 𝓑 x y))) :=
  fun (𝓐 𝓑 _ _ x hx y hy) =>
    let P := disj_pred2_R₁ 𝓐 𝓑
    let A₁ := (setPO(𝓐) ⊔ setPO(𝓑))
    let M := setPO(𝓐 P⨁O 𝓑)
    let R₁ := le_disj2 𝓐 𝓑
    let R₂ := (nonstr (setPO(𝓐) ⊔ setPO(𝓑)) R₁)
    let A := (setpo_disj2 𝓐 𝓑)
    let u₁ := bin_spec_is_spec P A A
    let u₀ := lessPO_is_lessPO A₁ R₁ R₂
    Iff.intro
    (
      fun (hxy) =>
        let u₂ := eq_subst (fun (t) => (x . t . y)) (≺(𝓐 P⨁O 𝓑)) R₁ (u₀) (hxy)
        And.right (
          Iff.mp (u₁ x y) (u₂)
        )
    )
    (
      fun (hxy) =>
        eq_subst (fun (t) => (x . t . y)) R₁ (≺(𝓐 P⨁O 𝓑)) (Eq.symm u₀) (
          Iff.mpr (u₁ x y) (
            let u₀ := setPO_is_setPO A₁ R₁ R₂
            And.intro (And.intro (eq_subst (fun (t) => x ∈ t) (M) A (u₀) hx) (eq_subst (fun (t) => y ∈ t) (M) A (u₀) hy)) (hxy)
          )
        )
    )

theorem sum_PO_lesseq : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (∀ x y ∈ setPO(𝓐 P⨁O 𝓑); ((x . ≼(𝓐 P⨁O 𝓑) . y) ↔ (disj_pred2_R₂ 𝓐 𝓑 x y))) :=
  fun (𝓐 𝓑 h𝓐 h𝓑 x hx y hy) =>
    let S := 𝓐 P⨁O 𝓑
    let U₀ := (sum_is_PO 𝓐 𝓑 h𝓐 h𝓑)
    let A := (setPO(𝓐) ⊔ setPO(𝓑))
    let R₁ := le_disj2 𝓐 𝓑
    let R₂ := (nonstr (setPO(𝓐) ⊔ setPO(𝓑)) R₁)
    Iff.intro

    (
      fun (hxy) =>
        let setA := setPO(𝓐 P⨁O 𝓑)


        let u₁ := Iff.mp (And.right (part_ord_pair_prop (𝓐 P⨁O 𝓑) U₀ x hx y hy)) hxy
        let u₂ := par_ord_pair_prop_R₂_A (𝓐 P⨁O 𝓑) (U₀) x y hxy
        let u₃ : setA = A := setPO_is_setPO A R₁ R₂
        let u₄ := eq_subst (fun (t) => x ∈ t) setA A (u₃) (And.left u₂)
        let u₆₀ := disj2_xAB_in setPO(𝓐) setPO(𝓑) x u₄


        Or.elim (u₁)
        (
          fun (hxly) =>
            let u₇ := Iff.mp (sum_PO_less 𝓐 𝓑 h𝓐 h𝓑 x (And.left u₂) y (And.right u₂)) hxly
            Or.elim u₇
            (
              fun (hxyA) =>
                Or.inl (
                  And.intro (And.left hxyA) (
                    And.intro (And.left (And.right hxyA)) (
                      part_ord_pair_prop_R₁R₂ 𝓐 h𝓐 (π₁ x) (π₁ y) (And.right (And.right hxyA)))
                  )
                )
            )
            (
              fun (hxyO) =>
                Or.elim hxyO
                (
                  fun (hxyB) =>
                    Or.inr (
                      Or.inl (
                        And.intro (And.left hxyB) (
                          And.intro (And.left (And.right hxyB)) (
                            part_ord_pair_prop_R₁R₂ 𝓑 h𝓑 (π₁ x) (π₁ y) (And.right (And.right hxyB))))
                      )
                    )
                )
                (
                  fun (hxyD) =>
                    Or.inr (
                      Or.inr (
                        And.intro (And.left hxyD) (And.right hxyD)
                      )
                    )
                )
            )
        )
        (
          fun (hxey) =>
            Or.elim u₆₀
            (
              fun (hxA) =>
                Or.inl (
                  let u₈ := And.right hxA
                  let u₉ := eq_subst (fun (t) => (π₂ t) = l2) (x) (y) (hxey) (u₈)
                  And.intro (u₈) (And.intro u₉ (
                    eq_subst (fun (t) => ((π₁ x) . ≼(𝓐) . (π₁ t))) x y (hxey) (
                      refl_R₂ 𝓐 h𝓐 (π₁ x) (And.left hxA)
                    )
                  ))
                )
            )
            (
              fun (hxB) =>
                Or.inr (
                  Or.inl (
                    let u₈ := And.right hxB
                    let u₉ := eq_subst (fun (t) => (π₂ t) = r2) (x) (y) (hxey) (u₈)
                    And.intro (u₈) (And.intro u₉ (
                      eq_subst (fun (t) => ((π₁ x) . ≼(𝓑) . (π₁ t))) x y (hxey) (
                        refl_R₂ 𝓑 h𝓑 (π₁ x) (And.left hxB)
                      )
                    ))
                  )
                )
            )
        )

    )
    (
      fun (hxy) =>

        Or.elim hxy
        (
          fun (hxyA) =>
            let u₀ := par_ord_pair_prop_R₂_A 𝓐 h𝓐 (π₁ x) (π₁ y) (And.right (And.right hxyA))
            let u₁ := Iff.mp (And.right (part_ord_pair_prop 𝓐 h𝓐 (π₁ x) (And.left u₀) (π₁ y) (And.right u₀))) (
              And.right (And.right hxyA)
            )
            Or.elim u₁
            (
              fun (hxlyA) =>

                let u₂ := Iff.mpr (sum_PO_less 𝓐 𝓑 h𝓐 h𝓑 x (hx) y (hy)) (
                  Or.inl (
                    And.intro (And.left hxyA) (And.intro (And.left (And.right hxyA)) (hxlyA))
                  )
                )
                part_ord_pair_prop_R₁R₂ (S) U₀ x y u₂
            )
            (
              fun (hxryA) =>
                let u₂ := And.left hxyA
                let u₃ := And.left (And.right hxyA)
                let u₄ := Eq.trans (u₂) (Eq.symm u₃)
                let u₄₀ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 P⨁O 𝓑)) ((setPO(𝓐) ⊔ setPO(𝓑))) (
                  setPO_is_setPO A R₁ R₂
                ) hx
                let u₄₅ := Iff.mpr (spec_is_spec (fun (t) => (π₂ t) = l2) (setPO(𝓐) ⊔ setPO(𝓑)) x) (And.intro (u₄₀) (And.left hxyA))
                let u₄₆ := eq_subst (fun (t) => x ∈ t) (DUL (setPO(𝓐) ⊔ setPO(𝓑))) (setPO(𝓐) × {l2}) (dul_A setPO(𝓐) setPO(𝓑)) (u₄₅)

                let u₅₀ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 P⨁O 𝓑)) ((setPO(𝓐) ⊔ setPO(𝓑))) (
                  setPO_is_setPO A R₁ R₂
                ) hy
                let u₅₅ := Iff.mpr (spec_is_spec (fun (t) => (π₂ t) = l2) (setPO(𝓐) ⊔ setPO(𝓑)) y) (And.intro (u₅₀) (u₃))
                let u₅₆ := eq_subst (fun (t) => y ∈ t) (DUL (setPO(𝓐) ⊔ setPO(𝓑))) (setPO(𝓐) × {l2}) (dul_A setPO(𝓐) setPO(𝓑)) (u₅₅)


                let u₆ := equal_fst_snd setPO(𝓐) {l2} x y (u₄₆) (u₅₆) (hxryA) (u₄)
                eq_subst (fun (t) => (x . ≼(𝓐 P⨁O 𝓑) . t)) x y (u₆) (refl_R₂ (𝓐 P⨁O 𝓑) (U₀) x (hx))
            )
        )
        (
          fun (hxyO) =>
            Or.elim hxyO
            (
              fun (hxyB) =>
                let u₀ := par_ord_pair_prop_R₂_A 𝓑 h𝓑 (π₁ x) (π₁ y) (And.right (And.right hxyB))
                let u₁ := Iff.mp (And.right (part_ord_pair_prop 𝓑 h𝓑 (π₁ x) (And.left u₀) (π₁ y) (And.right u₀))) (
                  And.right (And.right hxyB)
                )
                Or.elim u₁
                (
                  fun (hxlyB) =>

                    let u₂ := Iff.mpr (sum_PO_less 𝓐 𝓑 h𝓐 h𝓑 x (hx) y (hy)) (
                      Or.inr (
                        Or.inl (
                          And.intro (And.left hxyB) (And.intro (And.left (And.right hxyB)) (hxlyB))
                        )
                      )
                    )
                    part_ord_pair_prop_R₁R₂ (S) U₀ x y u₂
                )
                (
                  fun (hxryB) =>
                    let u₂ := And.left hxyB
                    let u₃ := And.left (And.right hxyB)
                    let u₄ := Eq.trans (u₂) (Eq.symm u₃)
                    let u₄₀ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 P⨁O 𝓑)) ((setPO(𝓐) ⊔ setPO(𝓑))) (
                      setPO_is_setPO A R₁ R₂
                    ) hx
                    let u₄₅ := Iff.mpr (spec_is_spec (fun (t) => (π₂ t) = r2) (setPO(𝓐) ⊔ setPO(𝓑)) x) (And.intro (u₄₀) (And.left hxyB))
                    let u₄₆ := eq_subst (fun (t) => x ∈ t) (DUR (setPO(𝓐) ⊔ setPO(𝓑))) (setPO(𝓑) × {r2}) (dur_B setPO(𝓐) setPO(𝓑)) (u₄₅)

                    let u₅₀ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 P⨁O 𝓑)) ((setPO(𝓐) ⊔ setPO(𝓑))) (
                      setPO_is_setPO A R₁ R₂
                    ) hy
                    let u₅₅ := Iff.mpr (spec_is_spec (fun (t) => (π₂ t) = r2) (setPO(𝓐) ⊔ setPO(𝓑)) y) (And.intro (u₅₀) (u₃))
                    let u₅₆ := eq_subst (fun (t) => y ∈ t) (DUR (setPO(𝓐) ⊔ setPO(𝓑))) (setPO(𝓑) × {r2}) (dur_B setPO(𝓐) setPO(𝓑)) (u₅₅)


                    let u₆ := equal_fst_snd setPO(𝓑) {r2} x y (u₄₆) (u₅₆) (hxryB) (u₄)
                    eq_subst (fun (t) => (x . ≼(𝓐 P⨁O 𝓑) . t)) x y (u₆) (refl_R₂ (𝓐 P⨁O 𝓑) (U₀) x (hx))
                  )
                )
            (
              fun (hxyD) =>
                let u₁ := Iff.mpr (sum_PO_less 𝓐 𝓑 h𝓐 h𝓑 x hx y hy) (
                  Or.inr (
                    Or.inr (
                      hxyD
                    )
                  )
                )
                part_ord_pair_prop_R₁R₂ (𝓐 P⨁O 𝓑) U₀ x y (u₁)
            )
        )
    )




noncomputable def po_set_cart (𝓐 𝓑) := setPO(𝓐) × setPO(𝓑)

def po_set_prop (𝓐 𝓑) := fun (s) => ∃ x₁ ∈ setPO(𝓐); ∃ y₁ ∈ setPO(𝓑); ∃ x₂ ∈ setPO(𝓐); ∃ y₂ ∈ setPO(𝓑);
(s = ((x₁, y₁), (x₂, y₂))) ∧ (x₁ . ≼(𝓐) . x₂) ∧ (y₁ . ≼(𝓑) . y₂)

noncomputable def leq_cart (𝓐 𝓑) := {s ∈ (po_set_cart 𝓐 𝓑) × (po_set_cart 𝓐 𝓑) | po_set_prop 𝓐 𝓑 s}

noncomputable def le_cart (𝓐 𝓑) := str (setPO(𝓐) × setPO(𝓑)) (leq_cart 𝓐 𝓑)

noncomputable def cartesian2_coordinate_part_ord (𝓐 𝓑) := ⁅setPO(𝓐) × setPO(𝓑); le_cart 𝓐 𝓑; leq_cart 𝓐 𝓑⁆
syntax term "Cart2CordPO" term : term
macro_rules
| `($𝓐 Cart2CordPO $𝓑) => `(cartesian2_coordinate_part_ord $𝓐 $𝓑)


theorem poset_cart_prop₁ : ∀ 𝓐 𝓑, ∀ s ∈ po_set_cart 𝓐 𝓑; (π₁ s) ∈ (setPO(𝓐)) :=
  fun (𝓐 𝓑) =>
    fun (s) =>
      fun (hs : s ∈ po_set_cart 𝓐 𝓑) =>
        fst_coor_set (setPO(𝓐)) (setPO(𝓑)) s hs


theorem poset_cart_prop₂ : ∀ 𝓐 𝓑, ∀ s ∈ po_set_cart 𝓐 𝓑; (π₂ s) ∈ (setPO(𝓑)) :=
  fun (𝓐 𝓑) =>
    fun (s) =>
      fun (hs : s ∈ po_set_cart 𝓐 𝓑) =>
        snd_coor_set (setPO(𝓐)) (setPO(𝓑)) s hs


theorem leq_cart_prop : ∀ 𝓐 𝓑, ∀ s₁ s₂ ∈ po_set_cart 𝓐 𝓑; (
(s₁ . (leq_cart 𝓐 𝓑) . s₂) ↔ (((π₁ s₁) . ≼(𝓐) . (π₁ s₂)) ∧ ((π₂ s₁) . ≼(𝓑) . (π₂ s₂)))) :=
  fun (𝓐 𝓑) =>
    fun (s₁) =>
      fun (hs₁ : s₁ ∈ po_set_cart 𝓐 𝓑) =>
        fun (s₂) =>
          fun (hs₂ : s₂ ∈ po_set_cart 𝓐 𝓑) =>
                let S₁ := (po_set_cart 𝓐 𝓑)
                let S := (S₁) × (S₁)
                let P := po_set_prop 𝓐 𝓑
                Iff.intro
                (
                  fun (hs : (s₁, s₂) ∈ (leq_cart 𝓐 𝓑)) =>
                    let u := And.right (Iff.mp (spec_is_spec P S (s₁, s₂)) hs)

                    Exists.elim u (
                      fun (x₁) =>
                        fun (hx₁) =>
                          Exists.elim (And.right hx₁) (
                            fun (y₁) =>
                              fun (hy₁) =>
                                Exists.elim (And.right hy₁) (
                                  fun (x₂) =>
                                    fun (hx₂) =>
                                      Exists.elim (And.right hx₂) (
                                        fun (y₂) =>
                                          fun (hy₂) =>
                                            let u₁ := And.right (hy₂)
                                            let u₁₀ := And.left u₁
                                            let u₁₁ := Iff.mp (ordered_pair_set_prop s₁ s₂ (x₁, y₁) (x₂, y₂)) u₁₀
                                            let u₃ := coordinates_fst_coor x₁ y₁
                                            let u₃₀ := coordinates_fst_coor x₂ y₂
                                            let u₄ := eq_subst (fun (t) => (π₁ t) = x₁) (x₁, y₁) s₁ (Eq.symm (And.left u₁₁)) u₃
                                            let u₅ := eq_subst (fun (t) => (π₁ t) = x₂) (x₂, y₂) s₂ (Eq.symm (And.right u₁₁)) u₃₀
                                            let u₆ := And.left (And.right u₁)
                                            let u₇ := eq_subst (fun (t) => (t, x₂) ∈ (≼(𝓐))) x₁ (π₁ s₁) (Eq.symm u₄) (u₆)
                                            let u₈ := eq_subst (fun (t) => (π₁ s₁, t) ∈ (≼(𝓐))) x₂ (π₁ s₂) (Eq.symm u₅) (u₇)
                                            let u₉ := coordinates_snd_coor x₁ y₁
                                            let u₉₁ := coordinates_snd_coor x₂ y₂
                                            let u₆₁ := And.right (And.right u₁)
                                            let u₆₂ := eq_subst (fun (t) => (π₂ t) = y₁) (x₁, y₁) s₁ (Eq.symm (And.left u₁₁) ) u₉
                                            let u₆₃ := eq_subst (fun (t) => (π₂ t) = y₂) (x₂, y₂) s₂ (Eq.symm (And.right u₁₁)) u₉₁
                                            let u₆₄ := eq_subst (fun (t) => (t, y₂) ∈ (≼(𝓑))) y₁ (π₂ s₁) (Eq.symm u₆₂) (u₆₁)
                                            let u₆₅ := eq_subst (fun (t) => (π₂ s₁, t) ∈ (≼(𝓑))) y₂ (π₂ s₂) (Eq.symm u₆₃) (u₆₄)
                                            And.intro (u₈) (u₆₅)
                                      )
                                )
                          )
                    )
                )
                (
                  fun (hs : ((π₁ s₁) . ≼(𝓐) . (π₁ s₂)) ∧ ((π₂ s₁) . ≼(𝓑) . (π₂ s₂))) =>
                    let u₁ := poset_cart_prop₁ 𝓐 𝓑 (s₁) (hs₁)
                    let u₂ := poset_cart_prop₂ 𝓐 𝓑 (s₁) (hs₁)
                    let u₃ := poset_cart_prop₁ 𝓐 𝓑 (s₂) (hs₂)
                    let u₄ := poset_cart_prop₂ 𝓐 𝓑 (s₂) (hs₂)
                    Iff.mpr (spec_is_spec P S (s₁, s₂)) (
                      And.intro (
                        Iff.mpr (cartesian_product_pair_prop S₁ S₁ s₁ s₂) (
                          And.intro (hs₁) (hs₂)
                        )
                      ) (
                        Exists.intro (π₁ s₁) (
                          And.intro (u₁) (
                            Exists.intro (π₂ s₁) (
                              And.intro (u₂) (
                                Exists.intro (π₁ s₂) (
                                  And.intro (u₃) (
                                    Exists.intro (π₂ s₂) (
                                      And.intro (u₄) (
                                        And.intro (

                                          Iff.mpr (ordered_pair_set_prop s₁ s₂ (π₁ s₁, π₂ s₁) (π₁ s₂, π₂ s₂)) (
                                            And.intro (

                                              fst_snd_then_unique setPO(𝓐) setPO(𝓑) s₁ (hs₁)

                                            ) (
                                              fst_snd_then_unique setPO(𝓐) setPO(𝓑) s₂ (hs₂)
                                            )
                                          )

                                        ) (hs)
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )

                )



theorem cart_PO_PO : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (PartOrd (𝓐 Cart2CordPO 𝓑)) :=
  fun (𝓐 𝓑) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (h𝓑 : (PartOrd 𝓑)) =>
        let S := setPO(𝓐) × setPO(𝓑)
        let L := le_cart 𝓐 𝓑
        let LE := leq_cart 𝓐 𝓑
        let P := po_set_prop 𝓐 𝓑
        let prop₁ := specification_set_subset P (S × S)
        let prop₂ := fun (x y) => fun (hxy : (x, y) ∈ LE) =>
          let u₁ := prop₁ (x, y) (hxy)
          Iff.mp (cartesian_product_pair_prop S S x y) u₁
        Exists.intro S (
          Exists.intro L (
            Exists.intro LE (
              And.intro (Eq.refl (𝓐 Cart2CordPO 𝓑)) (

                let emp := Iff.mpr (set_non_empty_iff_non_empty S) (

                      let u := po_emp 𝓐 h𝓐
                      let v := po_emp 𝓑 h𝓑

                      let u₁ := Iff.mp (set_non_empty_iff_non_empty (setPO(𝓐))) u
                      let v₁ := Iff.mp (set_non_empty_iff_non_empty (setPO(𝓑))) v
                      Exists.elim u₁ (
                        fun (x) =>
                          fun (hx) =>
                            Exists.elim v₁ (
                              fun (y) =>
                                fun (hy) =>
                                  Exists.intro (x, y) (
                                    Iff.mpr (cartesian_product_pair_prop (setPO(𝓐)) (setPO(𝓑)) x y) (
                                      And.intro (hx) (hy)
                                    )
                                  )
                            )
                      )
                    )

                let subs : LE ⊆ (S × S) := specification_set_subset P (S × S)
                Iff.mpr (part_ord_nspo_crit S L LE) (
                  And.intro (emp) (
                    And.intro (
                      And.intro (subs) (
                        And.intro (
                          fun (x) =>
                            fun (hx : x ∈ S) =>
                              Iff.mpr (leq_cart_prop 𝓐 𝓑 x hx x hx) (


                                And.intro (refl_R₂ 𝓐 (h𝓐) (π₁ x) (poset_cart_prop₁ 𝓐 𝓑 x hx)) (
                                  refl_R₂ 𝓑 (h𝓑) (π₂ x) (poset_cart_prop₂ 𝓐 𝓑 x hx)
                                )
                              )
                        ) (And.intro (

                          fun (x y) =>
                            fun (hxy : (x, y) ∈ LE ∧ (y, x) ∈ LE) =>
                              let u₀ := prop₂ x y (And.left hxy)

                              let u₁ := Iff.mp (leq_cart_prop 𝓐 𝓑 x (And.left u₀) y (And.right u₀)) (And.left hxy)
                              let u₂ := Iff.mp (leq_cart_prop 𝓐 𝓑 y (And.right u₀) x (And.left u₀)) (And.right hxy)

                              let u₃ := antisymm_R₂ 𝓐 (h𝓐) (π₁ x) (π₁ y) (And.left u₁) (And.left u₂)
                              let u₄ := antisymm_R₂ 𝓑 (h𝓑) (π₂ x) (π₂ y) (And.right u₁) (And.right u₂)


                              equal_fst_snd (setPO(𝓐)) (setPO(𝓑)) x y (And.left u₀) (And.right u₀) (u₃) (u₄)

                        ) (

                          fun (x y z) =>
                            fun (hxyz : (x, y) ∈ LE ∧ (y, z) ∈ LE) =>

                              let u₀ := prop₂ x y (And.left hxyz)
                              let u₀₁:= prop₂ y z (And.right hxyz)

                              let u₁ := Iff.mp (leq_cart_prop 𝓐 𝓑 x (And.left u₀) y (And.right u₀)) (And.left hxyz)
                              let u₂ := Iff.mp (leq_cart_prop 𝓐 𝓑 y (And.right u₀) z (And.right u₀₁)) (And.right hxyz)

                              let u₃ := trans_R₂ 𝓐 (h𝓐) (π₁ x) (π₁ y) (π₁ z) (And.left u₁) (And.left u₂)
                              let u₄ := trans_R₂ 𝓑 (h𝓑) (π₂ x) (π₂ y) (π₂ z) (And.right u₁) (And.right u₂)

                              Iff.mpr (leq_cart_prop 𝓐 𝓑 x (And.left u₀) z (And.right u₀₁)) (

                                And.intro (u₃) (u₄)
                              )

                        ))
                      )
                    ) (Eq.refl L)
                  )
                )
              )
            )
          )
        )











noncomputable def sub_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊆ C ∧ z = (B, C) }
noncomputable def subneq_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊊ C ∧ z = (B, C) }
noncomputable def boolean_PO_set (A) := ⁅(𝒫 A); (subneq_binrel A); (sub_binrel A)⁆
syntax "BoolPO" term : term
macro_rules
| `(BoolPO $A:term) => `(boolean_PO_set $A)

theorem NSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (sub_binrel A) ↔ (B ⊆ C) :=
  fun (A) =>
    fun (B) =>
      fun (hB : B ∈ 𝒫 A) =>
        fun (C) =>
          fun (hC : C ∈ 𝒫 A) =>
            Iff.intro
            (
              fun (hbc : (B, C) ∈ (sub_binrel A)) =>
                let u := And.right (Iff.mp (spec_is_spec (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A))
                (B, C)) hbc)
                Exists.elim u (
                  fun (B₀) =>
                    fun (hB₀ : ∃ C₀, B₀ ⊆ C₀ ∧ (B, C) = (B₀, C₀)) =>
                      Exists.elim hB₀
                      (
                        fun (C₀) =>
                          fun (hC₀ : B₀ ⊆ C₀ ∧ (B, C) = (B₀, C₀)) =>
                            let v := Iff.mp (ordered_pair_set_prop B C B₀ C₀) (And.right hC₀)
                            eq_subst (fun (t) => B ⊆ t) C₀ C (Eq.symm (And.right v)) (
                              eq_subst (fun (t) => t ⊆ C₀) B₀ B (Eq.symm (And.left v)) (And.left hC₀)
                            )
                      )
                )

            )
            (
              fun (hbc : B ⊆ C) =>
                Iff.mpr (spec_is_spec (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) (B, C)) (
                  And.intro (Iff.mpr (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) (
                    And.intro (hB) (hC)
                  )) (
                    Exists.intro B (Exists.intro C (And.intro (hbc) (
                      Eq.refl (B, C)
                    )))
                  )
                )
            )


theorem SPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (subneq_binrel A) ↔ (B ⊊ C) :=
  fun (A) =>
    fun (B) =>
      fun (hB : B ∈ 𝒫 A) =>
        fun (C) =>
          fun (hC : C ∈ 𝒫 A) =>
            Iff.intro
            (
              fun (hbc : (B, C) ∈ (subneq_binrel A)) =>
                let u := And.right (Iff.mp (spec_is_spec (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A))
                (B, C)) hbc)
                Exists.elim u (
                  fun (B₀) =>
                    fun (hB₀ : ∃ C₀, B₀ ⊊ C₀ ∧ (B, C) = (B₀, C₀)) =>
                      Exists.elim hB₀
                      (
                        fun (C₀) =>
                          fun (hC₀ : B₀ ⊊ C₀ ∧ (B, C) = (B₀, C₀)) =>
                            let v := Iff.mp (ordered_pair_set_prop B C B₀ C₀) (And.right hC₀)
                            eq_subst (fun (t) => B ⊊ t) C₀ C (Eq.symm (And.right v)) (
                              eq_subst (fun (t) => t ⊊ C₀) B₀ B (Eq.symm (And.left v)) (And.left hC₀)
                            )
                      )
                )
            )
            (
              fun (hbc : B ⊊ C) =>
                Iff.mpr (spec_is_spec (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) (B, C)) (
                  And.intro (Iff.mpr (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) (
                    And.intro (hB) (hC)
                  )) (
                    Exists.intro B (Exists.intro C (And.intro (hbc) (
                      Eq.refl (B, C)
                    )))
                  )
                )
            )
theorem NSPO_bool_pair_prop_pa : ∀ A B C, (B, C) ∈ (sub_binrel A) ↔ (B ⊆ C ∧ B ∈ 𝒫 A ∧ C ∈ 𝒫 A) :=
  fun (A B C) =>
    Iff.intro
    (
      fun (hbc : (B, C) ∈ (sub_binrel A)) =>
        let u := And.left (Iff.mp (spec_is_spec (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C))
        ((𝒫 A) × (𝒫 A)) (B, C)) hbc)
        let v := Iff.mp (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) u
        And.intro (Iff.mp (NSPO_bool_pair_prop A B (And.left v) C (And.right v)) hbc) (v)
    )
    (
      fun (hbc : (B ⊆ C ∧ B ∈ 𝒫 A ∧ C ∈ 𝒫 A)) =>
        Iff.mpr (spec_is_spec (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) (B, C)) (
          And.intro (Iff.mpr (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) (And.intro (And.left (And.right hbc)) (
            And.right (And.right hbc)
          ))) (
            Exists.intro B (Exists.intro C (And.intro (And.left hbc) (Eq.refl (B, C))))
          )
        )
    )
theorem SPO_bool_pair_prop_pa : ∀ A B C, (B, C) ∈ (subneq_binrel A) ↔ (B ⊊ C ∧ B ∈ 𝒫 A ∧ C ∈ 𝒫 A) :=
  fun (A B C) =>
    Iff.intro
    (
      fun (hbc : (B, C) ∈ (subneq_binrel A)) =>
        let u := And.left (Iff.mp (spec_is_spec (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C))
        ((𝒫 A) × (𝒫 A)) (B, C)) hbc)
        let v := Iff.mp (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) u
        And.intro (Iff.mp (SPO_bool_pair_prop A B (And.left v) C (And.right v)) hbc) (v)
    )
    (
      fun (hbc : (B ⊊ C ∧ B ∈ 𝒫 A ∧ C ∈ 𝒫 A)) =>
        Iff.mpr (spec_is_spec (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) (B, C)) (
          And.intro (Iff.mpr (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) (And.intro (And.left (And.right hbc)) (
            And.right (And.right hbc)
          ))) (
            Exists.intro B (Exists.intro C (And.intro (And.left hbc) (Eq.refl (B, C))))
          )
        )
    )
theorem boolean_PO : ∀ A, (PartOrd (BoolPO A)) :=
  fun (A) =>
    po_is_triple_po (𝒫 A) (subneq_binrel A) (sub_binrel A) (
        Iff.mpr (part_ord_nspo_crit (𝒫 A) (subneq_binrel A) (sub_binrel A)) (
        And.intro (boolean_set_not_empty A) (

          And.intro (
            And.intro (
              specification_set_subset (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A))
            ) (
              And.intro (
                fun (x) =>
                  fun (hx : x ∈ 𝒫 A) =>
                    Iff.mpr (NSPO_bool_pair_prop A x hx x hx) (
                      subset_refl x
                    )

              ) (And.intro (
                fun (x y) =>
                  fun (hxy : (x, y) ∈ (sub_binrel A) ∧ (y, x) ∈ (sub_binrel A)) =>
                    let u := Iff.mp (NSPO_bool_pair_prop_pa A x y) (And.left hxy)
                    let v := Iff.mp (NSPO_bool_pair_prop_pa A y x) (And.right hxy)
                    extensionality x y (
                      fun (t) =>
                        Iff.intro
                        (And.left u t)
                        (And.left v t)
                    )

              ) (
                fun (x y z) =>
                  fun (hxy : (x, y) ∈ (sub_binrel A) ∧ (y, z) ∈ (sub_binrel A)) =>
                    let u := Iff.mp (NSPO_bool_pair_prop_pa A x y) (And.left hxy)
                    let v := Iff.mp (NSPO_bool_pair_prop_pa A y z) (And.right hxy)
                    Iff.mpr (NSPO_bool_pair_prop_pa A x z) (
                      And.intro (
                        fun (t) =>
                          fun (ht : t ∈ x) =>
                            And.left v t (And.left u t (ht))
                      ) (And.intro (And.left (And.right u)) (And.right (And.right v)))
                    )

              ))
            )

          ) (
            let u := bin_on_is_bin (𝒫 A) (subneq_binrel A) (
              specification_set_subset (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A))
            )

            let v := bin_on_is_bin (𝒫 A) (str (𝒫 A) (sub_binrel A)) (
              fun (pr) =>
                fun (hpr : pr ∈ (str (𝒫 A) (sub_binrel A))) =>
                  let u := And.left (Iff.mp (difference_prop (sub_binrel A) (id_ (𝒫 A)) pr) hpr)
                  specification_set_subset (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) pr u

            )

            relation_equality (subneq_binrel A) (str (𝒫 A) (sub_binrel A)) u v (
              fun (x y) =>
                Iff.intro
                (
                  fun (hxy : (x, y) ∈ (subneq_binrel A)) =>
                    Iff.mpr (difference_prop (sub_binrel A) (id_ (𝒫 A)) (x, y)) (
                      And.intro (

                        Iff.mpr (NSPO_bool_pair_prop_pa A x y) (
                          let first := Iff.mp (SPO_bool_pair_prop_pa A x y) hxy
                          And.intro (And.left (And.left first)) (And.right first)
                        )

                      ) (
                        fun (hxyid : (x, y) ∈ (id_ (𝒫 A))) =>
                          And.right (And.left (Iff.mp (SPO_bool_pair_prop_pa A x y) hxy)) (
                            And.left (And.left (id_prop (𝒫 A) x y hxyid))
                          )
                      )
                    )
                )
                (
                  fun (hxy : (x, y) ∈ str (𝒫 A) (sub_binrel A)) =>
                    Iff.mpr (SPO_bool_pair_prop_pa A x y) (
                      let u := Iff.mp (difference_prop (sub_binrel A) (id_ (𝒫 A)) (x, y)) hxy
                      let v := Iff.mp (NSPO_bool_pair_prop_pa A x y) (And.left u)
                      And.intro (And.intro (And.left v) (

                        fun (hxy : x = y) =>
                          And.right u (
                            eq_subst (fun (t) => (x . (id_ (𝒫 A)) . t)) x y (hxy) (
                              prop_then_id (𝒫 A) x (

                                And.left (And.right v)
                              )
                            )
                          )
                      )) (And.right v)
                    )
                )
            )
          )
        )
      )
    )
