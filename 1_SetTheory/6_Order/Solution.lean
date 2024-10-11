import «Header»
open Classical


def refl (R A : Set) : Prop := ∀ x ∈ A; (x . R . x)
def irrefl (R : Set) : Prop := ∀ x, ¬ (x . R . x)
def symm (R : Set) : Prop := ∀ x y, ((x . R . y) → (y . R . x))
def antisymm (R : Set) : Prop := ∀ x y, ((x . R . y) ∧ (y . R . x) → (x = y))
def asymm (R : Set) : Prop := ∀ x y, ((x . R . y) → ¬ (y . R . x))
def transit (R : Set) : Prop := ∀ x y z, (x . R . y) ∧ (y . R . z) → (x . R . z)
def str_conn (R A : Set) : Prop := ∀ x y ∈ A; ((x . R . y) ∨ (y . R . x))
def wkl_conn (R A : Set) : Prop := ∀ x y ∈ A; ((x ≠ y) → (x . R . y) ∨ (y . R . x))



theorem bin_on_is_bin : ∀ A R, binary_relation_on A R → binary_relation R :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      And.left (prop_then_binary_relation A A R hAR)
theorem id_is_binon : ∀ A, ((id_ A) BinRelOn A) :=
  fun (A) =>
    specification_set_subset (fun (t) => ∃ x : Set, t = (x, x)) (A × A)
theorem refl_crit : ∀ A R, binary_relation_on A R → ((refl R A) ↔ ((id_ A) ⊆ R)) :=
  fun (A R) =>
    fun (hAR : binary_relation_on A R) =>
      Iff.intro
      (
        fun (hrefl : (refl R A)) =>
          rel_subset (id_ A) R (id_is_rel A) (bin_on_is_bin A R (hAR)) (
            fun (x y) =>
              fun (hxy : (x . (id_ A) . y)) =>
                let u := (id_prop A x y hxy)
                let v := And.right (And.left u)
                let s := And.left (And.left u)
                eq_subst (fun (t) => (x . R . t)) x y (s) (hrefl x v)
          )
      )
      (
        fun (hidar : (id_ A) ⊆ R) =>
          fun (x) =>
            fun (hx : x ∈ A) =>
              hidar (x, x) (prop_then_id A x hx)
      )
theorem irrefl_crit : ∀ A R, binary_relation_on A R → ((irrefl R) ↔ (R ∩ (id_ A) = ∅)) :=
  fun (A R) =>
    fun (hAR : binary_relation_on A R) =>
      Iff.intro
      (
        fun (hirrefl : (irrefl R)) =>
          extensionality (R ∩ (id_ A)) ∅ (
            fun (pr) =>
              Iff.intro
              (
                rel_subset (R ∩ (id_ A)) ∅ (
                  intersect2_rel_is_rel R (id_ A) (bin_on_is_bin A R (hAR)) (id_is_rel A)
                ) (bin_on_is_bin A ∅ (empty_set_is_subset_any (A × A))) (
                  fun (x y) =>
                    fun (hxy : (x . (R ∩ (id_ A)) . y)) =>
                      let u := Iff.mp (intersect_2sets_prop R (id_ A) (x, y)) hxy
                      False.elim (hirrefl x (
                        eq_subst (fun (t) => (x, t) ∈ R) y x (Eq.symm (
                          And.left (And.left (id_prop A x y (And.right u)))
                        )) (And.left u)
                      ))
                ) pr
              )
              (
                empty_set_is_subset_any (R ∩ (id_ A)) pr
              )
          )
      )
      (
        fun (heq : (R ∩ (id_ A) = ∅)) =>
          fun (x) =>
            fun (hx : (x . R . x)) =>
              let u := And.left (Iff.mp (cartesian_product_pair_prop A A x x) (
                hAR (x, x) hx
              ))
              empty_set_is_empty (x, x) (
                eq_subst (fun (t) => (x . t . x)) (R ∩ (id_ A)) ∅ (heq) (
                  Iff.mpr (intersect_2sets_prop R (id_ A) (x, x)) (
                    And.intro (hx) (prop_then_id A x (u))
                  )
                )
              )
      )
theorem symmetric_crit_sub_left : ∀ A R, binary_relation_on A R → ((symm R) ↔ (R ⊆ R⁻¹)) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hrelsymm : (symm R)) =>
          rel_subset R (R⁻¹) (bin_on_is_bin A R (hAR)) (inv_is_rel R (bin_on_is_bin A R hAR)) (
            fun (x y) =>
              fun (hxy : (x . R . y)) =>
                Iff.mp (inv_pair_prop R (bin_on_is_bin A R hAR) y x) (
                  hrelsymm x y hxy
                )
          )
      )
      (
        fun (hRRinv : (R ⊆ R⁻¹)) =>
          fun (x y) =>
            fun (hxy : (x . R . y)) =>
              Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hAR) y x) (
                hRRinv (x, y) hxy
              )
      )
theorem symmetric_crit_sub_right : ∀ A R, binary_relation_on A R → ((symm R) ↔ (R⁻¹ ⊆ R)) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hrelsymm : (symm R)) =>
          rel_subset (R⁻¹) R (inv_is_rel R (bin_on_is_bin A R hAR)) (bin_on_is_bin A R (hAR)) (
            fun (x y) =>
              fun (hxy : (x . (R⁻¹) . y)) =>
                hrelsymm y x (
                  Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hAR) y x) hxy
                )
          )
      )
      (
        fun (hrr : (R⁻¹ ⊆ R)) =>
          fun (x y) =>
            fun (hxy : (x . R . y)) =>
              let u := Iff.mp (inv_pair_prop R (bin_on_is_bin A R hAR) x y) hxy
              hrr (y, x) u
      )
theorem symmetric_crit_eq : ∀ A R, binary_relation_on A R → ((symm R) ↔ (R = R⁻¹)) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hsym : (symm R)) =>
          extensionality R (R⁻¹) (
            fun (t) =>
              Iff.intro
              (
                (Iff.mp (symmetric_crit_sub_left A R hAR)) hsym t
              )
              (
                (Iff.mp (symmetric_crit_sub_right A R hAR)) hsym t
              )
          )
      )
      (
        fun (hrr : (R = R⁻¹)) =>
          Iff.mpr (symmetric_crit_sub_left A R (hAR)) (
            eq_subst (fun (t) => R ⊆ t) R (R⁻¹) (hrr) (subset_refl R)
          )
      )
theorem antisymmetric_crit : ∀ A R, binary_relation_on A R → ((antisymm R) ↔ (R ∩ R⁻¹ ⊆ (id_ A))) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hantisym : (antisymm R)) =>
          let v := (intersect2_rel_is_rel R (R⁻¹) (bin_on_is_bin A R hAR)
          (inv_is_rel R (bin_on_is_bin A R hAR)))
          rel_subset (R ∩ R⁻¹) (id_ A) v (id_is_rel A) (
            fun (x y) =>
              fun (hxy : (x . (R ∩ R⁻¹) . y)) =>
                let t := And.right (interset2sets_subset_prop R (R⁻¹)) (x, y) hxy
                let u := And.left (interset2sets_subset_prop R (R⁻¹)) (x, y) hxy
                let s := hAR (x, y) u
                let r := And.left (Iff.mp (cartesian_product_pair_prop A A x y) s)
                eq_subst (fun (t) => (x . (id_ A) . t)) x y (hantisym x y (
                  And.intro (u) (Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hAR) y x) (t))
                )) (prop_then_id A x (r))
          )
      )
      (
        fun (hrrid : (R ∩ R⁻¹ ⊆ (id_ A))) =>
          fun (x y) =>
            fun (hxy : (x . R . y) ∧ (y . R . x)) =>
             And.left ( And.left (id_prop A x y (
              hrrid (x, y) (Iff.mpr (intersect_2sets_prop R (R⁻¹) (x, y)) (
                And.intro (And.left hxy) (Iff.mp (inv_pair_prop R (bin_on_is_bin A R hAR) y x) (And.right hxy))
              ))
             )))
      )
theorem asymmetric_crit : ∀ A R, binary_relation_on A R → ((asymm R) ↔ (R ∩ R⁻¹ = ∅)) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hrr : (asymm R)) =>
          extensionality (R ∩ (R⁻¹)) (∅) (
            fun (f) =>
              Iff.intro
              (
                rel_subset (R ∩ (R⁻¹)) ∅ (intersect2_rel_is_rel R (R⁻¹) (bin_on_is_bin A R hAR) (
                  (inv_is_rel R (bin_on_is_bin A R hAR))
                )) (bin_on_is_bin A ∅ (empty_set_is_subset_any (A × A))) (
                  fun (x y) =>
                    fun (hxy : (x . (R ∩ (R⁻¹)) . y)) =>
                      False.elim (
                        let u := Iff.mp (intersect_2sets_prop R (R⁻¹) (x, y)) hxy
                        hrr x y (And.left u) (
                          Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hAR) y x) (And.right u)
                        )
                      )
                ) f
              )
              (empty_set_is_subset_any (R ∩ R⁻¹) f)
          )
      )
      (
        fun (hrrinvemp : (R ∩ R⁻¹ = ∅)) =>
          fun (x y) =>
            fun (hxy : (x . R . y)) =>
              fun (hyx : (y . R . x)) =>
                empty_set_is_empty (x, y) (
                  eq_subst (fun (t) => (x . (t) . y)) (R ∩ R⁻¹) (∅) (hrrinvemp) (
                    Iff.mpr (intersect_2sets_prop R (R⁻¹) (x, y)) (
                      And.intro (hxy) (Iff.mp (inv_pair_prop R (bin_on_is_bin A R hAR) y x) (hyx))
                    )
                  )
                )
      )
theorem transitive_crit : ∀ A R, binary_relation_on A R → ((transit R) ↔ (R ∘ R ⊆ R)) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hr : (transit R)) =>
          rel_subset (R ∘ R) R (composition_is_rel R R) (bin_on_is_bin A R hAR) (
            fun (x y) =>
              fun (hxy : (x . (R ∘ R) . y)) =>
                Exists.elim (Iff.mp (composition_pair_prop R R x y) hxy) (
                  fun (a) =>
                    fun (ha : (x . R . a) ∧ (a . R . y)) =>
                      hr x a y ha
                )
          )
      )
      (
        fun (hr : (R ∘ R ⊆ R)) =>
          fun (x y z) =>
            fun (hxyz : (x . R . y) ∧ (y . R . z)) =>
              hr (x, z) (Iff.mpr (composition_pair_prop R R x z) (
                Exists.intro y hxyz
              ))
      )
theorem strongly_connected_crit : ∀ A R, binary_relation_on A R → ((str_conn R A) ↔ ((A × A) ⊆ (R ∪ R⁻¹))) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hrr : (str_conn R A)) =>
          rel_subset (A × A) (R ∪ R⁻¹) (bin_on_is_bin A (A × A) (subset_refl (A × A))) (
            union2_rel_is_rel R (R⁻¹) (bin_on_is_bin A R hAR) (inv_is_rel R (bin_on_is_bin A R hAR))
          ) (
            fun (x y) =>
              fun (hxy : (x . (A × A) . y)) =>
                let u := Iff.mp (cartesian_product_pair_prop A A x y) hxy
                Iff.mpr (union2sets_prop R (R⁻¹) (x, y)) (
                  Or.elim (hrr x (And.left u) y (And.right u))
                  (Or.inl)
                  (
                    fun (hyx : (y . R . x)) =>
                      Or.inr (
                        Iff.mp (inv_pair_prop R (bin_on_is_bin A R hAR) y x) hyx
                      )
                  )
                )
          )
      )
      (
        fun (har : (A × A) ⊆ (R ∪ R⁻¹)) =>
          fun (x) => fun (hx : x ∈ A) =>
            fun (y) => fun (hy : y ∈ A) =>
              let u := Iff.mpr (cartesian_product_pair_prop A A x y) (And.intro hx hy)
              let v := har (x, y) u
              let s := Iff.mp (union2sets_prop R (R⁻¹) (x, y)) v
              Or.elim s
              (
                Or.inl
              )
              (
                fun (hxy : (x . (R⁻¹) . y)) =>
                  Or.inr (
                    Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hAR) y x) hxy
                  )
              )
      )
theorem weakly_connected_crit : ∀ A R, binary_relation_on A R → ((wkl_conn R A) ↔ (((A × A) \ (id_ A)) ⊆ (R ∪ R⁻¹))) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (relw : (wkl_conn R A)) =>
          rel_subset ((A × A) \ (id_ A)) (R ∪ R⁻¹) (
            bin_on_is_bin A ((A × A) \ (id_ A)) (difference_subset_prop (A × A) (id_ A))
          ) (
            union2_rel_is_rel R (R⁻¹) (bin_on_is_bin A R hAR) (inv_is_rel R (bin_on_is_bin A R hAR))
          ) (
            fun (x y) =>
              fun (hxy : (x . ((A × A) \ (id_ A)) . y)) =>
                let u := difference_subset_prop (A × A) (id_ A) (x, y) hxy
                let v := Iff.mp (cartesian_product_pair_prop A A x y) u
                let _ := relw x (And.left v) y (And.right v)
                let t := And.right (Iff.mp (difference_prop (A × A) (id_ A) (x, y)) hxy)
                let r := fun (hxey : (x = y)) =>
                  t (
                    eq_subst (fun (t) => (x . (id_ A) . t)) x y (hxey) (prop_then_id A x (And.left v))
                  )
                let m := relw x (And.left v) y (And.right v) r

                Iff.mpr (union2sets_prop R (R⁻¹) (x, y)) (
                  Or.elim m
                  (Or.inl)
                  (
                    fun (hyx : (y . R . x)) =>
                      Or.inr (Iff.mp (inv_pair_prop R (bin_on_is_bin A R hAR) y x) (hyx))
                  )
                )
          )
      )
      (
        fun (har : (((A × A) \ (id_ A)) ⊆ (R ∪ R⁻¹))) =>
          fun (x) =>
            fun (hx : (x ∈ A)) =>
              fun (y) =>
                fun (hy : (y ∈ A)) =>
                  fun (hny : (x ≠ y)) =>
                    let u := har (x, y) (
                      Iff.mpr (difference_prop (A × A) (id_ A) (x, y)) (
                        And.intro (Iff.mpr (cartesian_product_pair_prop A A x y) (And.intro (hx) (hy))) (

                          fun (hxy : (x . (id_ A) . y)) =>
                            (hny) (And.left (And.left (id_prop A x y hxy)))
                        )
                      )
                    )

                    let v := Iff.mp (union2sets_prop R (R⁻¹) (x, y)) u

                    Or.elim v
                    (
                      Or.inl
                    )
                    (
                      fun (hxrinvy : (x . (R⁻¹) . y)) =>
                        Or.inr (Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hAR) y x) (
                          hxrinvy
                        ))
                    )
      )



theorem assym_iff_antisymm_irrefl : ∀ A R, binary_relation_on A R → ((asymm R) ↔ (antisymm R ∧ irrefl R)) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hassym : (asymm R)) =>
          And.intro
          (
            Iff.mpr (antisymmetric_crit A R hAR) (
              eq_subst (fun (t) => t ⊆ (id_ A)) (∅) (R ∩ R⁻¹) (Eq.symm (Iff.mp (asymmetric_crit A R hAR) hassym)) (
                empty_set_is_subset_any (id_ A)
              )
            )
          ) (
            fun (x) =>
              fun (hx : (x . R . x)) =>
                  (hassym x x) hx hx
          )
      )
      (
        fun (hr : (antisymm R ∧ irrefl R)) =>
          fun (x y) =>
            fun (hxy : (x . R . y)) =>
              fun (hyx : (y . R . x)) =>
                let u := And.left hr x y (And.intro hxy hyx)
                And.right hr x (
                  eq_subst (fun (t) => (x . R . t)) y x (Eq.symm u) (hxy)
                )
      )
theorem strcon_iff_wkcon_refl : ∀ A R, binary_relation_on A R → ((str_conn R A) ↔ (wkl_conn R A ∧ refl R A)) :=
  fun (A R) =>
    fun (_ : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hstr : (str_conn R A)) =>
          And.intro (
            fun (x) =>
              fun (hx : x ∈ A) =>
                fun (y) =>
                  fun (hy : y ∈ A) =>
                    fun (_ : x ≠ y) =>
                      hstr x hx y hy
          ) (
            fun (x) =>
              fun (hx : x ∈ A) =>
                Or.elim (hstr x hx x hx)
                (
                  fun (hxr : (x . R . x)) =>
                    hxr
                )
                (fun (hxr : (x . R . x)) =>
                    hxr
                )
          )
      )
      (
        fun (hwcrfl : (wkl_conn R A ∧ refl R A)) =>
          fun (x) =>
            fun (hx : x ∈ A) =>
              fun (y) =>
                fun (hy : y ∈ A) =>
                  Or.elim (em (x = y))
                  (
                    fun (hxy : (x = y)) =>
                      Or.inl (
                        eq_subst (fun (t) => (x . R . t)) x y (hxy) (And.right hwcrfl x hx)
                      )
                  )
                  (
                    And.left (hwcrfl) x hx y hy
                  )

      )
theorem emp_refl_irrefl : ∀ A R, binary_relation_on A R → ((A = ∅) ↔ (refl R A ∧ irrefl R)) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (Aemp : (A = ∅)) =>
          And.intro (
            fun (x) =>
              fun (hx : x ∈ A) =>
                False.elim (
                  empty_set_is_empty x (
                    eq_subst (fun (t) => x ∈ t) A ∅ (Aemp) (hx)
                  )
                )

          ) (
            fun (x) =>
              fun (hxR : (x . R . x)) =>
                Or.elim (em (x ∈ A))
                (
                  fun (hx : x ∈ A) =>
                  False.elim (
                    empty_set_is_empty x (
                      eq_subst (fun (t) => x ∈ t) A ∅ (Aemp) (hx)
                    )
                  )
                )
                (
                  fun (hx : x ∉ A) =>
                    hx (
                      And.left (Iff.mp (cartesian_product_pair_prop A A x x) (
                        hAR (x, x) (hxR)
                      ))
                    )
                )
          )
      )
      (
       fun (hrr : (refl R A ∧ irrefl R)) =>
        extensionality A ∅ (
          fun (x) =>
            Iff.intro
            (
              fun (hx : (x ∈ A)) =>
                False.elim (And.right hrr x (
                  And.left hrr x hx
                ))
            )
            (empty_set_is_subset_any A x)
        )
      )
theorem emp_symm_asymm : ∀ A R, binary_relation_on A R → ((R = ∅) ↔ (symm R ∧ asymm R)) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (Aemp : (R = ∅)) =>
          And.intro (
            fun (x y) =>
              fun (hxy : (x . R . y)) =>
                False.elim (
                  empty_set_is_empty (x, y) (
                    eq_subst (fun (t) => (x . t . y)) R ∅ (Aemp) (hxy)
                  )
                )


          ) (fun (x y) =>
              fun (hxy : (x . R . y)) =>
                False.elim (
                  empty_set_is_empty (x, y) (
                    eq_subst (fun (t) => (x . t . y)) R ∅ (Aemp) (hxy)
                  )
                ))
      )
      (
        fun (hsymasymm : (symm R ∧ asymm R)) =>
          extensionality R ∅ (
            fun (s) =>
              Iff.intro
              (
                rel_subset R ∅ (bin_on_is_bin A R (hAR)) (bin_on_is_bin A ∅ (empty_set_is_subset_any (A × A))) (
                  fun (x y) =>
                    fun (hxy : (x . R . y)) =>
                      False.elim (
                        And.right hsymasymm x y hxy (
                          And.left hsymasymm x y (hxy)
                        )
                      )
                ) s
              )
              (empty_set_is_subset_any R s)
          )
      )
theorem trans_irrefl_antisymm : ∀ A R, binary_relation_on A R → (transit R) → (irrefl R) → (antisymm R) :=
  fun (A R) =>
    fun (_ : (binary_relation_on A R)) =>
      fun (htr : (transit R)) =>
        fun (hirr : (irrefl R)) =>
          fun (x y) =>
            fun (hxy : (x . R . y) ∧ (y . R . x)) =>
              let u := htr x y x hxy
              False.elim (
                hirr x u
              )
theorem trans_irrefl_asymm : ∀ A R, binary_relation_on A R → (transit R) → (irrefl R) → (asymm R) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      fun (htr : (transit R)) =>
        fun (hirr : (irrefl R)) =>
          Iff.mpr (assym_iff_antisymm_irrefl A R hAR) (
            And.intro (trans_irrefl_antisymm A R hAR htr hirr) (hirr)
          )
theorem refl_symm_antisymm : ∀ A R, binary_relation_on A R → (((refl R A) ∧ (symm R) ∧ (antisymm R)) ↔ (R = (id_ A))) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      Iff.intro
      (
        fun (hr : ((refl R A) ∧ (symm R) ∧ (antisymm R))) =>
          extensionality (R) (id_ A) (
            fun (t) =>
              Iff.intro
              (
                let u := Iff.mp (symmetric_crit_eq A R hAR) (And.left (And.right hr))

                let v := Iff.mp (antisymmetric_crit A R hAR) (And.right (And.right hr))

                let s := eq_subst (fun (t) => R ∩ t ⊆ (id_ A)) (R⁻¹) (R) (Eq.symm u) (v)

                let k := eq_subst (fun (t) => t ⊆ (id_ A)) (R ∩ R) (R) (
                  intersec2_idemp R

                ) (s)

                k t

              )
              (Iff.mp (refl_crit A R hAR) (And.left hr) t)
          )
      )
      (
        fun (hR : (R = (id_ A))) =>
          And.intro (Iff.mpr (refl_crit A R hAR) (
            eq_subst (fun (t) => t ⊆ R) (R) (id_ A) (hR) (subset_refl R)
          )) (And.intro (
            fun (x y) =>
              fun (hxy : (x . R . y)) =>
                eq_subst (fun (t) => (t . R . x)) x y (
                  And.left (And.left (id_prop A x y (
                    eq_subst (fun (q) => (x . q . y)) R (id_ A) (hR) (hxy)
                  )))
                ) (
                  eq_subst (fun (q) => (x . q . x)) (id_ A) R (Eq.symm hR) (prop_then_id A x (

                    And.left (Iff.mp (cartesian_product_pair_prop A A x y) (
                      hAR (x, y) hxy
                    ))
                  ))
                )
          ) (
            fun (x y) =>
              fun (hxy : (x . R . y) ∧ (y . R . x)) =>
                And.left (And.left ((id_prop A x y) (
                  eq_subst (fun (t) => (x . t . y)) R (id_ A) (hR) (And.left hxy))
                )))
          )
        )


theorem inv_binon : ∀ A R, (R BinRelOn A) → ((R⁻¹) BinRelOn A) :=
  fun (A R) =>
    fun (hAR : (R BinRelOn A)) =>
      inv_between_mp A A R hAR
theorem refl_inv : ∀ A R, (R BinRelOn A) → ((refl R A) ↔ (refl (R⁻¹) A)) :=
  fun (A R) =>
    fun (hRA : (R BinRelOn A)) =>
      Iff.intro
      (
        fun (hrfl : (refl R A)) =>
          fun (x) =>
            fun (hx : x ∈ A) =>
              Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x x) (
                hrfl x hx
              )
      )
      (
        fun (hinvrfl : (refl (R⁻¹) A)) =>
          fun (x) =>
            fun (hx : x ∈ A) =>
              Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) x x) (
                hinvrfl x hx
              )
      )
theorem irrefl_inv : ∀ A R, (R BinRelOn A) → ((irrefl R) ↔ (irrefl (R⁻¹))) :=
  fun (A R) =>
    fun (hRA : (R BinRelOn A)) =>
      Iff.intro
      (
        fun (hirfl : (irrefl R)) =>
          fun (x) =>
            fun (hxr : (x . (R⁻¹) . x)) =>
              hirfl x (
                Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) x x) (
                  hxr
                )
              )
      )
      (
        fun (hirfl : (irrefl (R⁻¹))) =>
          fun (x) =>
            fun (hxr : (x . R . x)) =>
              hirfl x (
                Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x x) (hxr)
              )
      )
theorem symm_inv : ∀ A R, (R BinRelOn A) → ((symm R) ↔ (symm (R⁻¹))) :=
  fun (A R) =>
    fun (hRA : (R BinRelOn A)) =>
      Iff.intro
      (
        fun (hsymmr : (symm R)) =>
          fun (x y) =>
            fun (hxy : (x . (R⁻¹) . y)) =>
              let u := Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) y x) hxy
              let v := hsymmr y x u
              Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (v)
      )
      (
        fun (hsymminvr : (symm (R⁻¹))) =>
          fun (x y) =>
            fun (hxy : (x . R . y)) =>
              let u := Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x y) hxy
              let v := hsymminvr y x u
              Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) y x) (
                v
              )
      )
theorem antisymm_inv : ∀ A R, (R BinRelOn A) → ((antisymm R) ↔ (antisymm (R⁻¹))) :=
  fun (A R) =>
    fun (hRA : (R BinRelOn A)) =>
      Iff.intro
      (
        fun (hantis : (antisymm R)) =>
          fun (x y) =>
            fun (hxy : (x . (R⁻¹) . y) ∧ (y . (R⁻¹) . x)) =>
              hantis x y (And.intro (Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (And.right hxy)) (
                Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) y x) (
                  And.left hxy
                )
              ))
      )
      (
        fun (hantis : (antisymm (R⁻¹))) =>
          fun (x y) =>
            fun (hxy : (x . R . y) ∧ (y . R . x)) =>
              hantis x y (
                And.intro (Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) y x) (And.right hxy)) (
                  Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (And.left hxy)
                )
              )
      )
theorem asymm_inv : ∀ A R, (R BinRelOn A) → ((asymm R) ↔ (asymm (R⁻¹))) :=
  fun (A R) =>
    fun (hRA : (R BinRelOn A)) =>
      Iff.intro
      (
        fun (hasymm : (asymm R)) =>
          fun (x y) =>
            fun (hxy : (x . (R⁻¹) . y)) =>
              fun (hyx : (y . (R⁻¹) . x)) =>
                hasymm x y (Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (hyx)) (
                  Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) y x) (hxy)
                )
      )
      (
        fun (hinvassym : (asymm (R⁻¹))) =>
          fun (x y) =>
            fun (hxy : (x . R . y)) =>
              fun (hyx : (y . R . x)) =>
                hinvassym x y (Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) y x) (hyx)) (
                  Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (hxy)
                )

      )
theorem transit_inv : ∀ A R, (R BinRelOn A) → ((transit R) ↔ (transit (R⁻¹))) :=
  fun (A R) =>
    fun (hRA : (R BinRelOn A)) =>
      Iff.intro
      (
        fun (transr : (transit R)) =>
          fun (x y z) =>
            fun (hxyz : (x . (R⁻¹) . y) ∧ (y . (R⁻¹) . z)) =>
              Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) z x) (
                transr z y x (And.intro (
                  Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) z y) (And.right hxyz)
                ) (
                  Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) y x) (And.left hxyz)
                ))
              )
      )
      (
        fun (transrinv : (transit (R⁻¹))) =>
          fun (x y z) =>
            fun (hxyz : (x . R . y) ∧ (y . R . z)) =>
              Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) x z) (
                transrinv z y x (
                  And.intro (Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) y z) (And.right hxyz)) (
                    Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (And.left hxyz)
                  )
                )
              )
      )
theorem str_conn_inv : ∀ A R, (R BinRelOn A) → ((str_conn R A) ↔ (str_conn (R⁻¹) A)) :=
  fun (A R) =>
    fun (hRA : (R BinRelOn A)) =>
      Iff.intro
      (
        fun (hstr : (str_conn R A)) =>
          fun (x) =>
            fun (hx : x ∈ A) =>
              fun (y) =>
                fun (hy : y ∈ A) =>
                  let u := hstr x hx y hy
                  Or.elim u
                  (
                    fun (hxyr : (x . R . y)) =>
                      Or.inr (
                        Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x y) hxyr
                      )
                  )
                  (
                    fun (hxyr : (y . R . x)) =>
                      Or.inl (
                        Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) y x) hxyr
                      )
                  )
      )
      (
        fun (hstr : (str_conn (R⁻¹) A)) =>
          fun (x) =>
            fun (hx : x ∈ A) =>
              fun (y) =>
                fun (hy : y ∈ A) =>
                  let u := hstr x hx y hy
                  Or.elim u
                  (
                    fun (hxyr : (x . (R⁻¹) . y)) =>
                      Or.inr (
                        Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) y x) (hxyr)
                      )
                  )
                  (
                    fun (hxyr : (y . (R⁻¹) . x)) =>
                      Or.inl (
                        Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (hxyr)
                      )
                  )
      )
theorem wkl_conn_inv : ∀ A R, (R BinRelOn A) → ((wkl_conn R A) ↔ (wkl_conn (R⁻¹) A)) :=
  fun (A R) =>
    fun (hRA : (R BinRelOn A)) =>
      Iff.intro
      (
        fun (hwkstr : (wkl_conn R A)) =>
          fun (x) =>
            fun (hx : x ∈ A) =>
              fun (y) =>
                fun (hy : y ∈ A) =>
                  fun (hxy : x ≠ y) =>
                    let u := hwkstr x hx y hy hxy
                    Or.elim u
                    (
                      fun (hxyr : (x . R . y)) =>
                        Or.inr (
                          Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (hxyr)
                        )
                    )
                    (
                      fun (hxyr : (y . R . x)) =>
                        Or.inl (
                          Iff.mp (inv_pair_prop R (bin_on_is_bin A R hRA) y x) hxyr
                        )
                    )
      )
      (
        fun (hwkstr : (wkl_conn (R⁻¹) A)) =>
          fun (x) =>
            fun (hx : x ∈ A) =>
              fun (y) =>
                fun (hy : y ∈ A) =>
                  fun (hxy : x ≠ y) =>
                    let u := hwkstr x hx y hy hxy
                    Or.elim u
                    (
                      fun (hxyr : (x . (R⁻¹) . y)) =>
                        Or.inr (
                          Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) y x) (hxyr)
                        )
                    )
                    (
                      fun (hxyr : (y . (R⁻¹) . x)) =>
                        Or.inl (
                          Iff.mpr (inv_pair_prop R (bin_on_is_bin A R hRA) x y) (hxyr)
                        )
                    )
      )
theorem compos_binon : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → ((P ∘ Q) BinRelOn A) :=
  fun (A P Q) =>
    fun (hPA : (P BinRelOn A)) =>
      fun (hQA : (Q BinRelOn A)) =>
        rel_subset ((P ∘ Q)) (A × A) (composition_is_rel P Q) (bin_on_is_bin A (A × A) (subset_refl (A × A))) (
          fun (x y) =>
            fun (hxy : (x . (P ∘ Q) . y)) =>
              let u := Iff.mp (composition_pair_prop P Q x y) hxy
              Exists.elim u (
                fun (z) =>
                  fun (hz : (x . Q . z) ∧ (z . P . y)) =>
                    let v := hQA (x, z) (And.left hz)
                    let s := hPA (z, y) (And.right hz)
                    let t := And.left (Iff.mp (cartesian_product_pair_prop A A x z) v)
                    let m := And.right (Iff.mp (cartesian_product_pair_prop A A z y) s)
                    Iff.mpr (cartesian_product_pair_prop A A x y) (And.intro (t) (m))
              )
        )
theorem refl_compos_char : ∀ A P Q, (refl P A) → (refl Q A) → (refl (P ∘ Q) A) :=
  fun (A P Q) =>
    fun (hreflP : (refl P A)) =>
      fun (hreflQ : (refl Q A)) =>
        fun (x) =>
          fun (hx : x ∈ A) =>
            Iff.mpr (composition_pair_prop P Q x x) (
              Exists.intro x (And.intro (hreflQ x hx) (hreflP x hx))
            )
theorem refl_compos_prop : ∀ A P Q, (refl (P ∘ Q) A) → ((is_surjective P A) ∧ (is_total Q A)) :=
  fun (A P Q) =>
      fun (hreflpq : refl (P ∘ Q) A) =>
        And.intro (
          fun (y) =>
            fun (hy : y ∈ A) =>
              let u := hreflpq y hy
              let v := Iff.mp (composition_pair_prop P Q y y) u
              Exists.elim v (
                fun (x) =>
                  fun (hx : (y . Q . x) ∧ (x . P . y)) =>
                    Exists.intro x (And.right hx)
              )
        ) (
          fun (x) =>
            fun (hx : x ∈ A) =>
              let u := hreflpq x hx
              let v := Iff.mp (composition_pair_prop P Q x x) u
              Exists.elim v (
                fun (y) =>
                  fun (hy : (x . Q . y) ∧ (y . P . x)) =>
                    Exists.intro y (And.left hy)
              )
        )
theorem symm_compos_prop : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → (symm P) → (symm Q) → (((P ∘ Q)⁻¹) = (Q ∘ P)) :=
  fun (A P Q) =>
    fun (binp : (P BinRelOn A)) =>
      fun (binq : (Q BinRelOn A)) =>
        fun (hpsymm : (symm P)) =>
          fun (hqsymm : (symm Q)) =>
            let u := inv_composition_prop P Q (bin_on_is_bin A P binp) (bin_on_is_bin A Q binq)
            let v := eq_subst (fun (t) => (P ∘ Q)⁻¹ = t ∘ (P⁻¹)) (Q⁻¹) Q (Eq.symm (Iff.mp (symmetric_crit_eq A Q binq) (hqsymm))) (
              u)
            eq_subst (fun (t) => (P ∘ Q)⁻¹ = Q ∘ t) (P⁻¹) (P) (Eq.symm (Iff.mp (symmetric_crit_eq A P binp) (hpsymm))) (v)

theorem subs_binon : ∀ A P Q, (Q BinRelOn A) → (P ⊆ Q) → (P BinRelOn A) :=
  fun (A P Q) =>
    fun (hQA : (Q BinRelOn A)) =>
      fun (hPQ : P ⊆ Q) =>
        fun (x) =>
          fun (hx : x ∈ P) =>
            hQA x (hPQ x hx)
theorem refl_subs : ∀ A P Q, (refl P A) → (P ⊆ Q) → (refl Q A) :=
  fun (A P Q) =>
    fun (hreflp : (refl P A)) =>
      fun (hpq : (P ⊆ Q)) =>
        fun (x) =>
          fun (hx : x ∈ A) =>
            hpq (x, x) (hreflp x hx)
theorem irrefl_subs : ∀ P Q, (irrefl Q) → (P ⊆ Q) → (irrefl P) :=
  fun (P Q) =>
    fun (hirrefl : (irrefl Q)) =>
      fun (hpq : (P ⊆ Q)) =>
        fun (x) =>
          fun (hxx : (x . P . x)) =>
            hirrefl x (hpq (x, x) (hxx))
theorem antisymm_subs : ∀ P Q, (antisymm Q) → (P ⊆ Q) → (antisymm P) :=
  fun (P Q) =>
    fun (hantisymm : (antisymm Q)) =>
      fun (hpq : (P ⊆ Q)) =>
        fun (x y) =>
          fun (hxy : (x . P . y) ∧ (y . P . x)) =>
            hantisymm x y (And.intro (hpq (x, y) (And.left hxy)) (hpq (y, x) (And.right hxy)))
theorem asymm_subs : ∀ P Q, (asymm Q) → (P ⊆ Q) → (asymm P) :=
  fun (P Q) =>
    fun (hasymm : (asymm Q)) =>
      fun (hpq : (P ⊆ Q)) =>
        fun (x y) =>
          fun (hxy : (x . P . y)) =>
            fun (hyx : (y . P . x)) =>
              let u := hpq (x, y) hxy
              let v := hpq (y, x) hyx
              hasymm x y u v
theorem str_conn_subs : ∀ A P Q, (P ⊆ Q) → (str_conn P A) → (str_conn Q A) :=
  fun (A P Q) =>
    fun (hpq : (P ⊆ Q)) =>
      fun (hstr : (str_conn P A)) =>
        fun (x) =>
          fun (hx : x ∈ A) =>
            fun (y) =>
              fun (hy : y ∈ A) =>
                Or.elim (hstr x hx y hy)
                (
                  fun (hxpy : (x . P . y)) =>
                    Or.inl (hpq (x, y) hxpy)
                )
                (
                  fun (hxpy : (y . P . x)) =>
                    Or.inr (hpq (y, x) hxpy)
                )
theorem wkl_conn_subs : ∀ A P Q, (P ⊆ Q) → (wkl_conn P A) → (wkl_conn Q A) :=
  fun (A P Q) =>
    fun (hpq : (P ⊆ Q)) =>
      fun (hwkl : (wkl_conn P A)) =>
        fun (x) =>
          fun (hx : x ∈ A) =>
            fun (y) =>
              fun (hy : y ∈ A) =>
                fun (hxy : (x ≠ y)) =>
                  Or.elim (hwkl x hx y hy hxy)
                  (
                    fun (hxpy : (x . P . y)) =>
                      Or.inl (hpq (x, y) hxpy)
                  )
                  (
                    fun (hxpy : (y . P . x)) =>
                      Or.inr (hpq (y, x) hxpy)
                  )


theorem un_binon : ∀ A P Q, (P BinRelOn A) → (Q BinRelOn A) → ((P ∪ Q) BinRelOn A) :=
  fun (A P Q) =>
    fun (hPA : (P BinRelOn A)) =>
      fun (hQA : (Q BinRelOn A) ) =>
        fun (x) =>
          fun (hx : x ∈ (P ∪ Q)) =>
            Or.elim (Iff.mp (union2sets_prop P Q x) hx)
            (
              fun (hxP : x ∈ P) =>
                hPA x hxP
            )
            (
              fun (hxQ : x ∈ Q) =>
                hQA x hxQ
            )
theorem refl_un_left : ∀ A P Q, (refl P A) → (refl (P ∪ Q) A) :=
  fun (A P Q) =>
    fun (hreflP : (refl P A)) =>
        fun (x) =>
          fun (hx : x ∈ A) =>
            Iff.mpr (union2sets_prop P Q (x, x)) (
              Or.inl (hreflP x hx)
            )
theorem refl_un_right : ∀ A P Q, (refl Q A) → (refl (P ∪ Q) A) :=
  fun (A P Q) =>
    fun (hreflQ : (refl Q A)) =>
      fun (x) =>
        fun (hx : x ∈ A) =>
          Iff.mpr (union2sets_prop P Q (x, x)) (
            Or.inr (hreflQ x hx)
          )
theorem irrefl_un : ∀ P Q, (irrefl P) → (irrefl Q) → (irrefl (P ∪ Q)) :=
  fun (P Q) =>
    fun (hirreflP : (irrefl P)) =>
      fun (hirreflQ : (irrefl Q)) =>
        fun (x) =>
          fun (hx : (x . (P ∪ Q) . x)) =>
            Or.elim (Iff.mp (union2sets_prop P Q (x, x)) hx)
            (
              fun (hxp : (x . P . x)) =>
                hirreflP x hxp
            )
            (
              fun (hxq : (x . Q . x)) =>
                hirreflQ x hxq
            )
theorem symm_un : ∀ P Q, (symm P) → (symm Q) → (symm (P ∪ Q)) :=
  fun (P Q) =>
    fun (hsymmP : (symm P)) =>
      fun (hsymmQ : (symm Q)) =>
        fun (x y) =>
          fun (hxypq : (x . (P ∪ Q) . y)) =>
            let u := Iff.mp (union2sets_prop P Q (x, y)) hxypq
            Iff.mpr (union2sets_prop P Q (y, x)) (
              Or.elim u
              (
                fun (xyp : (x . P . y)) =>
                  Or.inl (hsymmP x y xyp)
              )
              (
                fun (xyq : (x . Q . y)) =>
                  Or.inr (hsymmQ x y xyq)
              )
            )
theorem str_con_un_left : ∀ A P Q, (str_conn P A) → (str_conn (P ∪ Q) A) :=
  fun (A P Q) =>
    fun (hstrconP : (str_conn P A)) =>
        str_conn_subs A P (P ∪ Q) (
          And.left (union2sets_subset_prop P Q)
        ) (hstrconP)
theorem str_con_un_right : ∀ A P Q, (str_conn Q A) → (str_conn (P ∪ Q) A) :=
  fun (A P Q) =>
    fun (hstrconQ : (str_conn Q A)) =>
        str_conn_subs A Q (P ∪ Q) (
          And.right (union2sets_subset_prop P Q)
        ) (hstrconQ)
theorem wkl_con_un_left : ∀ A P Q, (wkl_conn P A) → (wkl_conn (P ∪ Q) A) :=
  fun (A P Q) =>
    fun (hwkconP : (wkl_conn P A)) =>
      wkl_conn_subs A P (P ∪ Q) (
        And.left (union2sets_subset_prop P Q)
      ) (hwkconP)
theorem wkl_con_un_right : ∀ A P Q, (wkl_conn Q A) → (wkl_conn (P ∪ Q) A) :=
  fun (A P Q) =>
    fun (hwkconQ : (wkl_conn Q A)) =>
      wkl_conn_subs A Q (P ∪ Q) (
        And.right (union2sets_subset_prop P Q)
      ) (hwkconQ)



theorem int_binon_left : ∀ A P Q, (P BinRelOn A) → ((P ∩ Q) BinRelOn A) :=
  fun (A P Q) =>
    fun (hPA : (P BinRelOn A)) =>
      subs_binon A (P ∩ Q) P hPA (
        And.left (interset2sets_subset_prop P Q)
      )
theorem int_binon_right : ∀ A P Q, (Q BinRelOn A) → ((P ∩ Q) BinRelOn A) :=
  fun (A P Q) =>
    fun (hQA : (Q BinRelOn A)) =>
      subs_binon A (P ∩ Q) Q hQA (
        And.right (interset2sets_subset_prop P Q)
      )
theorem refl_int : ∀ A P Q, (refl P A) → (refl Q A) → (refl (P ∩ Q) A) :=
  fun (A P Q) =>
    fun (hreflP : (refl P A)) =>
      fun (hreflQ : (refl Q A)) =>
        fun (x) =>
          fun (hx : x ∈ A) =>
            Iff.mpr (intersect_2sets_prop P Q (x, x)) (
              And.intro (hreflP x hx) (hreflQ x hx)
            )
theorem irrefl_int_left : ∀ P Q, (irrefl P) → (irrefl (P ∩ Q)) :=
  fun (P Q) =>
    fun (hirreflP : (irrefl P)) =>
        fun (x) =>
          fun (hx : (x . (P ∩ Q) . x)) =>
            (hirreflP x) (And.left (Iff.mp (intersect_2sets_prop P Q (x, x)) hx))
theorem irrefl_int_right : ∀ P Q, (irrefl Q) → (irrefl (P ∩ Q)) :=
  fun (P Q) =>
    fun (hirreflQ : (irrefl Q)) =>
      fun (x) =>
        fun (hx : (x . (P ∩ Q) . x)) =>
          (hirreflQ x) (And.right (Iff.mp (intersect_2sets_prop P Q (x, x)) (hx)))
theorem symm_int : ∀ P Q, (symm P) → (symm Q) → (symm (P ∩ Q)) :=
  fun (P Q) =>
    fun (hsymmP : (symm P)) =>
      fun (hsymmQ : (symm Q)) =>
        fun (x y) =>
          fun (hxyPQ : (x . (P ∩ Q) . y)) =>
            let u := Iff.mp (intersect_2sets_prop P Q (x, y)) hxyPQ
            Iff.mpr (intersect_2sets_prop P Q (y, x)) (
              And.intro (hsymmP x y (And.left u)) (hsymmQ x y (And.right u))
            )
theorem antisym_int_left : ∀ P Q, (antisymm P) → (antisymm (P ∩ Q)) :=
  fun (P Q) =>
    fun (hantisymmP : (antisymm P)) =>
        fun (x y) =>
          fun (hxy : (x . (P ∩ Q) . y) ∧ (y . (P ∩ Q) . x)) =>
            let u := Iff.mp (intersect_2sets_prop P Q (x, y)) (And.left hxy)
            let v := Iff.mp (intersect_2sets_prop P Q (y, x)) (And.right hxy)
            hantisymmP x y (And.intro (And.left u) (And.left v))
theorem antisym_int_right : ∀ P Q, (antisymm Q) → (antisymm (P ∩ Q)) :=
  fun (P Q) =>
    fun (hantisymmP : (antisymm Q)) =>
        fun (x y) =>
          fun (hxy : (x . (P ∩ Q) . y) ∧ (y . (P ∩ Q) . x)) =>
            let u := Iff.mp (intersect_2sets_prop P Q (x, y)) (And.left hxy)
            let v := Iff.mp (intersect_2sets_prop P Q (y, x)) (And.right hxy)
            hantisymmP x y (And.intro (And.right u) (And.right v))
theorem trans_int : ∀ P Q, (transit P) → (transit Q) → (transit (P ∩ Q)) :=
  fun (P Q) =>
    fun (htransP : (transit P)) =>
      fun (htransQ : (transit Q)) =>
        fun (x y z) =>
          fun (hxyz : (x . (P ∩ Q) . y) ∧ (y . (P ∩ Q) . z)) =>
            let u := Iff.mp (intersect_2sets_prop P Q (x, y)) (And.left hxyz)
            let v := Iff.mp (intersect_2sets_prop P Q (y, z)) (And.right hxyz)
            Iff.mpr (intersect_2sets_prop P Q (x, z)) (
              And.intro (
                htransP x y z (And.intro (And.left u) (And.left v))
              ) (htransQ x y z (And.intro (And.right u) (And.right v)))
            )


theorem diff_binon : ∀ A P Q, (P BinRelOn A) → ((P \ Q) BinRelOn A) :=
  fun (A P Q) =>
    fun (hPA : (P BinRelOn A)) =>
      subs_binon A (P \ Q) P hPA (
        difference_subset_prop P Q
      )
theorem irrefl_diff : ∀ P Q, (irrefl P) → (irrefl (P \ Q)) :=
  fun (P Q) =>
    fun (hirreflP : (irrefl P)) =>
      fun (x) =>
        fun (hx : (x . (P \ Q) . x)) =>
          let u := Iff.mp (difference_prop P Q (x, x)) hx
          hirreflP x (And.left u)
theorem symm_diff : ∀ P Q, (symm P) → (symm Q) → (symm (P \ Q)) :=
  fun (P Q) =>
    fun (hsymmP : (symm P)) =>
      fun (hsymmQ : (symm Q)) =>
        fun (x y) =>
          fun (hxy : (x . (P \ Q) . y)) =>
            let u := Iff.mp (difference_prop P Q (x, y)) hxy
            Iff.mpr (difference_prop P Q (y, x)) (
              And.intro (hsymmP x y (And.left u)) (
                fun (hxyQ : (y . Q . x)) =>
                  And.right u (hsymmQ y x hxyQ)
              )
            )
theorem asymm_diff : ∀ P Q, (asymm P) → (asymm (P \ Q)) :=
  fun (P Q) =>
    fun (hassymP : (asymm P)) =>
        asymm_subs (P \ Q) P hassymP (
          difference_subset_prop P Q
        )
theorem antisymm_diff : ∀ P Q, (antisymm P) → (antisymm (P \ Q)) :=
  fun (P Q) =>
    fun (hantisymP : (antisymm P)) =>
      antisymm_subs (P \ Q) P hantisymP (
        difference_subset_prop P Q
      )


theorem compl_binon : ∀ A P, ((comp A A P) BinRelOn A) :=
  fun (A P) =>
    difference_subset_prop (A × A) P
theorem symm_compl : ∀ A P, (symm P) → (symm (comp A A P)) :=
  fun (A P) =>
    fun (hsymm : (symm P)) =>
      fun (x y) =>
        fun (hxy : (x . (comp A A P) . y)) =>
          let u := Iff.mp (difference_prop (A × A) P (x, y)) hxy
          Iff.mpr (difference_prop (A × A) P (y, x)) (
            And.intro (Iff.mpr (cartesian_product_pair_prop A A y x) (
              let v := Iff.mp (cartesian_product_pair_prop A A x y) (And.left u)
              And.intro (And.right v) (And.left v)
            )) (
              fun (hxyP : (y . P . x)) =>
                let t := hsymm y x hxyP
                And.right u (t)
            )
          )


def is_strict_partial_order (R A : Set) := (R BinRelOn A) ∧ irrefl R ∧ transit R
syntax term "SPO" term : term
macro_rules
| `($R:term SPO $A:term) => `(is_strict_partial_order $R $A)
def is_nonstrict_partial_order (R A : Set) := (R BinRelOn A) ∧ refl R A ∧ antisymm R ∧ transit R
syntax term "NSPO" term : term
macro_rules
| `($R:term NSPO $A:term) => `(is_nonstrict_partial_order $R $A)
noncomputable def str (A R) := R \ (id_ A)
noncomputable def nonstr (A R) := R ∪ (id_ A)
noncomputable def SPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R SPO A) }
noncomputable def NSPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R NSPO A) }
def is_partial_order (A R₁ R₂ : Set) : Prop := A ≠ ∅ ∧ (R₁ SPO A) ∧ (R₂ = nonstr A R₁)
syntax term "with" term "PO" term  : term
macro_rules
| `($R₁:term with $R₂:term PO $A:term) => `(is_partial_order $A $R₁ $R₂)
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


theorem spo_antisymm : ∀ A R, (R SPO A) → antisymm R :=
  fun (A R) =>
    fun (hAR : (R SPO A)) =>
      trans_irrefl_antisymm A R (And.left hAR) (And.right (And.right hAR)) (And.left (And.right hAR))
theorem spo_asymm : ∀ A R, (R SPO A) → asymm R :=
  fun (A R) =>
    fun (hAR : (R SPO A)) =>
      Iff.mpr (assym_iff_antisymm_irrefl A R (And.left hAR)) (
        And.intro (spo_antisymm A R hAR) (And.left (And.right hAR))
      )
theorem spo_then_nspo : ∀ A R, (R SPO A) → ((nonstr A R) NSPO A) :=
  fun (A R) =>
    fun (hAR : (R SPO A)) =>
      And.intro (un_binon A R (id_ A) (And.left hAR) (id_is_binon A)) (
        And.intro (refl_un_right A R (id_ A) (prop_then_id A)) (
          And.intro (
            fun (x y) =>
              fun (hxy : (x . (R ∪ (id_ A)) . y) ∧ (y . (R ∪ (id_ A)) . x)) =>
                  Or.elim (Iff.mp (union2sets_prop R (id_ A) (x, y)) (And.left hxy))
                  (
                    fun (hxyR : (x . R . y)) =>
                      Or.elim (Iff.mp (union2sets_prop R (id_ A) (y, x)) (And.right hxy))
                      (
                          fun (hyxR : (y . R . x)) =>
                            spo_antisymm A R (hAR) x y (And.intro (hxyR) (hyxR))
                      )
                      (
                        fun (hyxid : (y . (id_ A) . x)) =>
                          Eq.symm (And.left (And.left (id_prop A y x hyxid)))
                      )
                  )
                  (
                    fun (hyxid : (x  . (id_ A) . y)) =>
                     And.left ( And.left (id_prop A x y hyxid))
                  )
          ) (
            fun (x y z) =>
              fun (hxyz : (x . (R ∪ (id_ A)) . y) ∧ (y . (R ∪ (id_ A)) . z)) =>
                Or.elim (Iff.mp (union2sets_prop R (id_ A) (x, y)) (And.left hxyz))
                (
                  fun (xhyR : (x . R . y)) =>
                    Or.elim (Iff.mp (union2sets_prop R (id_ A) (y, z)) (And.right hxyz))
                    (
                      fun (hyzR : (y . R . z)) =>
                        let u := And.right (And.right hAR) x y z (And.intro xhyR hyzR)
                        Iff.mpr (union2sets_prop R (id_ A) (x, z)) (Or.inl u)
                    )
                    (
                      fun (hyzid : (y . (id_ A) . z)) =>
                        eq_subst (fun (t) => (x . (R ∪ (id_ A)) . t)) y z (
                          And.left (And.left (id_prop A y z hyzid))
                        ) (And.left hxyz)
                    )
                )
                (
                  fun (hyxid : (x  . (id_ A) . y)) =>
                    eq_subst (fun (t) => (t . (R ∪ (id_ A)) . z)) y x (
                      Eq.symm (And.left (And.left (id_prop A x y hyxid)))
                      ) (And.right hxyz)
                )
          )
          )
      )
theorem nspo_then_spo : ∀ A R, (R NSPO A) → ((str A R) SPO A) :=
  fun (A R) =>
    fun (hAR : (R NSPO A)) =>
      And.intro (diff_binon A R (id_ A) (And.left hAR)) (
        let irreflRdiffid := fun (x) =>
            fun (hx : (x . (R \ (id_ A)) . x)) =>
              let u := Iff.mp (difference_prop R (id_ A) (x, x)) hx
              Or.elim (em (x ∈ A))
              (
                fun (hxA : x ∈ A) =>
                  (And.right u) (prop_then_id A x hxA)
              )
              (
                fun (hxA : x ∉ A) =>
                  hxA (And.left (Iff.mp (cartesian_product_pair_prop A A x x)
                  (And.left hAR (x, x) (And.left u))))
              )
        And.intro (
          irreflRdiffid
        ) (
          fun (x y z) =>
            fun (hxyz : (x . (R \ (id_ A)) . y) ∧ (y . (R \ (id_ A)) . z)) =>
              let u := Iff.mp (difference_prop R (id_ A) (x, y)) (And.left hxyz)
              let v := Iff.mp (difference_prop R (id_ A) (y, z)) (And.right hxyz)
              Iff.mpr (difference_prop R (id_ A) (x, z)) (
                let xzR := And.right (And.right (And.right hAR)) x y z (
                    And.intro (And.left u) (And.left v)
                  )
                And.intro (
                  xzR
                ) (
                  fun (xzida : (x . (id_ A) . z)) =>
                    let first := eq_subst (fun (t) => (y . R . t)) z x (Eq.symm (And.left (And.left (id_prop A x z xzida)))) (
                      And.left v)
                    let second := And.left (And.right (And.right hAR)) x y (And.intro (And.left u) (first))
                    And.right u (
                      let third := And.left (Iff.mp (cartesian_product_pair_prop A A x y) (
                        And.left hAR (x, y) (And.left u)
                      ))
                      eq_subst (fun (t) => (x . (id_ A) . t)) x y (second) (prop_then_id A x third)
                    )
                )
              )
        )
      )
theorem str_nonstr_id : ∀ A R, (R SPO A) → ((str A (nonstr A R)) = R) :=
  fun (A R) =>
    fun (hRA : (R SPO A)) =>
      extensionality ((R ∪ (id_ A)) \ (id_ A)) R (
        fun (pr) =>
          Iff.intro
          (
            fun (hpr : (pr ∈ (R ∪ (id_ A)) \ (id_ A))) =>
              let u := Iff.mp (difference_prop (R ∪ (id_ A)) (id_ A) pr) hpr
              Or.elim (Iff.mp (union2sets_prop R (id_ A) pr) (And.left u))
              (
                fun (hprR : pr ∈ R) =>
                  hprR
              )
              (
                fun (hpid : pr ∈ (id_ A)) =>
                  False.elim (
                    And.right u (hpid)
                  )
              )
          )
          (
            fun (hpr : (pr ∈ R)) =>
              Iff.mpr (difference_prop (R ∪ (id_ A)) (id_ A) pr) (
                And.intro (Iff.mpr (union2sets_prop R (id_ A) pr) (Or.inl hpr)) (
                  fun (hprida : pr ∈ (id_ A)) =>
                    let v := And.left hRA pr hpr
                    let v₂ := Iff.mp (cartesian_product_is_cartesian A A pr) v
                    Exists.elim v₂
                    (
                      fun (x) =>
                        fun (hx : x ∈ A ∧ ∃ y ∈ A; pr = (x, y)) =>
                          Exists.elim (And.right hx) (
                            fun (y) =>
                              fun (hy : y ∈ A ∧ pr = (x, y)) =>
                                let v₃ := eq_subst (fun (t) => t ∈ (id_ A)) pr (x, y) (And.right hy) (hprida)
                                And.left (And.right hRA) x (
                                  eq_subst (fun (t) => t ∈ R) pr (x, x) (
                                    Eq.trans (And.right hy) (
                                      Iff.mpr (ordered_pair_set_prop x y x x) (
                                        And.intro (Eq.refl x) (Eq.symm (
                                          And.left (And.left (id_prop A x y (v₃)))
                                        ))
                                      )
                                    )
                                  ) (hpr)
                                )
                          )

                    )

                )
              )
          )
      )
theorem nonstr_str_id : ∀ A R, (R NSPO A) → ((nonstr A (str A R)) = R) :=
  fun (A R) =>
    fun (hRA : (R NSPO A)) =>
      extensionality (nonstr A (str A R)) R (
        fun (pr) =>
          Iff.intro
          (
            fun (hpr : pr ∈ (nonstr A (str A R))) =>
              let u := Iff.mp (union2sets_prop (R \ (id_ A)) (id_ A) pr) hpr
              Or.elim u
              (
                fun (hprid : pr ∈ (R \ (id_ A))) =>
                  And.left (Iff.mp (difference_prop R (id_ A) pr) hprid)
              )
              (
                fun (hid : pr ∈ id_ A) =>
                  Iff.mp (refl_crit A R (And.left hRA)) (

                    And.left (And.right hRA)
                  ) pr hid
              )
          )
          (
            fun (hpr : pr ∈ R) =>
              Iff.mpr (union2sets_prop (R \ (id_ A)) (id_ A) pr) (
                Or.elim (em (pr ∈ (id_ A)))
                (
                  fun (hprida : pr ∈ (id_ A)) =>
                    Or.inr hprida
                )
                (
                  fun (hprnida : pr ∉ (id_ A)) =>
                    Or.inl (
                      Iff.mpr (difference_prop R (id_ A) pr) (
                        And.intro hpr hprnida
                      )
                    )
                )
              )
          )
      )
theorem SPOS_NSPOS_equinum : ∀ A, (SPOS A) ~ (NSPOS A) :=
  fun (A) =>
    let φ := lam_fun (SPOS A) (NSPOS A) (nonstr A)

    Exists.intro φ (

      Iff.mp (rev_criterion φ (SPOS A) (NSPOS A)) (

        let func_prop₁ := lam_then_fun_prop (nonstr A) (SPOS A) (NSPOS A) (
          fun (R) =>
            fun (hR : R ∈ (SPOS A)) =>
              Iff.mpr (spec_is_spec (fun (P) => (P NSPO A)) (𝒫 (A × A)) (nonstr A R)) (
                let spo_R :=Iff.mp (spec_is_spec (fun (P) => (P SPO A)) (𝒫 (A × A)) R) hR
                let nspo_Rdiffid := spo_then_nspo A R (And.right spo_R)
                And.intro (Iff.mpr (boolean_set_is_boolean (A × A) (nonstr A R)) (
                  And.left nspo_Rdiffid
                )) (nspo_Rdiffid)
              )
        )
        And.intro (
          And.left (func_prop₁)


        ) (

          let ψ := lam_fun (NSPOS A) (SPOS A) (str A)




          Exists.intro ψ (

            let func_prop₂ := lam_then_fun_prop (str A) (NSPOS A) (SPOS A) (
              fun (R) =>
                fun (hR : R ∈ (NSPOS A)) =>
                  Iff.mpr (spec_is_spec (fun (P) => (P SPO A)) (𝒫 (A × A)) (str A R)) (
                    let nspo_R := Iff.mp (spec_is_spec (fun (P) => (P NSPO A)) (𝒫 (A × A)) R) hR
                    let spo_Rdunid := nspo_then_spo A R (And.right nspo_R)
                    And.intro (Iff.mpr (boolean_set_is_boolean (A × A) (str A R)) (
                      And.left spo_Rdunid
                    )) (spo_Rdunid)
                  )
              )


            And.intro (And.left func_prop₂) (
              And.intro (

                let u := function_composition_A φ ψ (SPOS (A)) (NSPOS (A)) (SPOS (A)) (And.left func_prop₁) (
                  And.left func_prop₂)

                let v := And.left (id_is_bij (SPOS A))


                Iff.mpr (equal_functions_abc_A (ψ ∘ φ) (id_ (SPOS A)) (SPOS A) (SPOS A) (SPOS A) (
                  And.left u
                ) (v)) (
                  fun (x) =>
                    fun (hx : x ∈ (SPOS A)) =>
                      let spo_x := And.right (Iff.mp (spec_is_spec (fun (R) => R SPO A)
                      (𝒫 (A × A)) x) (hx))

                      let nspo_x := spo_then_nspo A x (
                          spo_x
                      )
                      let frst := And.right u x hx
                      Eq.trans (frst) (

                        let u₂ := And.right func_prop₁ x hx
                        let u₃ := eq_subst (fun (t) => ψ⦅t⦆ = ψ⦅nonstr A x⦆) (nonstr A x) (φ⦅x⦆) (Eq.symm (u₂)) (
                          Eq.refl (ψ⦅nonstr A x⦆))

                        Eq.trans (u₃) (
                          let u₄ := And.right func_prop₂ (nonstr A x) (
                            Iff.mpr (
                            spec_is_spec (fun (R) => R NSPO A) (𝒫 (A × A)) (nonstr A x)) (
                              And.intro (
                                Iff.mpr (boolean_set_is_boolean (A × A) (nonstr A x)) (
                                  And.left nspo_x
                                )

                              ) (nspo_x)
                            )
                          )
                          Eq.trans (u₄) (

                            let u₅ := str_nonstr_id A x (spo_x)

                            Eq.trans (u₅) (

                              Iff.mp (function_equal_value_prop (id_ (SPOS A)) (SPOS A) (SPOS A) v x x hx) (
                                prop_then_id (SPOS A) x hx
                              )
                            )
                          )
                        )
                      )

                )



              ) (

                let u := function_composition_A ψ φ (NSPOS (A)) (SPOS (A)) (NSPOS (A)) (And.left func_prop₂) (
                  And.left func_prop₁)

                let v := And.left (id_is_bij (NSPOS A))

                Iff.mpr (equal_functions_abc_A (φ ∘ ψ) (id_ (NSPOS A)) (NSPOS A) (NSPOS A) (NSPOS A) (
                  And.left u
                ) (v)) (
                  fun (x) =>
                    fun (hx : x ∈ (NSPOS A)) =>
                      let nspo_x := And.right (Iff.mp (spec_is_spec (fun (R) => R NSPO A)
                      (𝒫 (A × A)) x) (hx))

                      let spo_x := nspo_then_spo A x (
                          nspo_x
                      )

                      let frst := And.right u x hx
                      Eq.trans (frst) (


                        let u₂ := And.right func_prop₂ x hx
                        let u₃ := eq_subst (fun (t) => φ⦅t⦆ = φ⦅str A x⦆) (str A x) (ψ⦅x⦆) (Eq.symm u₂) (
                          Eq.refl (φ⦅str A x⦆))

                        Eq.trans (u₃) (
                          let u₄ := And.right func_prop₁ (str A x) (
                            Iff.mpr (
                            spec_is_spec (fun (R) => R SPO A) (𝒫 (A × A)) (str A x)) (
                              And.intro (
                                Iff.mpr (boolean_set_is_boolean (A × A) (str A x)) (
                                  And.left spo_x
                                )

                              ) (spo_x)
                            )
                          )

                          Eq.trans (u₄) (

                            let u₅ := nonstr_str_id A x (nspo_x)

                            Eq.trans (u₅) (
                              Iff.mp (function_equal_value_prop (id_ (NSPOS A)) (NSPOS A) (NSPOS A) v x x hx) (
                                prop_then_id (NSPOS A) x hx
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
    )



theorem part_ord_nspo_crit : ∀ A R₁ R₂, (R₁ with R₂ PO A) ↔ ((A ≠ ∅) ∧ (R₂ NSPO A) ∧ (R₁ = str A R₂)) :=
  fun (A R₁ R₂) =>
    Iff.intro
    (
      fun (hpo : (R₁ with R₂ PO A)) =>
        let hpo₁ := And.right hpo
        And.intro (And.left hpo) (
        And.intro (
          eq_subst (fun (t) => t NSPO A) (nonstr A R₁) R₂ (Eq.symm (And.right hpo₁)) (
            spo_then_nspo A R₁ (And.left hpo₁)
          )

        ) (

          Eq.symm (
            eq_subst (fun (t) => str A t = R₁) (nonstr A R₁) (R₂) (Eq.symm (And.right hpo₁)) (
              str_nonstr_id A R₁ (And.left hpo₁)
            )
          )
        )
        )
    )
    (
      fun (hpo : ((A ≠ ∅) ∧ (R₂ NSPO A) ∧ (R₁ = str A R₂))) =>
        And.intro (And.left hpo) (
          let hpo₁ := And.right hpo
          And.intro (
            eq_subst (fun (t) => t SPO A) (str A R₂) R₁ (Eq.symm (And.right hpo₁)) (nspo_then_spo A R₂ (And.left hpo₁))
          ) (
            Eq.symm (
              eq_subst (fun (t) => nonstr A t = R₂) (str A R₂) (R₁) (Eq.symm (And.right hpo₁)) (nonstr_str_id A R₂ (
                And.left hpo₁))
            )
          )
        )
    )
theorem part_ord_crit : ∀ A R₁ R₂, (R₁ with R₂ PO A) ↔ ((A ≠ ∅) ∧ (R₁ SPO A) ∧ (R₂ NSPO A) ∧ (R₂ = nonstr A R₁) ∧ (R₁ = str A R₂)) :=
  fun (A R₁ R₂) =>
    Iff.intro
    (
      fun (hpo : (R₁ with R₂ PO A)) =>
        let hpo₁ := And.right hpo
        let hpo₂ := Iff.mp (part_ord_nspo_crit A R₁ R₂) hpo
        let hpo₃ := And.right hpo₂
        And.intro (And.left hpo) (And.intro (And.left hpo₁) (And.intro (And.left hpo₃) (And.intro (And.right hpo₁) (
          And.right hpo₃))))
    )
    (
      fun (hpo : (A ≠ ∅) ∧ (R₁ SPO A) ∧ (R₂ NSPO A) ∧ (R₂ = nonstr A R₁) ∧ (R₁ = str A R₂)) =>
        let hpo₁ := And.right hpo
        And.intro (And.left hpo) (And.intro (And.left hpo₁) (And.left (And.right (And.right hpo₁))))
    )


theorem triple_po_is_po : ∀ 𝓐, (PartOrd 𝓐) → (is_partial_order setPO(𝓐) ≺(𝓐) ≼(𝓐)) :=
  fun (𝓐) =>
    fun (PO𝓐 : (PartOrd 𝓐)) =>
      Exists.elim PO𝓐 (
        fun (A) =>
          fun (hA) =>
            Exists.elim hA (
              fun (R₁) =>
                fun (hR₁) =>
                  Exists.elim hR₁ (
                    fun (R₂) =>
                      fun (hR₂ : 𝓐 = ⁅A; R₁; R₂⁆ ∧ (is_partial_order A R₁ R₂)) =>
                        let u := setPO(𝓐)
                        let u₁ := eq_subst (fun (t) => setPO(𝓐) = setPO(t)) 𝓐 (⁅A; R₁; R₂⁆) (And.left hR₂) (Eq.refl u)
                        let u₂ := coordinates_fst_coor (A, R₁) R₂
                        let u₃ := coordinates_fst_coor A R₁
                        let u₄ := eq_subst (fun (t) => fst_coor (t) = A) (A, R₁) (fst_coor ((A, R₁), R₂)) (Eq.symm (u₂)) (u₃)
                        let u₅ := Eq.trans u₁ u₄
                        let u₆ := ≺(𝓐)
                        let u₇ := eq_subst (fun (t) => ≺(𝓐) = ≺(t)) 𝓐 (⁅A; R₁; R₂⁆) (And.left hR₂) (Eq.refl u₆)
                        let u₈ := coordinates_snd_coor A R₁
                        let u₉ := eq_subst (fun (t) => snd_coor (t) = R₁) (A, R₁) (fst_coor ((A, R₁), R₂)) (Eq.symm (u₂)) (u₈)
                        let u₁₀ := Eq.trans u₇ u₉
                        let u₁₁ := eq_subst (fun (t) => ≼(𝓐) = ≼(t)) 𝓐 (⁅A; R₁; R₂⁆) (And.left hR₂) (Eq.refl (≼(𝓐)))
                        let u₁₂ := coordinates_snd_coor (A, R₁) R₂
                        let u₁₃ := Eq.trans u₁₁ u₁₂

                        eq_subst (fun (t) => is_partial_order t (≺(𝓐)) (≼(𝓐))) A (setPO(𝓐)) (Eq.symm u₅) (
                          eq_subst (fun (t₂) => is_partial_order A (t₂) (≼(𝓐))) (R₁) (≺(𝓐)) (Eq.symm u₁₀) (
                            eq_subst (fun (t₃) => is_partial_order A R₁ t₃) (R₂) (≼(𝓐)) (Eq.symm u₁₃) (
                              And.right hR₂
                            )
                          )
                        )
                  )
            )
      )
theorem setPO_is_setPO : ∀ A R₁ R₂, (setPO(⁅A; R₁; R₂⁆) = A) :=
  fun (A R₁ R₂) =>
    let u₂ := coordinates_fst_coor (A, R₁) R₂
    let u₃ := coordinates_fst_coor A R₁
    eq_subst (fun (t) => fst_coor (t) = A) (A, R₁) (fst_coor ((A, R₁), R₂)) (Eq.symm (u₂)) (u₃)
theorem lessPO_is_lessPO :  ∀ A R₁ R₂, (≺(⁅A; R₁; R₂⁆) = R₁) :=
  fun (A R₁ R₂) =>
    let u₂ := coordinates_fst_coor (A, R₁) R₂
    let u₈ := coordinates_snd_coor A R₁
    eq_subst (fun (t) => snd_coor (t) = R₁) (A, R₁) (fst_coor ((A, R₁), R₂)) (Eq.symm (u₂)) (u₈)
theorem lesseqPO_is_lesseqPO : ∀ A R₁ R₂, (≼(⁅A; R₁; R₂⁆) = R₂) :=
  fun (A R₁ R₂) =>
    coordinates_snd_coor (A, R₁) R₂
theorem po_is_triple_po : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (PartOrd (⁅A; R₁; R₂⁆)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      Exists.intro A (Exists.intro R₁ (Exists.intro R₂ (And.intro (Eq.refl (⁅A; R₁; R₂⁆)) (hR))))
theorem po_less_more : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≺(𝓐)) . y) ↔ (y . ≻(𝓐) . x) :=
  fun (𝓐) =>
    fun (h𝓐 : PartOrd 𝓐) =>
      fun (x) =>
        fun (y) =>
          let u := And.left (And.left (And.right (triple_po_is_po 𝓐 h𝓐)))
          let u₁ := bin_on_is_bin (setPO(𝓐)) (≺(𝓐)) u
          inv_pair_prop (≺(𝓐)) u₁ x y
theorem po_lesseq_moreeq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . (≼(𝓐)) . y) ↔ (y . ≽(𝓐) . x) :=
  fun (𝓐) =>
    fun (h𝓐 : PartOrd 𝓐) =>
      fun (x) =>
        fun (y) =>
          let u := And.left (And.left (And.right (Iff.mp (part_ord_nspo_crit (setPO(𝓐)) (≺(𝓐)) (≼(𝓐))) (triple_po_is_po 𝓐 h𝓐))))
          let u₁ := bin_on_is_bin (setPO(𝓐)) (≼(𝓐)) u
          inv_pair_prop (≼(𝓐)) u₁ x y

theorem part_ord_pair_prop : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y ∈ (setPO(𝓐)); ((x . (≺(𝓐)) . y) ↔ ((x . ≼(𝓐) . y) ∧ x ≠ y)) ∧ ((x . (≼(𝓐)) . y) ↔ ((x . (≺(𝓐)) . y) ∨ x = y))) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let R₂ := (≼(𝓐))
      let hRA := triple_po_is_po 𝓐 h𝓐
      fun (x) => fun (hx : x ∈ A) => fun (y) => fun (_ : y ∈ A) =>
        let proof₁ := Iff.intro
          (
            fun (hxy : (x . R₁ . y)) =>
              let m := Iff.mp (cartesian_product_pair_prop A A x y) (And.left (And.left (And.right hRA)) (x, y) hxy)
              let u := And.right ( And.right ( And.right (And.right (Iff.mp (part_ord_crit A R₁ R₂) hRA))))
              let v := eq_subst (fun (t) => (x . t . y)) (R₁) (str A R₂) u (hxy)
              let s := Iff.mp (difference_prop R₂ (id_ A) (x, y)) v
              And.intro (And.left s) (
                fun (hxyeq : x = y) =>
                  And.right s (
                    eq_subst (fun (t) => (x . (id_ A) . t)) x y (hxyeq) (prop_then_id A x (And.left m))
                  )

              )
          )
          (
            fun (hxy : (x . R₂ . y) ∧ (x ≠ y)) =>
              let u := Iff.mpr (difference_prop R₂ (id_ A) (x, y)) (
                And.intro (And.left hxy) (
                  fun (hxyeq : (x . (id_ A) . y)) =>
                    And.right hxy (
                      And.left (And.left (id_prop A x y hxyeq))
                    )
                )
              )

              eq_subst (fun (t) => (x . t . y)) (R₂ \ (id_ A)) R₁ (Eq.symm (
                And.right ( And.right ( And.right (And.right (Iff.mp (part_ord_crit A R₁ R₂) hRA))))
              )) u
          )
        And.intro (
          proof₁


        ) (
          Iff.intro
          (
            fun (hxy : (x . R₂ . y)) =>
              Or.elim (em (x = y))
              (
                fun (hxyeq : x = y) =>
                  Or.inr hxyeq
              )
              (
                fun (hxyneq : x ≠ y) =>
                  Or.inl (Iff.mpr proof₁ (And.intro hxy (hxyneq)))
              )
          )
          (
            fun (hxy : (x . R₁ . y) ∨ (x = y)) =>
              Or.elim hxy
              (
                fun (xhyR : (x . R₁ . y)) =>
                  And.left (Iff.mp proof₁ (xhyR))
              )
              (
                fun (hxyeq : (x = y)) =>
                  let u := And.right ((And.right hRA))
                  eq_subst (fun (t) => (x . t . y)) (nonstr A R₁) (R₂) (Eq.symm u) (
                    Iff.mpr (union2sets_prop (R₁) (id_ A) (x, y)) (
                      Or.inr (
                        eq_subst (fun (t) => (x . (id_ A) . t)) x y (hxyeq) (
                          prop_then_id A x hx
                        )
                      )
                    )
                  )
              )
          )
        )
theorem par_ord_pair_prop_R₁_A : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≺(𝓐)) . y) → ((x ∈ (setPO(𝓐))) ∧ (y ∈ (setPO(𝓐))))) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      fun (x y) =>
        fun (hxy : (x . R₁ . y)) =>
          let u := And.left (And.left (And.right hR)) (x, y) hxy
          Iff.mp (cartesian_product_pair_prop A A x y) u
theorem par_ord_pair_prop_R₂_A : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≼(𝓐)) . y) → ((x ∈ (setPO(𝓐))) ∧ (y ∈ (setPO(𝓐))))) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let R₂ := (≼(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      fun (x y) =>
        fun (hxy : (x . R₂ . y)) =>
          let u := And.left (And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR))) (x, y) hxy
          Iff.mp (cartesian_product_pair_prop A A x y) u
theorem part_ord_pair_prop_R₁R₂ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, (x . ≺(𝓐) . y) → (x . (≼(𝓐)) . y) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      fun (x y) =>
        fun (hxy : (x . R₁ . y)) =>
          let u₁ := And.left (And.left (And.right hR)) (x, y) hxy
          let u₂ := Iff.mp (cartesian_product_pair_prop A A x y) u₁
          And.left (Iff.mp (And.left (part_ord_pair_prop 𝓐 h𝓐 x (And.left u₂) y (And.right u₂))) hxy)
theorem part_ord_pair_prop_R₁neq : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y ∈ (setPO(𝓐)); (x . ≺(𝓐) . y) → (x ≠ y) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      fun (x) => fun (hx : x ∈ A) =>
        fun (y) => fun (hy : y ∈ A) =>
          fun (hxy : (x . R₁ . y)) =>
              And.right (Iff.mp (And.left (part_ord_pair_prop 𝓐 h𝓐 x hx y hy)) hxy)
theorem part_ord_pair_prop_eqR₂ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y ∈ (setPO(𝓐)); (x = y) → (x . (≼(𝓐)) . y) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      fun (x) => fun (hx : x ∈ A) =>
        fun (y) => fun (hy : y ∈ A) =>
          fun (hxy : (x = y)) =>
            Iff.mpr (And.right (part_ord_pair_prop 𝓐 h𝓐 x hx y hy)) (
              Or.inr hxy
            )
theorem part_ord_pair_prop_neqR₂R₁ : ∀ 𝓐, (PartOrd 𝓐) → ∀ x y, ((x . (≼(𝓐)) . y) ∧ (x ≠ y)) → (x . (≺(𝓐)) . y) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let R₂ := (≼(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      fun (x y) =>
        fun (hxyR₂ : (x . R₂ . y) ∧ (x ≠ y)) =>
          let u₁ := And.left (And.left (And.right (And.right (Iff.mp (part_ord_crit A R₁ R₂) hR)))) (x, y) (And.left hxyR₂)
          let u₂ := Iff.mp (cartesian_product_pair_prop A A x y) u₁
          Iff.mpr (And.left (part_ord_pair_prop 𝓐 h𝓐 x (And.left u₂) y (And.right u₂))) hxyR₂


theorem binA_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (≺(𝓐)) BinRelOn (setPO(𝓐)) :=
    fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      And.left (And.left (And.right (triple_po_is_po 𝓐 h𝓐)))
theorem bin_R₁ : ∀ 𝓐, (PartOrd 𝓐) → BinRel (≺(𝓐)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      bin_on_is_bin (setPO(𝓐)) (≺(𝓐)) (
        binA_R₁ 𝓐 h𝓐
      )
theorem irrefl_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x, ¬ (x . (≺(𝓐)) . x)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let hR := triple_po_is_po 𝓐 h𝓐
      And.left (And.right (And.left (And.right hR)))
theorem asymm_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≺(𝓐)) . y) → ¬ (y . (≺(𝓐)) . x)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      let u := And.left (And.right hR)
      spo_asymm A R₁ u
theorem trans_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≺(𝓐)) . y) → (y . (≺(𝓐)) . z) → (x . (≺(𝓐)) . z)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let R₁ := (≺(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      let u := And.left (And.right hR)
      let v := And.right (And.right u)
      fun (x y z) =>
        fun (hxy : (x . R₁ . y)) =>
          fun (hyz : (y . R₁ . z)) =>
            v x y z (And.intro hxy hyz)


theorem binA_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (≼(𝓐)) BinRelOn (setPO(𝓐)) :=
    fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let u := Iff.mp (part_ord_nspo_crit (setPO(𝓐)) (≺(𝓐)) (≼(𝓐))) (
        triple_po_is_po 𝓐 h𝓐
      )
      And.left (And.left (And.right u))
theorem bin_R₂ : ∀ 𝓐, (PartOrd 𝓐) → BinRel (≼(𝓐)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      bin_on_is_bin (setPO(𝓐)) (≼(𝓐)) (
        binA_R₂ 𝓐 h𝓐
      )
theorem refl_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x ∈ (setPO(𝓐)); (x . (≼(𝓐)) . x)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let R₂ := (≼(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      And.left (And.right (And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR))))
theorem antisymm_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . x) → (x = y)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let R₂ := (≼(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      let u := And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR))
      let v := And.left (And.right (And.right u))
      fun (x y) =>
        fun (hxyR₂ : (x . R₂ . y)) =>
          fun (hyxR₂ : (y . R₂ . x)) =>
            v x y (And.intro (hxyR₂) (hyxR₂))
theorem trans_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x . (≼(𝓐)) . z)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let A := (setPO(𝓐))
      let R₁ := (≺(𝓐))
      let R₂ := (≼(𝓐))
      let hR := triple_po_is_po 𝓐 h𝓐
      let u := And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR))
      let v := And.right (And.right (And.right u))
      fun (x y z) =>
        fun (hxyR₂ : (x . R₂ . y)) =>
          fun (hyzR₂ : (y . R₂ . z)) =>
            v x y z (And.intro hxyR₂ hyzR₂)
theorem stabil_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x = z) → ((x = y) ∧ (y = z))) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let R₁ := (≺(𝓐))
      let R₂ := (≼(𝓐))
      fun (x y z) =>
        fun (hxy : (x . R₂ . y)) =>
          fun (hyz : (y . R₂ . z)) =>
            fun (hxz : (x = z)) =>
              Or.elim (em (x = y))
              (
                fun (hxyeq : x = y) =>
                  Or.elim (em (y = z))
                  (
                    fun (hyzeq : y = z) =>
                      And.intro (hxyeq) (hyzeq)
                  )
                  (
                    fun (_ : y ≠ z) =>
                      And.intro (hxyeq) (
                        byContradiction (
                          fun (hyzneq₂ : y ≠ z) =>
                            let u := part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 y z (And.intro (hyz) (hyzneq₂))
                            let v := eq_subst (fun (t) => (t, z) ∈ R₁) y x (Eq.symm hxyeq) (u)
                            let m := par_ord_pair_prop_R₁_A 𝓐 h𝓐 x z v
                            let t := part_ord_pair_prop_R₁neq 𝓐 h𝓐 x (And.left m) z (And.right m) v
                            t hxz
                        )
                      )
                  )
              )
              (
                fun (hxyneq : x ≠ y) =>
                  Or.elim (em (y = z))
                  (
                    fun (hyzeq : y = z) =>
                      And.intro (
                        byContradiction (
                          fun (hxyneq : x ≠ y) =>
                            let u := part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 x y (And.intro (hxy) (hxyneq))
                            let v := eq_subst (fun (t) => (x, t) ∈ R₁) y z (hyzeq) (u)
                            let t := eq_subst (fun (t) => (x, t) ∈ R₁) z x (Eq.symm (hxz)) (v)
                            irrefl_R₁ 𝓐 h𝓐 x t

                        )
                      ) (hyzeq)
                  )
                  (
                    fun (hnyzeq : y ≠ z) =>
                      let u := part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 y z (And.intro (hyz) (hnyzeq))
                      let v := part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 x y (And.intro (hxy) (hxyneq))
                      let s := trans_R₁ 𝓐 h𝓐 x y z v u
                      let t := eq_subst (fun (t) => (x, t) ∈ R₁) z x (Eq.symm (hxz)) (s)

                     False.elim ( irrefl_R₁ 𝓐 h𝓐 x t)
                  )
              )
theorem no_symm_R₁_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y, ¬ ((x . (≺(𝓐)) . y) ∧ (y . (≼(𝓐)) . x))) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let R₁ := (≺(𝓐))
      let R₂ := (≼(𝓐))
      fun (x y) =>
        fun (hxy : (x . R₁ . y) ∧ (y . R₂ . x)) =>
          let u := And.left hxy
          let v := part_ord_pair_prop_R₁R₂ 𝓐 h𝓐 x y u
          let t := antisymm_R₂ 𝓐 h𝓐 x y v (And.right hxy)
          irrefl_R₁ 𝓐 h𝓐 x (
            eq_subst (fun (t) => (x . R₁ . t)) y x (Eq.symm (t)) (u)
          )

theorem trans_R₁_R₂_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≺(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x . (≼(𝓐)) . z)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x y z) =>
        fun (hxy : (x . (≺(𝓐)) . y)) =>
          fun (hyz : (y . (≼(𝓐)) . z)) =>
            let u := part_ord_pair_prop_R₁R₂ 𝓐 h𝓐 x y hxy
            trans_R₂ 𝓐 h𝓐 x y z u hyz
theorem trans_R₁_R₂_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≺(𝓐)) . y) → (y . (≼(𝓐)) . z) → (x . (≺(𝓐)) . z)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x y z) =>
        fun (hxy : (x . (≺(𝓐)) . y)) =>
          fun (hyz : (y . (≼(𝓐)) . z)) =>
            let u := trans_R₁_R₂_R₂ 𝓐 h𝓐 x y z hxy hyz
            part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 x z (And.intro (u) (
              fun (hxz : (x = z)) =>
                let v := eq_subst (fun (t) => (t . (≺(𝓐)) . y)) x z hxz hxy
                no_symm_R₁_R₂ 𝓐 h𝓐 z y (And.intro (v) (hyz))
            ))
theorem trans_R₂_R₁_R₂ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≺(𝓐)) . z) → (x . (≼(𝓐)) . z)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x y z) =>
        fun (hxy : (x . (≼(𝓐)) . y)) =>
          fun (hyz : (y . (≺(𝓐)) . z)) =>
            let u := part_ord_pair_prop_R₁R₂ 𝓐 h𝓐 y z hyz
            trans_R₂ 𝓐 h𝓐 x y z (hxy) (u)
theorem trans_R₂_R₁_R₁ : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y z, (x . (≼(𝓐)) . y) → (y . (≺(𝓐)) . z) → (x . (≺(𝓐)) . z)) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x y z) =>
        fun (hxy : (x . (≼(𝓐)) . y)) =>
          fun (hyz : (y . (≺(𝓐)) . z)) =>
            let u := trans_R₂_R₁_R₂ 𝓐 h𝓐 x y z hxy hyz
            part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 x z (And.intro (u) (
              fun (hxz : (x = z)) =>
                let v := eq_subst (fun (t) => (y . (≺(𝓐)) . t)) z x (Eq.symm hxz) hxy
                no_symm_R₁_R₂ 𝓐 h𝓐 z y (And.intro (v) (hyz))
            ))

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
theorem sub_is_PO : ∀ 𝓐 B, (B ≠ ∅) → (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (PartOrd ⁅B; ≺(𝓐) ∩ (B × B); ≼(𝓐) ∩ (B × B)⁆) :=
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
theorem inter_is_PO_PO :∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (setPO(𝓐) = setPO(𝓑)) →
  (PartOrd ⁅setPO(𝓐); ≺(𝓐) ∩ ≺(𝓑); ≼(𝓐) ∩ ≼(𝓑)⁆) :=
    fun (𝓐 𝓑) =>
      fun (h𝓐 : (PartOrd 𝓐) ) =>
        fun (h𝓑 : (PartOrd 𝓑)) =>
          fun (eqse : (setPO(𝓐) = setPO(𝓑))) =>
            let A := setPO(𝓐)
            let B := setPO(𝓑)
            let P₁ := ≺(𝓐)
            let P₂ := ≼(𝓐)
            let Q₁ := ≺(𝓑)
            let Q₂ := ≼(𝓑)
            let hP := triple_po_is_po 𝓐 h𝓐
            let hQ := triple_po_is_po 𝓑 h𝓑
            po_is_triple_po A (P₁ ∩ Q₁) (P₂ ∩ Q₂) (
                let u := And.left (And.left (And.right hP))
                let vP := And.right (And.left (And.right hP))
                let sP := And.right (And.right hP)
                let sQ := And.right (And.right hQ)
                let vQ := And.right (And.left (And.right hQ))
                let reflP₂ := refl_R₂ 𝓐 h𝓐
                let first := And.left (And.left (And.right (Iff.mp (part_ord_nspo_crit A P₁ P₂) hP)))
                And.intro (And.left hP) (
                  And.intro (And.intro (int_binon_left A P₁ Q₁ (u)) (
                    And.intro (irrefl_int_left P₁ Q₁ (And.left vP)) (
                      trans_int P₁ Q₁ (And.right vP) (And.right vQ)
                    )
                  )) (
                    let u₁ := eq_subst (fun (t) => P₂ ∩ Q₂ = t ∩ Q₂) P₂ (nonstr A P₁) (sP) (Eq.refl (P₂ ∩ Q₂))
                    let u₂ := eq_subst (fun (t) => (nonstr A P₁) ∩ Q₂ = (nonstr A P₁) ∩ t) Q₂ (nonstr A Q₁) (
                      eq_subst (fun (t) => Q₂ = nonstr t Q₁) B A (Eq.symm (eqse)) (sQ)
                    ) (
                      Eq.refl ((nonstr A P₁) ∩ Q₂))
                    let u₃ := Eq.trans u₁ u₂


                    Eq.trans (u₃) (
                      let v₁ := inter_union_distribution (nonstr A P₁) (Q₁) (id_ A)

                      Eq.trans v₁ (


                        let s := Iff.mp (And.left (subset_using_equality (id_ A) (nonstr A P₁))) (
                          Iff.mp (refl_crit A (nonstr A P₁) (
                            eq_subst (fun (t) => t BinRelOn A) (P₂) (nonstr A P₁) (sP) (first)
                          )) (
                            eq_subst (fun (t) => refl t A) (P₂) (nonstr A P₁) (sP) (reflP₂)
                          )
                        )

                        let s₂ := Eq.symm (intersec2_comm (id_ A) (nonstr A P₁))

                        let s₃ := Eq.trans (s₂) (s)

                        let r := eq_subst (fun (t) => (nonstr A P₁ ∩ Q₁) ∪ (nonstr A P₁ ∩ (id_ A))
                        = (nonstr A P₁ ∩ Q₁) ∪ (t)) (nonstr A P₁ ∩ (id_ A)) (id_ A) (s₃) (
                          Eq.refl ((nonstr A P₁ ∩ Q₁) ∪ (nonstr A P₁ ∩ id_ A))
                        )

                        Eq.trans r (

                          -- (nonstr A P₁ ∩ Q₁) ∪ id_ A = nonstr A (P₁ ∩ Q₁)

                          eq_subst (fun (t) => t ∪ id_ A = nonstr A (P₁ ∩ Q₁)) (P₁ ∩ Q₁) (nonstr A P₁ ∩ Q₁) (
                            extensionality (P₁ ∩ Q₁) (nonstr A P₁ ∩ Q₁) (
                              fun (f) =>
                                Iff.intro
                                (
                                  fun (hf : f ∈ (P₁ ∩ Q₁)) =>
                                    let fprop := Iff.mp (intersect_2sets_prop P₁ Q₁ f) hf
                                    Iff.mpr (intersect_2sets_prop (nonstr A P₁) (Q₁) f) (
                                      And.intro (Iff.mpr (union2sets_prop P₁ (id_ A) f) (
                                        Or.inl (And.left fprop)
                                      )) (And.right fprop)
                                    )
                                )
                                (
                                  fun (hf : f ∈ ((nonstr A P₁) ∩ Q₁)) =>
                                    let fprop := Iff.mp (intersect_2sets_prop (nonstr A P₁) Q₁ f) hf
                                    Iff.mpr (intersect_2sets_prop (P₁) (Q₁) f) (
                                      And.intro (
                                        Or.elim (Iff.mp (union2sets_prop P₁ (id_ A) f) (And.left fprop))
                                        (
                                          fun (fpr₁ : f ∈ P₁) =>
                                            fpr₁
                                        )
                                        (
                                          fun (fpr₁ : f ∈ (id_ A)) =>
                                            False.elim (
                                              let Q_irr := irrefl_R₁ 𝓑 h𝓑
                                              let Q_bin := And.left (And.left (And.right hQ))
                                              let Q_irr_crit := Iff.mp (irrefl_crit A Q₁ (

                                                eq_subst (fun (t) => Q₁ BinRelOn t) B A (Eq.symm (eqse)) (Q_bin)
                                              )) (Q_irr)


                                              empty_set_is_empty f (

                                                eq_subst (fun (t) => f ∈ t) (Q₁ ∩ (id_ A)) (∅) (Q_irr_crit) (
                                                  Iff.mpr (intersect_2sets_prop Q₁ (id_ A) f) (
                                                    And.intro (And.right fprop) (fpr₁)
                                                  )
                                                )
                                              )
                                            )
                                        )


                                      ) (And.right fprop)
                                    )
                                )
                            )


                          ) (
                            Eq.refl (nonstr A (P₁ ∩ Q₁))
                          )

                        )
                      )
                    )
                  )
                )
      )

def noncomparable_nonstr (𝓐 x y : Set) : Prop := (¬ (x . (≼(𝓐)) . y)) ∧ (¬ (x . (≽(𝓐)) . y))
def noncomparable_str (𝓐 x y : Set) : Prop := (¬ (x . (≺(𝓐)) . y)) ∧ (¬ (x . (≻(𝓐)) . y))
theorem PO_noncomp : ∀ 𝓐, (PartOrd 𝓐) → (∀ x y ∈ (setPO(𝓐)); (noncomparable_nonstr 𝓐 x y) ↔ (x ≠ y ∧ (noncomparable_str 𝓐 x y))) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x) =>
        fun (hx : x ∈ (setPO(𝓐))) =>
          fun (y) =>
            fun (hy : y ∈ (setPO(𝓐))) =>
              let R₁ := (≺(𝓐))
              let R₂ := (≼(𝓐))
              Iff.intro
              (
                fun (hxy : (noncomparable_nonstr 𝓐 x y)) =>
                  And.intro (
                    fun (hxyeq : (x = y)) =>
                      And.left hxy (
                        part_ord_pair_prop_eqR₂ 𝓐 h𝓐 x hx y hy hxyeq
                      )
                  ) (And.intro (
                    fun (xhyR₁ : (x . R₁ . y)) =>
                      And.left hxy (
                        part_ord_pair_prop_R₁R₂ 𝓐 h𝓐 x y xhyR₁

                      )
                  ) (
                    fun (xhyR₁ : (x . ≻(𝓐) . y)) =>
                    (And.right hxy) (
                      let u := part_ord_pair_prop_R₁R₂ 𝓐 h𝓐 y x (
                        Iff.mpr (po_less_more 𝓐 h𝓐 y x) (xhyR₁)
                      )
                      Iff.mp (po_lesseq_moreeq 𝓐 h𝓐 y x) u
                      )
                  ))
              )
              (
                fun (hxy : (x ≠ y) ∧ (noncomparable_str 𝓐 x y)) =>
                  And.intro (

                    fun (hxyR₁ : (x . R₂ . y)) =>
                      And.left (And.right hxy) (
                        part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 x y (And.intro (hxyR₁) (And.left hxy))
                      )

                  ) (
                    fun (hxyR₂ : (x . (≽(𝓐)) . y)) =>
                      And.right (And.right hxy) (
                        let u := part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 y x (And.intro (

                          Iff.mpr (po_lesseq_moreeq 𝓐 h𝓐 y x) (hxyR₂)
                        ) (
                          fun (hyx : y = x) =>
                            And.left hxy (Eq.symm hyx)
                          ))
                        Iff.mp (po_less_more 𝓐 h𝓐 y x) (u)
                      )

                  )
              )



def is_maximal (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (x . (≺(𝓐)) . y))
def is_minimal (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (y . (≺(𝓐)) . x))
def is_maximum (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (y . (≼(𝓐)) . x))
def is_minimum (𝓐 B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (x . (≼(𝓐)) . y))
noncomputable def max_set (𝓐 B) := {z ∈ B | is_maximal 𝓐 B z }
noncomputable def min_set (𝓐 B) := {z ∈ B | is_minimal 𝓐 B z }


theorem max_set_is_max_set : ∀ 𝓐 B x, ((x ∈ max_set 𝓐 B) ↔ (is_maximal 𝓐 B x)) :=
  fun (𝓐 B x) =>
      Iff.intro
      (
        fun (hxmax : (x ∈ max_set 𝓐 B)) =>
          And.right (Iff.mp (spec_is_spec (fun (t) => is_maximal 𝓐 B t) B x) hxmax)

      )
      (
        fun (hxmax : (is_maximal 𝓐 B x)) =>
          Iff.mpr (spec_is_spec (fun (t) => is_maximal 𝓐 B t) B x) (
            And.intro (And.left hxmax) (hxmax)
          )

      )
theorem min_set_is_min_set : ∀ 𝓐 B x, ((x ∈ min_set 𝓐 B) ↔ (is_minimal 𝓐 B x)) :=
  fun (𝓐 B x) =>
      Iff.intro
      (
        fun (hxmin : (x ∈ min_set 𝓐 B)) =>
          And.right (Iff.mp (spec_is_spec (fun (t) => is_minimal 𝓐 B t) B x) hxmin)

      )
      (
        fun (hxmin : (is_minimal 𝓐 B x)) =>
          Iff.mpr (spec_is_spec (fun (t) => is_minimal 𝓐 B t) B x) (
            And.intro (And.left hxmin) (hxmin)
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
theorem min_max_inv_um :  ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_minimum 𝓐 B x) ↔ (is_maximum (invPO 𝓐) B x)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : ((PartOrd 𝓐))) =>
      Iff.intro
        (
          fun (hmin : (is_minimum 𝓐 B x)) =>
            And.intro (And.left hmin) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  let u := And.right hmin y hyB
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 y x) u


            )
        )
        (
          fun (hmax : (is_maximum (invPO 𝓐) B x)) =>
            And.intro (And.left hmax) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  let u := And.right hmax y hyB
                  Iff.mp (inv_PO_lesseq 𝓐 h𝓐 y x) u
            )

        )
theorem max_min_inv_um :  ∀ 𝓐 B x, (PartOrd 𝓐) → ((is_maximum 𝓐 B x) ↔ (is_minimum (invPO 𝓐) B x)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      Iff.intro
        (
          fun (hmax : (is_maximum 𝓐 B x)) =>
            And.intro (And.left hmax) (
              fun (y) =>
                fun (hyB : y ∈ B) =>
                  let u := And.right hmax y hyB
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 x y) u


            )
        )
        (
          fun (hmin : (is_minimum (invPO 𝓐) B x)) =>
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
theorem max_al_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) → (∃ i ∈ I; is_maximal 𝓐 (B _ i) x) → (is_maximal 𝓐 (⋂[ i in I ] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (B IndxFun I)) =>
      fun (hx : (x ∈ (⋂[ i in I ] B at i))) =>
        fun (hexii : ∃ i ∈ I; is_maximal 𝓐 (B _ i) x) =>
          And.intro (hx) (
            fun (y) =>
              fun (hy : y ∈ (⋂[ i in I ] B at i)) =>
                Exists.elim hexii (
                  fun (i) =>
                    fun (hi : i ∈ I ∧ is_maximal 𝓐 (B _ i) x) =>
                      And.right (And.right hi) y (

                        let u := fun (hIemp : I = ∅) =>
                          empty_set_is_empty i (
                            eq_subst (fun (t) => i ∈ t) I ∅ hIemp (And.left hi)
                          )
                        Iff.mp (indexed_intersection_is_intersection B I u hI y) hy i (And.left hi)
                      )
                )
          )
theorem min_al_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) → (∃ i ∈ I; is_minimal 𝓐 (B _ i) x) → (is_minimal 𝓐 (⋂[ i in I ] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (B IndxFun I)) =>
      fun (hx : (x ∈ (⋂[ i in I ] B at i))) =>
        fun (hexii : ∃ i ∈ I; is_minimal 𝓐 (B _ i) x) =>
          And.intro (hx) (
            fun (y) =>
              fun (hy : y ∈ (⋂[ i in I ] B at i)) =>
                Exists.elim hexii (
                  fun (i) =>
                    fun (hi : i ∈ I ∧ is_minimal 𝓐 (B _ i) x) =>
                      And.right (And.right hi) y (

                        let u := fun (hIemp : I = ∅) =>
                          empty_set_is_empty i (
                            eq_subst (fun (t) => i ∈ t) I ∅ hIemp (And.left hi)
                          )
                        Iff.mp (indexed_intersection_is_intersection B I u hI y) hy i (And.left hi)
                      )
                )
          )
theorem max_um_inter_prop :∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) → (∃ i ∈ I; is_maximum 𝓐 (B _ i) x) → (is_maximum 𝓐 (⋂[ i in I ] B at i) x) :=
   fun (𝓐 B I x) =>
    fun (hI : (B IndxFun I)) =>
      fun (hx : (x ∈ (⋂[ i in I ] B at i))) =>
        fun (hexii : ∃ i ∈ I; is_maximum 𝓐 (B _ i) x) =>
          And.intro (hx) (
            fun (y) =>
              fun (hy : y ∈ (⋂[ i in I ] B at i)) =>
                Exists.elim hexii (
                  fun (i) =>
                    fun (hi : i ∈ I ∧ is_maximum 𝓐 (B _ i) x) =>
                      And.right (And.right hi) y (

                        let u := fun (hIemp : I = ∅) =>
                          empty_set_is_empty i (
                            eq_subst (fun (t) => i ∈ t) I ∅ hIemp (And.left hi)
                          )
                        Iff.mp (indexed_intersection_is_intersection B I u hI y) hy i (And.left hi)
                      )
                )
          )
theorem min_um_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (x ∈ (⋂[ i in I ] B at i)) → (∃ i ∈ I; is_minimum 𝓐 (B _ i) x) → (is_minimum 𝓐 (⋂[ i in I ] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (B IndxFun I)) =>
      fun (hx : (x ∈ (⋂[ i in I ] B at i))) =>
        fun (hexii : ∃ i ∈ I; is_minimum 𝓐 (B _ i) x) =>
          And.intro (hx) (
            fun (y) =>
              fun (hy : y ∈ (⋂[ i in I ] B at i)) =>
                Exists.elim hexii (
                  fun (i) =>
                    fun (hi : i ∈ I ∧ is_minimum 𝓐 (B _ i) x) =>
                      And.right (And.right hi) y (

                        let u := fun (hIemp : I = ∅) =>
                          empty_set_is_empty i (
                            eq_subst (fun (t) => i ∈ t) I ∅ hIemp (And.left hi)
                          )
                        Iff.mp (indexed_intersection_is_intersection B I u hI y) hy i (And.left hi)
                      )
                )
          )
theorem max_um_is_al : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_maximum 𝓐 B x) → (is_maximal 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      let first := triple_po_is_po 𝓐 h𝓐
      let v := bin_on_is_bin (setPO(𝓐)) (≼(𝓐)) (
        And.left (And.left (And.right (Iff.mp (part_ord_nspo_crit (setPO(𝓐)) (≺(𝓐)) (≼(𝓐))) first)))
      )
      fun (hm_um : (is_maximum 𝓐 B x)) =>

        And.intro (And.left hm_um) (
          fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hxy : (x . (≺(𝓐)) . y)) =>
                  no_symm_R₁_R₂ 𝓐 h𝓐 x y (
                    And.intro (hxy) (
                      let u := And.right hm_um y hyB
                      Iff.mpr (inv_pair_prop (≼(𝓐)) (v) y x) u
                    )
                  )
        )
theorem min_um_is_al : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_minimum 𝓐 B x) → (is_minimal 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>

      fun (hm_um : (is_minimum 𝓐 B x)) =>

        And.intro (And.left hm_um) (
          fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hxy : (y . (≺(𝓐)) . x)) =>
                  let first := And.left (And.left (And.right (triple_po_is_po 𝓐 h𝓐)))
                  let second := bin_on_is_bin (setPO(𝓐)) (≺(𝓐)) first
                  let third := Iff.mpr (inv_pair_prop (≺(𝓐)) second y x) (Iff.mp (inv_pair_prop (≺(𝓐))
                  (bin_R₁ 𝓐 h𝓐) y x) (hxy))
                  no_symm_R₁_R₂ 𝓐 h𝓐 y x (
                    And.intro (third) (
                      And.right hm_um y hyB
                    )
                  )
        )
theorem max_um_unique : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_maximum 𝓐 B x) → (is_maximum 𝓐 B y) → (x = y) :=
  fun (𝓐 B x y) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hmaxx : (is_maximum 𝓐 B x)) =>
        fun (hmaxy : (is_maximum 𝓐 B y)) =>
          let u := And.right hmaxx y (And.left hmaxy)
          let u₀₁ := Iff.mp (inv_pair_prop (≼(𝓐)) (bin_R₂ 𝓐 h𝓐) y x) (u)
          let u₂ := Iff.mpr (po_lesseq_moreeq 𝓐 h𝓐 y x) (u₀₁)
          let v := And.right hmaxy x (And.left hmaxx)
          let v₀₂ := Iff.mp (inv_pair_prop (≼(𝓐)) (bin_R₂ 𝓐 h𝓐) x y) (v)
          let v₂ := Iff.mpr (po_lesseq_moreeq 𝓐 h𝓐 x y) (v₀₂)
          antisymm_R₂ 𝓐 h𝓐 x y (v₂) (u₂)
theorem min_um_unique : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_minimum 𝓐 B x) → (is_minimum 𝓐 B y) → (x = y) :=
  fun (𝓐 B x y) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hminx : (is_minimum 𝓐 B x)) =>
        fun (hminy : (is_minimum 𝓐 B y)) =>
          let u := And.right hminx y (And.left hminy)
          let v := And.right hminy x (And.left hminx)
          antisymm_R₂ 𝓐 h𝓐 x y (u) (v)
theorem max_um_maxset_singl : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_maximum 𝓐 B x) → (max_set 𝓐 B = {x}) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hmaxum : (is_maximum 𝓐 B x)) =>
          extensionality (max_set 𝓐 B) {x} (
              fun (y) =>
                Iff.intro
                (
                  fun (hy : y ∈ (max_set 𝓐 B)) =>
                    let first := Iff.mp (max_set_is_max_set 𝓐 B y) hy
                    let u := And.right (first) x (And.left hmaxum)

                    let v := And.right hmaxum y (And.left first)



                    eq_subst (fun (t) => t ∈ {x}) x y (
                      byContradiction (
                        fun (hxyneq : x ≠ y) =>
                          let s := part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 y x (And.intro (
                            Iff.mpr (po_lesseq_moreeq 𝓐 h𝓐 y x) (
                              Iff.mp (inv_pair_prop (≼(𝓐)) (bin_R₂ 𝓐 h𝓐) y x) (
                                v
                              )
                            )
                          ) (
                            fun (hyxeq : y = x) =>
                              hxyneq (Eq.symm hyxeq)
                          ))

                          u s
                      )


                    ) (elem_in_singl x)


                )
                (
                  fun (hy : y ∈ {x}) =>
                    let u := in_singl_elem x y hy
                    Iff.mpr (max_set_is_max_set 𝓐 B y) (
                      eq_subst (fun (t) => is_maximal 𝓐 B t) x y (Eq.symm u) (

                        And.intro (And.left hmaxum) (
                          fun (z) =>
                            fun (hz : z ∈ B) =>
                              fun (hxz : (x . (≺(𝓐)) . z)) =>
                                let v := And.right hmaxum z hz
                                let v₂ := Iff.mpr (po_lesseq_moreeq 𝓐 h𝓐 z x) (
                                  Iff.mp (inv_pair_prop (≼(𝓐)) (bin_R₂ 𝓐 h𝓐) z x) (v)
                                )
                                no_symm_R₁_R₂ 𝓐 h𝓐 x z (
                                  And.intro (hxz) (v₂)
                                )
                        )
                      )
                    )
                )
            )
theorem min_um_minset_singl : ∀ 𝓐 B x, (PartOrd 𝓐) → (is_minimum 𝓐 B x) → (min_set 𝓐 B = {x}) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hmaxum : (is_minimum 𝓐 B x)) =>
          extensionality (min_set 𝓐 B) {x} (
              fun (y) =>
                Iff.intro
                (
                  fun (hy : y ∈ (min_set 𝓐 B)) =>
                    let first := Iff.mp (min_set_is_min_set 𝓐 B y) hy
                    let u := And.right (first) x (And.left hmaxum)

                    let v := And.right hmaxum y (And.left first)
                    let v₂ := Iff.mp (po_lesseq_moreeq 𝓐 h𝓐 x y) v



                    eq_subst (fun (t) => t ∈ {x}) x y (
                      byContradiction (
                        fun (hxyneq : x ≠ y) =>
                          let s := part_ord_pair_prop_neqR₂R₁ 𝓐 h𝓐 x y (And.intro (
                            Iff.mpr (po_lesseq_moreeq 𝓐 h𝓐 x y) v₂
                          ) (
                            hxyneq
                            ))
                          let t := Iff.mp (po_less_more 𝓐 h𝓐 x y) s
                          u (Iff.mpr (inv_pair_prop (≺(𝓐)) (bin_R₁ 𝓐 h𝓐) x y) (t))
                      )


                    ) (elem_in_singl x)


                )
                (
                  fun (hy : y ∈ {x}) =>
                    let u := in_singl_elem x y hy
                    Iff.mpr (min_set_is_min_set 𝓐 B y) (
                      eq_subst (fun (t) => is_minimal 𝓐 B t) x y (Eq.symm u) (

                        And.intro (And.left hmaxum) (
                          fun (z) =>
                            fun (hz : z ∈ B) =>
                              fun (hxz : (z . (≺(𝓐)) . x)) =>
                                let v := And.right hmaxum z hz
                                let v₂ := Iff.mpr (po_less_more 𝓐 h𝓐 z x) (
                                  Iff.mp (inv_pair_prop (≺(𝓐)) (bin_R₁ 𝓐 h𝓐) z x) (
                                    hxz
                                  )
                                )
                                no_symm_R₁_R₂ 𝓐 h𝓐 z x (
                                  And.intro (v₂) (v)
                                )
                        )
                      )
                    )
                )
            )
theorem max_al_subset_prop : ∀ 𝓐 B C x, (C ⊆ B) → (is_maximal 𝓐 B x) → (x ∈ C) → (is_maximal 𝓐 C x) :=
  fun (𝓐 B C x) =>
        fun (hCB : (C ⊆ B)) =>
          fun (hmax : (is_maximal 𝓐 B x)) =>
            fun (hxC : x ∈ C) =>
              And.intro hxC (
                fun (y) =>
                  fun (hy : y ∈ C) =>
                    And.right hmax y (hCB y hy)
              )
theorem min_al_subsets_prop : ∀ 𝓐 B C x, (C ⊆ B) → (is_minimal 𝓐 B x) → (x ∈ C) → (is_minimal 𝓐 C x) :=
  fun (𝓐 B C x) =>
        fun (hCB : (C ⊆ B)) =>
          fun (hmin : (is_minimal 𝓐 B x)) =>
            fun (hxC : x ∈ C) =>
              And.intro hxC (
                fun (y) =>
                  fun (hy : y ∈ C) =>
                    And.right hmin y (hCB y hy)
              )
theorem max_um_subset_prop : ∀ 𝓐 B C x, (C ⊆ B) → (is_maximum 𝓐 B x) → (x ∈ C) → (is_maximum 𝓐 C x) :=
  fun (𝓐 B C x) =>
        fun (hCB : (C ⊆ B)) =>
          fun (hmax : (is_maximum 𝓐 B x)) =>
            fun (hxC : x ∈ C) =>
              And.intro hxC (
                fun (y) =>
                  fun (hy : y ∈ C) =>
                    And.right hmax y (hCB y hy)
              )
theorem min_um_subset_prop : ∀ 𝓐 B C x, (C ⊆ B) → (is_minimum 𝓐 B x) → (x ∈ C) → (is_minimum 𝓐 C x) :=
  fun (𝓐 B C x) =>
        fun (hCB : (C ⊆ B)) =>
          fun (hmin : (is_minimum 𝓐 B x)) =>
            fun (hxC : x ∈ C) =>
              And.intro hxC (
                fun (y) =>
                  fun (hy : y ∈ C) =>
                    And.right hmin y (hCB y hy)
              )
theorem max_al_un_prop : ∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_maximal 𝓐 (B _ i) x) → (is_maximal 𝓐 (⋃[i in I] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hBI : (B Indx I)) =>
        fun (hix : (∀ i ∈ I; is_maximal 𝓐 (B _ i) x) ) =>
          let u := Iff.mp (set_non_empty_iff_non_empty I) hI
          Exists.elim u (
            fun (i) =>
              fun (hi : i ∈ I) =>
                let v₁ := And.left (hix i hi)
                let v₂ := Iff.mpr (indexed_union_is_union B I hBI x) (Exists.intro i (And.intro hi (v₁)))
                And.intro v₂ (
                  fun (y) =>
                    fun (hy : y ∈ (⋃[i in I] B at i)) =>
                      let v := Iff.mp (indexed_union_is_union B I hBI y) hy
                      Exists.elim v (
                        fun (j) =>
                          fun (hj : j ∈ I ∧ y ∈ (B _ j)) =>
                            And.right (hix j (And.left hj)) y (And.right hj)
                      )

                )
          )
theorem min_al_un_prop : ∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_minimal 𝓐 (B _ i) x) → (is_minimal 𝓐 (⋃[i in I] B at i) x) :=
   fun (𝓐 B I x) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hBI : (B Indx I)) =>
        fun (hix : (∀ i ∈ I; is_minimal 𝓐 (B _ i) x) ) =>
          let u := Iff.mp (set_non_empty_iff_non_empty I) hI
          Exists.elim u (
            fun (i) =>
              fun (hi : i ∈ I) =>
                let v₁ := And.left (hix i hi)
                let v₂ := Iff.mpr (indexed_union_is_union B I hBI x) (Exists.intro i (And.intro hi (v₁)))
                And.intro v₂ (
                  fun (y) =>
                    fun (hy : y ∈ (⋃[i in I] B at i)) =>
                      let v := Iff.mp (indexed_union_is_union B I hBI y) hy
                      Exists.elim v (
                        fun (j) =>
                          fun (hj : j ∈ I ∧ y ∈ (B _ j)) =>
                            And.right (hix j (And.left hj)) y (And.right hj)
                      )

                )
          )
theorem max_um_un_prop : ∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_maximum 𝓐 (B _ i) x) → (is_maximum 𝓐 (⋃[i in I] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hBI : (B Indx I)) =>
        fun (hix : (∀ i ∈ I; is_maximum 𝓐 (B _ i) x) ) =>
          let u := Iff.mp (set_non_empty_iff_non_empty I) hI
          Exists.elim u (
            fun (i) =>
              fun (hi : i ∈ I) =>
                let v₁ := And.left (hix i hi)
                let v₂ := Iff.mpr (indexed_union_is_union B I hBI x) (Exists.intro i (And.intro hi (v₁)))
                And.intro v₂ (
                  fun (y) =>
                    fun (hy : y ∈ (⋃[i in I] B at i)) =>
                      let v := Iff.mp (indexed_union_is_union B I hBI y) hy
                      Exists.elim v (
                        fun (j) =>
                          fun (hj : j ∈ I ∧ y ∈ (B _ j)) =>
                            And.right (hix j (And.left hj)) y (And.right hj)
                      )

                )
          )
theorem min_um_un_prop : ∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_minimum 𝓐 (B _ i) x) → (is_minimum 𝓐 (⋃[i in I] B at i) x) :=
   fun (𝓐 B I x) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hBI : (B Indx I)) =>
        fun (hix : (∀ i ∈ I; is_minimum 𝓐 (B _ i) x) ) =>
          let u := Iff.mp (set_non_empty_iff_non_empty I) hI
          Exists.elim u (
            fun (i) =>
              fun (hi : i ∈ I) =>
                let v₁ := And.left (hix i hi)
                let v₂ := Iff.mpr (indexed_union_is_union B I hBI x) (Exists.intro i (And.intro hi (v₁)))
                And.intro v₂ (
                  fun (y) =>
                    fun (hy : y ∈ (⋃[i in I] B at i)) =>
                      let v := Iff.mp (indexed_union_is_union B I hBI y) hy
                      Exists.elim v (
                        fun (j) =>
                          fun (hj : j ∈ I ∧ y ∈ (B _ j)) =>
                            And.right (hix j (And.left hj)) y (And.right hj)
                      )

                )
          )




def is_upper_bound (𝓐 B x : Set) := x ∈ setPO(𝓐) ∧ ∀ y ∈ B; (y . (≼(𝓐)) . x)
def is_lower_bound (𝓐 B x : Set) := x ∈ setPO(𝓐) ∧ ∀ y ∈ B; (x . (≼(𝓐)) . y)

noncomputable def lower_bounds (𝓐 B) := {z ∈ setPO(𝓐) | is_lower_bound 𝓐 B z}
noncomputable def upper_bounds (𝓐 B) := {z ∈ setPO(𝓐) | is_upper_bound 𝓐 B z}

syntax term "▴" term : term
syntax term "▾" term : term
macro_rules
| `($𝓐:term ▾ $B:term) => `(lower_bounds $𝓐 $B)
| `($𝓐:term ▴ $B:term) => `(upper_bounds $𝓐 $B)


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
theorem low_bou_set_is_low_bou : ∀ 𝓐 B x, (x ∈ (𝓐 ▾ B) ↔ (is_lower_bound 𝓐 B x)) :=
  fun (𝓐 B) =>
    fun (x) =>
      Iff.intro
      (
        fun (hx : x ∈ (𝓐 ▾ B)) =>
          And.right (Iff.mp (spec_is_spec (fun (P) => is_lower_bound 𝓐 B P) (setPO(𝓐)) x) hx)
      )
      (
        fun (hx : (is_lower_bound 𝓐 B x)) =>
          Iff.mpr (spec_is_spec (fun (P) => is_lower_bound 𝓐 B P) (setPO(𝓐)) x) (
            And.intro (And.left hx) (hx)
          )
      )
theorem upp_bou_set_is_upp_bou : ∀ 𝓐 B x, (x ∈ (𝓐 ▴ B) ↔ (is_upper_bound 𝓐 B x)) :=
  fun (𝓐 B) =>
    fun (x) =>
      Iff.intro
      (
        fun (hx : x ∈ (𝓐 ▴ B)) =>
          And.right (Iff.mp (spec_is_spec (fun (P) => is_upper_bound 𝓐 B P) (setPO(𝓐)) x) hx)
      )
      (
        fun (hx : (is_upper_bound 𝓐 B x)) =>
          Iff.mpr (spec_is_spec (fun (P) => is_upper_bound 𝓐 B P) (setPO(𝓐)) x) (
            And.intro (And.left hx) (hx)
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
theorem max_um_upp_bou : ∀ 𝓐 B x, (B ⊆ (setPO(𝓐))) → (is_maximum 𝓐 B x) → (is_upper_bound 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (hBA : (B ⊆ (setPO(𝓐)))) =>
      fun (hmax : (is_maximum 𝓐 B x)) =>
        And.intro (hBA x (And.left hmax)) (And.right hmax)
theorem min_um_low_bou : ∀ 𝓐 B x, (B ⊆ (setPO(𝓐))) → (is_minimum 𝓐 B x) → (is_lower_bound 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (hBA : (B ⊆ (setPO(𝓐)))) =>
      fun (hmin : (is_minimum 𝓐 B x)) =>
        And.intro (hBA x (And.left hmin)) (And.right hmin)
theorem upp_bou_max_um : ∀ 𝓐 B x, (is_upper_bound 𝓐 B x) → (x ∈ B) → (is_maximum 𝓐 B x) :=
  fun (𝓐 B x) =>
      fun (hupp : (is_upper_bound 𝓐 B x)) =>
        fun (hx : x ∈ B) =>
          And.intro (hx) (
            let v := And.right (hupp)
            fun (y) =>
              fun (hy : y ∈ B) =>
                v y hy
          )
theorem low_bou_min_um : ∀ 𝓐 B x, (is_lower_bound 𝓐 B x) → (x ∈ B) → (is_minimum 𝓐 B x) :=
  fun (𝓐 B x) =>
      fun (hupp : (is_lower_bound 𝓐 B x)) =>
        fun (hx : x ∈ B) =>
          And.intro (hx) (
            let v := And.right (hupp)
            fun (y) =>
              fun (hy : y ∈ B) =>
                v y hy
          )
theorem upp_bou_subset : ∀ 𝓐 B C x, (B ⊆ C) → (is_upper_bound 𝓐 C x) → (is_upper_bound 𝓐 B x) :=
  fun (𝓐 B C x) =>
    fun (hBC : (B ⊆ C)) =>
      fun (huppC : (is_upper_bound 𝓐 C x)) =>
        And.intro (And.left huppC) (
          fun (y) =>
            fun (hy : y ∈ B) =>
              And.right huppC y (hBC y hy)
        )
theorem low_bou_subset : ∀ 𝓐 B C x, (B ⊆ C) → (is_lower_bound 𝓐 C x) → (is_lower_bound 𝓐 B x) :=
  fun (𝓐 B C x) =>
    fun (hBC : (B ⊆ C)) =>
      fun (hlowC : (is_lower_bound 𝓐 C x)) =>
        And.intro (And.left hlowC) (
          fun (y) =>
            fun (hy : y ∈ B) =>
              And.right hlowC y (hBC y hy)
        )
theorem upp_bou_set_subset : ∀ 𝓐 B C, (B ⊆ C) → (𝓐 ▴ C) ⊆ (𝓐 ▴ B) :=
  fun (𝓐 B C) =>
    fun (hBC : (B ⊆ C)) =>
      fun (x) =>
        fun (huppC : x ∈ (𝓐 ▴ C)) =>
          Iff.mpr (upp_bou_set_is_upp_bou 𝓐 B x) (
            upp_bou_subset 𝓐 B C x hBC (
              Iff.mp (upp_bou_set_is_upp_bou 𝓐 C x) (huppC)
            )
          )
theorem low_bou_set_subset : ∀ 𝓐 B C, (B ⊆ C) → (𝓐 ▾ C) ⊆ (𝓐 ▾ B) :=
  fun (𝓐 B C) =>
    fun (hBC : (B ⊆ C)) =>
      fun (x) =>
        fun (hlowC : (x ∈ (𝓐 ▾ C))) =>
          Iff.mpr (low_bou_set_is_low_bou 𝓐 B x) (
            low_bou_subset 𝓐 B C x hBC (
              Iff.mp (low_bou_set_is_low_bou 𝓐 C x) (hlowC)
            )
          )
theorem sub_upp_low : ∀ 𝓐 B, (B ⊆ (setPO(𝓐))) → (B ⊆ (𝓐 ▴ (𝓐 ▾ B))) :=
  fun (𝓐 B) =>
    fun (hBA : B ⊆ setPO(𝓐)) =>
      fun (x) =>
        fun (hx : x ∈ B) =>
          Iff.mpr (upp_bou_set_is_upp_bou 𝓐 ((𝓐 ▾ B)) x) (
            And.intro (hBA x hx) (
              fun (y) =>
                fun (hy : y ∈ (𝓐 ▾ B)) =>
                  And.right (Iff.mp (low_bou_set_is_low_bou 𝓐 B y) hy) x hx
            )
          )
theorem sub_low_upp :∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (B ⊆ (𝓐 ▾ (𝓐 ▴ B))) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hBA : B ⊆ setPO(𝓐)) =>
      fun (x) =>
        fun (hx : x ∈ B) =>
          Iff.mpr (low_bou_set_is_low_bou 𝓐 (𝓐 ▴ B) x) (
            And.intro (hBA x hx) (
              fun (y) =>
                fun (hy : y ∈ (𝓐 ▴ B)) =>
                  And.right (Iff.mp (upp_bou_set_is_upp_bou 𝓐 B y) hy) x hx
            )
          )
theorem upp_low_upp_is_low : ∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (𝓐 ▴ (𝓐 ▾ (𝓐 ▴ B))) = (𝓐 ▴ B) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hBA : (B ⊆ (setPO(𝓐)))) =>
        sub_sub_then_eq (𝓐 ▴ (𝓐 ▾ (𝓐 ▴ B))) (𝓐 ▴ B) (
          upp_bou_set_subset 𝓐 B (𝓐 ▾ (𝓐 ▴ B)) (sub_low_upp 𝓐 B h𝓐 hBA)
        ) (
          let P := fun (t) => is_upper_bound 𝓐 B t
          sub_upp_low 𝓐 (𝓐 ▴ B) (specification_set_subset P (setPO(𝓐)))
        )
theorem low_upp_low_is_upp : ∀ 𝓐 B, (PartOrd 𝓐) → (B ⊆ (setPO(𝓐))) → (𝓐 ▾ (𝓐 ▴ (𝓐 ▾ B))) = (𝓐 ▾ B) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hBA : (B ⊆ (setPO(𝓐)))) =>
        sub_sub_then_eq (𝓐 ▾ (𝓐 ▴ (𝓐 ▾ B))) (𝓐 ▾ B) (
          low_bou_set_subset 𝓐 B (𝓐 ▴ (𝓐 ▾ B)) (sub_upp_low 𝓐 B hBA)
        ) (
          let P := fun (t) => is_lower_bound 𝓐 B t
          sub_low_upp 𝓐 (𝓐 ▾ B) h𝓐 (specification_set_subset P (setPO(𝓐)))
        )


theorem upp_bou_inter : ∀ 𝓐 B I x, (B IndxFun I) → (∃ i ∈ I; is_upper_bound 𝓐 (B _ i) x) → (is_upper_bound 𝓐 (⋂[ i in I ] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hBI : (B IndxFun I)) =>
      fun (hupp : (∃ i ∈ I; is_upper_bound 𝓐 (B _ i) x)) =>
        Exists.elim hupp (
          fun (i) =>
            fun (hi : i ∈ I ∧ is_upper_bound 𝓐 (B _ i) x) =>
              let u := indexed_intersection_sub_indexed B I hBI i (And.left hi)
              upp_bou_subset 𝓐 (⋂[ i in I ] B at i) (B _ i) x u (And.right hi)
        )
theorem low_bou_inter : ∀ 𝓐 B I x, (B IndxFun I) → (∃ i ∈ I; is_lower_bound 𝓐 (B _ i) x) → (is_lower_bound 𝓐 (⋂[ i in I ] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hBI : (B IndxFun I)) =>
      fun (hupp : (∃ i ∈ I; is_lower_bound 𝓐 (B _ i) x)) =>
        Exists.elim hupp (
          fun (i) =>
            fun (hi : i ∈ I ∧ is_lower_bound 𝓐 (B _ i) x) =>
              let u := indexed_intersection_sub_indexed B I hBI i (And.left hi)
              low_bou_subset 𝓐 (⋂[ i in I ] B at i) (B _ i) x u (And.right hi)
        )
theorem upp_bou_un_prop : ∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_upper_bound 𝓐 (B _ i) x) → (is_upper_bound 𝓐 (⋃[i in I] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hBI : (B Indx I)) =>
         fun (hiI : (∀ i ∈ I; is_upper_bound 𝓐 (B _ i) x)) =>
            Exists.elim (Iff.mp (set_non_empty_iff_non_empty I) hI) (
              fun (i) =>
                fun (hi : i ∈ I) =>
                  let u := hiI i hi
                  let s := And.left u
                  And.intro s (
                    fun (y) =>
                      fun (hy : y ∈ (⋃[i in I] B at i)) =>
                        Exists.elim (Iff.mp (indexed_union_is_union B I hBI y) hy) (
                          fun (j) =>
                            fun (hj : j ∈ I ∧ y ∈ (B _ j)) =>
                              And.right (hiI j (And.left hj)) y (And.right hj)
                        )
                  )
            )
theorem low_bou_un_prop : ∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_lower_bound 𝓐 (B _ i) x) → (is_lower_bound 𝓐 (⋃[i in I] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hBI : (B Indx I)) =>
         fun (hiI : (∀ i ∈ I; is_lower_bound 𝓐 (B _ i) x)) =>
            Exists.elim (Iff.mp (set_non_empty_iff_non_empty I) hI) (
              fun (i) =>
                fun (hi : i ∈ I) =>
                  let u := hiI i hi
                  let s := And.left u
                  And.intro s (
                    fun (y) =>
                      fun (hy : y ∈ (⋃[i in I] B at i)) =>
                        Exists.elim (Iff.mp (indexed_union_is_union B I hBI y) hy) (
                          fun (j) =>
                            fun (hj : j ∈ I ∧ y ∈ (B _ j)) =>
                              And.right (hiI j (And.left hj)) y (And.right hj)
                        )
                  )
            )



def is_supremum (𝓐 B x : Set) : Prop := is_minimum 𝓐 (𝓐 ▴ B) x
def is_infimum (𝓐 B x : Set) : Prop := is_maximum 𝓐 (𝓐 ▾ B) x

theorem sup_is_upp : ∀ 𝓐 B x, is_supremum 𝓐 B x → (is_upper_bound 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (hsup : (is_supremum 𝓐 B x)) =>
      let u := And.left hsup
      Iff.mp (upp_bou_set_is_upp_bou 𝓐 B x) u
theorem inf_is_low : ∀ 𝓐 B x, is_infimum 𝓐 B x → (is_lower_bound 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (hinf : (is_infimum 𝓐 B x)) =>
      let u := And.left hinf
      Iff.mp (low_bou_set_is_low_bou 𝓐 B x) u
theorem sup_is_sm_upp : ∀ 𝓐 B x, is_supremum 𝓐 B x → (∀ y, (is_upper_bound 𝓐 B y) → (x . (≼(𝓐)) . y)) :=
  fun (𝓐 B x) =>
    fun (hsup : is_supremum 𝓐 B x) =>
      fun (y) =>
        fun (hy : (is_upper_bound 𝓐 B y)) =>
          let v := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 B y) hy
          And.right hsup y v
theorem inf_is_big_low : ∀ 𝓐 B x, is_infimum 𝓐 B x → (∀ y, (is_lower_bound 𝓐 B y) → (y . (≼(𝓐)) . x)) :=
  fun (𝓐 B x) =>
    fun (hinf : is_infimum 𝓐 B x) =>
      fun (y) =>
        fun (hy : (is_lower_bound 𝓐 B y)) =>
          let v := Iff.mpr (low_bou_set_is_low_bou 𝓐 B y) hy
          And.right hinf y v


theorem upp_and_sm_upp_sup : ∀ 𝓐 B x, (is_upper_bound 𝓐 B x) → (∀ y, (is_upper_bound 𝓐 B y) → (x . (≼(𝓐)) . y)) → (is_supremum 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (huppx : (is_upper_bound 𝓐 B x)) =>
      fun (huppy : (∀ y, (is_upper_bound 𝓐 B y) → (x . (≼(𝓐)) . y))) =>
        And.intro (
          Iff.mpr (upp_bou_set_is_upp_bou 𝓐 B x) (
            huppx
          )
        ) (
          fun (y) =>
            fun (hy : y ∈ (𝓐 ▴ B)) =>
              huppy y (
                Iff.mp (upp_bou_set_is_upp_bou 𝓐 B y) hy
              )
        )
theorem low_and_big_low_inf : ∀ 𝓐 B x, (is_lower_bound 𝓐 B x) → (∀ y, (is_lower_bound 𝓐 B y) → (y . (≼(𝓐)) . x)) → (is_infimum 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (huppx : (is_lower_bound 𝓐 B x)) =>
      fun (huppy : (∀ y, (is_lower_bound 𝓐 B y) → (y . (≼(𝓐)) . x))) =>
        And.intro (
          Iff.mpr (low_bou_set_is_low_bou 𝓐 B x) (
            huppx
          )
        ) (
          fun (y) =>
            fun (hy : y ∈ (𝓐 ▾ B)) =>
              huppy y (
                Iff.mp (low_bou_set_is_low_bou 𝓐 B y) hy
              )
        )
theorem sup_uni : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_supremum 𝓐 B x) → (is_supremum 𝓐 B y) → (x = y) :=
  fun (𝓐 B x y) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hsupx : (is_supremum 𝓐 B x)) =>
        fun (hsupy : (is_supremum 𝓐 B y)) =>
          min_um_unique 𝓐 (𝓐 ▴ B) x y h𝓐 hsupx hsupy
theorem inf_uni : ∀ 𝓐 B x y, (PartOrd 𝓐) → (is_infimum 𝓐 B x) → (is_infimum 𝓐 B y) → (x = y) :=
  fun (𝓐 B x y) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hinfx : (is_infimum 𝓐 B x)) =>
        fun (hinfy : (is_infimum 𝓐 B y)) =>
          max_um_unique 𝓐 (𝓐 ▾ B) x y h𝓐 hinfx hinfy
theorem inv_is_sup_inf : ∀ 𝓐 B, (PartOrd 𝓐) → (∀ x, (is_supremum 𝓐 B x) ↔ (is_infimum (invPO 𝓐) B x)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (x) =>
        Iff.intro
        (
          fun (hsupx : (is_supremum 𝓐 B x)) =>
            let u := And.left hsupx
            let res₁ := upp_bou_set_inv 𝓐 B
            let res₂ := eq_subst (fun (t) => x ∈ t) (upper_bounds 𝓐 B) (lower_bounds (inv_PO 𝓐) B) res₁ u
            And.intro (res₂) (

              fun (y) =>
                fun (hy : y ∈ ((inv_PO 𝓐) ▾ B)) =>
                  let v := upp_bou_set_inv 𝓐 B
                  let v₂ := eq_subst (fun (t) => y ∈ t) ((inv_PO 𝓐) ▾ B) (𝓐 ▴ B) (Eq.symm v) hy
                  let v₃ := And.right hsupx y v₂
                  Iff.mpr (inv_PO_lesseq 𝓐 h𝓐 y x) v₃

            )
        )
        (
          fun (hinfinvx : (is_infimum (invPO 𝓐) B x)) =>
            let u := And.left hinfinvx
            let res₁ := upp_bou_set_inv 𝓐 B
            let res₂ := eq_subst (fun (t) => x ∈ t) (lower_bounds (inv_PO 𝓐) B) (upper_bounds 𝓐 B) (Eq.symm res₁) u
            And.intro (res₂) (
              fun (y) =>
                fun (hy : y ∈ (𝓐 ▴ B)) =>
                  let v := upp_bou_set_inv 𝓐 B
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
theorem max_um_is_sup : ∀ 𝓐 B x, (B ⊆ setPO(𝓐)) → (is_maximum 𝓐 B x) → (is_supremum 𝓐 B x) :=
  fun (𝓐 B x) =>
    fun (hBA : (B ⊆ setPO(𝓐))) =>
      fun (hmax : (is_maximum 𝓐 B x)) =>
        And.intro (
          Iff.mpr (upp_bou_set_is_upp_bou 𝓐 B x) (
            And.intro (hBA x (And.left hmax)) (And.right hmax)
          )
        ) (
          fun (y) =>
            fun (hy : y ∈ (𝓐 ▴ B)) =>
              And.right (Iff.mp (upp_bou_set_is_upp_bou 𝓐 B y) hy) x (And.left hmax)
        )
theorem min_um_is_inf :∀ 𝓐 B x, (B ⊆ setPO(𝓐)) → (is_minimum 𝓐 B x) → (is_infimum 𝓐 B x)  :=
  fun (𝓐 B x) =>
    fun (hBA : (B ⊆ setPO(𝓐))) =>
      fun (hmax : (is_minimum 𝓐 B x)) =>
        And.intro (
          Iff.mpr (low_bou_set_is_low_bou 𝓐 B x) (
            And.intro (hBA x (And.left hmax)) (And.right hmax)
          )
        ) (
          fun (y) =>
            fun (hy : y ∈ (𝓐 ▾ B)) =>
              And.right (Iff.mp (low_bou_set_is_low_bou 𝓐 B y) hy) x (And.left hmax)
        )
theorem sup_subset : ∀ 𝓐 B C x y, (PartOrd 𝓐) → (B ⊆ C) → (is_supremum 𝓐 C x) → (is_supremum 𝓐 B y) → (¬ (x . (≺(𝓐)) . y)) :=
  fun (𝓐 B C x y) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hBC : (B ⊆ C)) =>
        fun (hsupC : (is_supremum 𝓐 C x)) =>
          fun (hsupB : (is_supremum 𝓐 B y)) =>
            fun (hxy : (x . (≺(𝓐)) . y)) =>
              let v₁ := And.left hsupC
              let v := upp_bou_set_subset 𝓐 B C hBC x (v₁)
              let u := And.right hsupB x (v)
              no_symm_R₁_R₂ 𝓐 h𝓐 x y (
                And.intro (hxy) (u)
              )
theorem inf_subset : ∀ 𝓐 B C x y, (PartOrd 𝓐) → (B ⊆ C) → (is_infimum 𝓐 C x) → (is_infimum 𝓐 B y) → (¬ (y . (≺(𝓐)) . x)) :=
  fun (𝓐 B C x y) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hBC : (B ⊆ C)) =>
        fun (hinfC : (is_infimum 𝓐 C x)) =>
          fun (hinfB : (is_infimum 𝓐 B y)) =>
            fun (hxy : (y . (≺(𝓐)) . x)) =>
              let v₁ := And.left hinfC
              let v := low_bou_set_subset 𝓐 B C hBC x (v₁)
              let u := And.right hinfB x (v)
              no_symm_R₁_R₂ 𝓐 h𝓐 y x (
                And.intro (
                  hxy
                ) (

                  u
                )
              )
theorem sup_union : ∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_supremum 𝓐 (B _ i) x) → (is_supremum 𝓐 (⋃[i in I] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hBI : (B Indx I)) =>
        fun (hiall : (∀ i ∈ I; is_supremum 𝓐 (B _ i) x)) =>
          And.intro (
            Iff.mpr (upp_bou_set_is_upp_bou 𝓐 (⋃[i in I] B at i) x) (
              upp_bou_un_prop 𝓐 B I x hI hBI (
                fun (i) => fun (hi : i ∈ I) =>
                  Iff.mp (upp_bou_set_is_upp_bou 𝓐 (B _ i) x) (
                    And.left (hiall i hi)
                  )
              )
            )
          ) (
            fun (y) =>
              fun (hy : y ∈ (𝓐 ▴ (⋃[i in I] B at i))) =>
                let u := Iff.mp (upp_bou_set_is_upp_bou 𝓐 (⋃[i in I] B at i) y) hy
                Exists.elim (Iff.mp (set_non_empty_iff_non_empty I) hI) (
                  fun (i) =>
                    fun (hi : i ∈ I) =>
                      let v := upp_bou_subset 𝓐 (B _ i) (⋃[i in I] B at i) y (
                        indexed_sub_indexed_union B I hBI i hi
                      ) u
                      let v₀ := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 (B _ i) y) v
                      let v₂ := hiall i hi
                      And.right v₂ y v₀
                )
          )
theorem inf_union : ∀ 𝓐 B I x, (I ≠ ∅) → (B Indx I) → (∀ i ∈ I; is_infimum 𝓐 (B _ i) x) → (is_infimum 𝓐 (⋃[i in I] B at i) x) :=
  fun (𝓐 B I x) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hBI : (B Indx I)) =>
        fun (hiall : (∀ i ∈ I; is_infimum 𝓐 (B _ i) x)) =>
          And.intro (
            Iff.mpr (low_bou_set_is_low_bou 𝓐 (⋃[i in I] B at i) x) (
              low_bou_un_prop 𝓐 B I x hI hBI (
                fun (i) => fun (hi : i ∈ I) =>
                  Iff.mp (low_bou_set_is_low_bou 𝓐 (B _ i) x) (
                    And.left (hiall i hi)
                  )
              )
            )
          ) (
            fun (y) =>
              fun (hy : y ∈ (𝓐 ▾ (⋃[i in I] B at i))) =>
                let u := Iff.mp (low_bou_set_is_low_bou 𝓐 (⋃[i in I] B at i) y) hy
                Exists.elim (Iff.mp (set_non_empty_iff_non_empty I) hI) (
                  fun (i) =>
                    fun (hi : i ∈ I) =>
                      let v := low_bou_subset 𝓐 (B _ i) (⋃[i in I] B at i) y (
                        indexed_sub_indexed_union B I hBI i hi
                      ) u
                      let v₀ := Iff.mpr (low_bou_set_is_low_bou 𝓐 (B _ i) y) v
                      let v₂ := hiall i hi
                      And.right v₂ y v₀
                )
          )



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


theorem max_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MaxExi B) → (is_maximum 𝓐 B (𝓐 Max B)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hmaxexi : (𝓐 MaxExi B)) =>
        Exists.elim hmaxexi (
          fun (y) =>
            fun (hy : is_maximum 𝓐 B y) =>
              let S := {b ∈ B | is_maximum 𝓐 B b}
              let u := extensionality S {y} (
                fun (s) =>
                  Iff.intro
                  (
                    fun (hs : s ∈ S) =>
                      let v := And.right (Iff.mp (spec_is_spec (fun (t) => is_maximum 𝓐 B t) (B) s) hs)
                      let v₂ := max_um_unique 𝓐 B s y h𝓐 v hy
                      eq_subst (fun (t) => t ∈ {y}) y s (Eq.symm v₂) (elem_in_singl y)
                  )
                  (
                    fun (hs : s ∈ {y}) =>
                      let v := in_singl_elem y s hs
                      let v₂ := eq_subst (fun (t) => is_maximum 𝓐 B t) y s (Eq.symm v) hy
                      Iff.mpr (spec_is_spec (fun (t) => is_maximum 𝓐 B t) (B) s) (
                        And.intro (And.left v₂) (v₂)
                      )
                  )
              )
              let r := eq_subst (fun (t) => ⋃ t = (𝓐 Max B)) S {y} u (Eq.refl (⋃ S))
              let v := Eq.symm (union_singleton y)
              let res₁ := Eq.trans v r

              eq_subst (fun (t) => is_maximum 𝓐 B t) y (𝓐 Max B) res₁ hy
        )
theorem min_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MinExi B) → (is_minimum 𝓐 B (𝓐 Min B)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hminexi : (𝓐 MinExi B)) =>
        Exists.elim hminexi (
          fun (y) =>
            fun (hy : is_minimum 𝓐 B y) =>
              let S := {b ∈ B | is_minimum 𝓐 B b}
              let u := extensionality S {y} (
                fun (s) =>
                  Iff.intro
                  (
                    fun (hs : s ∈ S) =>
                      let v := And.right (Iff.mp (spec_is_spec (fun (t) => is_minimum 𝓐 B t) (B) s) hs)
                      let v₂ := min_um_unique 𝓐 B s y h𝓐 v hy
                      eq_subst (fun (t) => t ∈ {y}) y s (Eq.symm v₂) (elem_in_singl y)
                  )
                  (
                    fun (hs : s ∈ {y}) =>
                      let v := in_singl_elem y s hs
                      let v₂ := eq_subst (fun (t) => is_minimum 𝓐 B t) y s (Eq.symm v) hy
                      Iff.mpr (spec_is_spec (fun (t) => is_minimum 𝓐 B t) (B) s) (
                        And.intro (And.left v₂) (v₂)
                      )
                  )
              )
              let r := eq_subst (fun (t) => ⋃ t = (𝓐 Min B)) S {y} u (Eq.refl (⋃ S))
              let v := Eq.symm (union_singleton y)
              let res₁ := Eq.trans v r

              eq_subst (fun (t) => is_minimum 𝓐 B t) y (𝓐 Min B) res₁ hy
        )
theorem supr_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 SuprExi B) → (is_supremum 𝓐 B (𝓐 Supr B)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 SuprExi B)) =>
        Exists.elim hexi (
          fun (y) =>
            fun (hy : is_supremum 𝓐 B y) =>
              let S := {b ∈ setPO(𝓐) | is_supremum 𝓐 B b}
              let u := extensionality S {y} (
                fun (s) =>
                  Iff.intro
                  (
                    fun (hs : s ∈ S) =>
                      let v := And.right (Iff.mp (spec_is_spec (fun (t) => is_supremum 𝓐 B t) (setPO(𝓐)) s) hs)
                      let v₂ := sup_uni 𝓐 B s y h𝓐 v hy
                      eq_subst (fun (t) => t ∈ {y}) y s (Eq.symm v₂) (elem_in_singl y)
                  )
                  (
                    fun (hs : s ∈ {y}) =>
                      let v := in_singl_elem y s hs
                      let v₂ := eq_subst (fun (t) => is_supremum 𝓐 B t) y s (Eq.symm v) hy
                      Iff.mpr (spec_is_spec (fun (t) => is_supremum 𝓐 B t) (setPO(𝓐)) s) (
                        And.intro (
                          And.left (Iff.mp (spec_is_spec (fun (t) => is_upper_bound 𝓐 B t) setPO(𝓐) s) (And.left v₂))
                        ) (v₂)
                      )
                  )
              )
              let r := eq_subst (fun (t) => ⋃ t = (𝓐 Supr B)) S {y} u (Eq.refl (⋃ S))
              let v := Eq.symm (union_singleton y)
              let res₁ := Eq.trans v r

              eq_subst (fun (t) => is_supremum 𝓐 B t) y (𝓐 Supr B) res₁ hy
        )
theorem inf_po_prop : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 InfmExi B) → (is_infimum 𝓐 B (𝓐 Infm B)) :=
   fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 InfmExi B)) =>
        Exists.elim hexi (
          fun (y) =>
            fun (hy : is_infimum 𝓐 B y) =>
              let S := {b ∈ setPO(𝓐) | is_infimum 𝓐 B b}
              let u := extensionality S {y} (
                fun (s) =>
                  Iff.intro
                  (
                    fun (hs : s ∈ S) =>
                      let v := And.right (Iff.mp (spec_is_spec (fun (t) => is_infimum 𝓐 B t) (setPO(𝓐)) s) hs)
                      let v₂ := inf_uni 𝓐 B s y h𝓐 v hy
                      eq_subst (fun (t) => t ∈ {y}) y s (Eq.symm v₂) (elem_in_singl y)
                  )
                  (
                    fun (hs : s ∈ {y}) =>
                      let v := in_singl_elem y s hs
                      let v₂ := eq_subst (fun (t) => is_infimum 𝓐 B t) y s (Eq.symm v) hy
                      Iff.mpr (spec_is_spec (fun (t) => is_infimum 𝓐 B t) (setPO(𝓐)) s) (
                        And.intro (
                          And.left (Iff.mp (spec_is_spec (fun (t) => is_lower_bound 𝓐 B t) setPO(𝓐) s) (And.left v₂))
                        ) (v₂)
                      )
                  )
              )
              let r := eq_subst (fun (t) => ⋃ t = (𝓐 Infm B)) S {y} u (Eq.refl (⋃ S))
              let v := Eq.symm (union_singleton y)
              let res₁ := Eq.trans v r

              eq_subst (fun (t) => is_infimum 𝓐 B t) y (𝓐 Infm B) res₁ hy
        )
theorem max_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 MaxExi B) → ((is_maximum 𝓐 B x) ↔ (x = 𝓐 Max B)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 MaxExi B)) =>
        let u := max_po_prop 𝓐 B h𝓐 hexi
        Iff.intro
        (
          fun (hmax : (is_maximum 𝓐 B x)) =>
            max_um_unique 𝓐 B x (𝓐 Max B) h𝓐 hmax u
        )
        (
          fun (hmax : (x = 𝓐 Max B)) =>
            eq_subst (fun (t) => is_maximum 𝓐 B t) (𝓐 Max B) x (Eq.symm hmax) u
        )
theorem min_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 MinExi B) → ((is_minimum 𝓐 B x) ↔ (x = 𝓐 Min B)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 MinExi B)) =>
        let u := min_po_prop 𝓐 B h𝓐 hexi
        Iff.intro
        (
          fun (hmin : (is_minimum 𝓐 B x)) =>
            min_um_unique 𝓐 B x (𝓐 Min B) h𝓐 hmin u
        )
        (
          fun (hmin : (x = 𝓐 Min B)) =>
            eq_subst (fun (t) => is_minimum 𝓐 B t) (𝓐 Min B) x (Eq.symm hmin) u
        )
theorem supr_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 SuprExi B) → ((is_supremum 𝓐 B x) ↔ (x = 𝓐 Supr B)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 SuprExi B)) =>
        let u := supr_po_prop 𝓐 B h𝓐 hexi
        Iff.intro
        (
          fun (hsupr : (is_supremum 𝓐 B x)) =>
            sup_uni 𝓐 B x (𝓐 Supr B) h𝓐 hsupr u
        )
        (
          fun (hsupr : (x = 𝓐 Supr B)) =>
            eq_subst (fun (t) => is_supremum 𝓐 B t) (𝓐 Supr B) x (Eq.symm hsupr) u
        )
theorem infm_po_crit : ∀ 𝓐 B x, (PartOrd 𝓐) → (𝓐 InfmExi B) → ((is_infimum 𝓐 B x) ↔ (x = 𝓐 Infm B)) :=
   fun (𝓐 B x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 InfmExi B)) =>
        let u := inf_po_prop 𝓐 B h𝓐 hexi
        Iff.intro
        (
          fun (hinfm : (is_infimum 𝓐 B x)) =>
            inf_uni 𝓐 B x (𝓐 Infm B) h𝓐 hinfm u
        )
        (
          fun (hinfm : (x = 𝓐 Infm B)) =>
            eq_subst (fun (t) => is_infimum 𝓐 B t) (𝓐 Infm B) x (Eq.symm hinfm) u
        )
theorem sup_is_max :  ∀ 𝓐 B, (B ⊆ setPO(𝓐)) → (PartOrd 𝓐) → (𝓐 MaxExi B) → (𝓐 SuprExi B) ∧ ((𝓐 Supr B) = 𝓐 Max B) :=
  fun (𝓐 B) =>
    fun (hBA : (B ⊆ setPO(𝓐))) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hmax : (𝓐 MaxExi B)) =>
          Exists.elim hmax (
            fun (x) =>
              fun (hx : is_maximum 𝓐 B x) =>
                let u := And.intro (hBA x (And.left hx)) (And.right hx)
                let v := fun (y) => fun (hy : is_upper_bound 𝓐 B y) =>
                  And.right hy x (And.left hx)

                let v₂ := upp_and_sm_upp_sup 𝓐 B x u v
                let v₃ := Exists.intro x v₂

                And.intro (v₃) (
                  Iff.mp (max_po_crit 𝓐 B (𝓐 Supr B) h𝓐 hmax) (
                    let s := Iff.mp (supr_po_crit 𝓐 B x h𝓐 v₃) v₂
                    eq_subst (fun (t) => is_maximum 𝓐 B t) x (𝓐 Supr B) s hx
                  )
                )

          )
theorem inf_is_min : ∀ 𝓐 B, (B ⊆ setPO(𝓐)) → (PartOrd 𝓐) → (𝓐 MinExi B) → (𝓐 InfmExi B) ∧ ((𝓐 Infm B) = 𝓐 Min B) :=
  fun (𝓐 B) =>
    fun (hBA : (B ⊆ setPO(𝓐))) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hmin : (𝓐 MinExi B)) =>
          Exists.elim hmin (
            fun (x) =>
              fun (hx : is_minimum 𝓐 B x) =>
                let u := And.intro (hBA x (And.left hx)) (And.right hx)
                let v := fun (y) => fun (hy : is_lower_bound 𝓐 B y) =>
                  And.right hy x (And.left hx)
                let v₂ := low_and_big_low_inf 𝓐 B x u v
                let v₃ := Exists.intro x v₂

                And.intro (v₃) (
                  Iff.mp (min_po_crit 𝓐 B (𝓐 Infm B) h𝓐 hmin) (
                    let s := Iff.mp (infm_po_crit 𝓐 B x h𝓐 v₃) v₂
                    eq_subst (fun (t) => is_minimum 𝓐 B t) x (𝓐 Infm B) s hx
                  )
                )

          )
theorem max_min_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MaxExi B) → (((invPO 𝓐) MinExi B) ∧ ((𝓐 Max B) = (invPO(𝓐)) Min B)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 MaxExi B)) =>
        Exists.elim hexi (
          fun (x) =>
            fun (hx : is_maximum 𝓐 B x) =>
              let u := Iff.mp (max_min_inv_um 𝓐 B x h𝓐) hx
              let v₂ := Exists.intro x u
              And.intro (v₂) (
                Iff.mp (min_po_crit (invPO(𝓐)) B (𝓐 Max B) (inv_is_PO 𝓐 h𝓐) v₂)
                (
                  Iff.mp ((max_min_inv_um (𝓐) B (𝓐 Max B) h𝓐)) (max_po_prop 𝓐 B h𝓐 (
                    Exists.intro x hx
                  ))
                )
              )
          )
theorem min_max_inv : ∀ 𝓐 B, (PartOrd 𝓐) → (𝓐 MinExi B) → (((invPO 𝓐) MaxExi B) ∧ ((𝓐 Min B) = (invPO(𝓐)) Max B)) :=
  fun (𝓐 B) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hexi : (𝓐 MinExi B)) =>
        Exists.elim hexi (
          fun (x) =>
            fun (hx : is_minimum 𝓐 B x) =>
              let u := Iff.mp (min_max_inv_um 𝓐 B x h𝓐) hx
              let v₂ := Exists.intro x u
              And.intro (v₂) (
                Iff.mp (max_po_crit (invPO(𝓐)) B (𝓐 Min B) (inv_is_PO 𝓐 h𝓐) v₂)
                (
                  Iff.mp ((min_max_inv_um (𝓐) B (𝓐 Min B)) h𝓐 ) (min_po_prop 𝓐 B h𝓐 (
                    Exists.intro x hx
                  ))
                )
              )
          )
theorem max_subset_prop : ∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MaxExi B) → (((𝓐 Max B) ∈ C) ↔ ((𝓐 MaxExi C) ∧ ((𝓐 Max C) = 𝓐 Max B))) :=
  fun (𝓐 B C) =>
    fun (hCB : (C ⊆ B)) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hmaxexi : (𝓐 MaxExi B)) =>
          Iff.intro
          (
            fun (hmaxb : (𝓐 Max B) ∈ C) =>
              let u := max_po_prop 𝓐 B h𝓐 hmaxexi
              let v := max_um_subset_prop 𝓐 B C (𝓐 Max B) hCB u hmaxb
              let s := Exists.intro (𝓐 Max B) v
              And.intro (s) (
                let r := max_po_prop 𝓐 C h𝓐 s

                max_um_unique 𝓐 C (𝓐 Max C) (𝓐 Max B) h𝓐 r v
              )
          )
          (
            fun (hmaxc : (𝓐 MaxExi C) ∧ ((𝓐 Max C) = 𝓐 Max B)) =>
              eq_subst (fun (t) => t ∈ C) (𝓐 Max C) (𝓐 Max B) (And.right hmaxc) (
                And.left (max_po_prop 𝓐 C h𝓐 (And.left hmaxc))
              )
          )
theorem min_subset_prop : ∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MinExi B) → (((𝓐 Min B) ∈ C) ↔ ((𝓐 MinExi C) ∧ ((𝓐 Min C) = 𝓐 Min B))) :=
  fun (𝓐 B C) =>
    fun (hCB : (C ⊆ B)) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hminexi : (𝓐 MinExi B)) =>
          Iff.intro
          (
            fun (hminb : (𝓐 Min B) ∈ C) =>
              let u := min_po_prop 𝓐 B h𝓐 hminexi
              let v := min_um_subset_prop 𝓐 B C (𝓐 Min B) hCB u hminb
              let s := Exists.intro (𝓐 Min B) v
              And.intro (s) (
                let r := min_po_prop 𝓐 C h𝓐 s

                min_um_unique 𝓐 C (𝓐 Min C) (𝓐 Min B) h𝓐 r v
              )
          )
          (
            fun (hminc : (𝓐 MinExi C) ∧ ((𝓐 Min C) = 𝓐 Min B)) =>
              eq_subst (fun (t) => t ∈ C) (𝓐 Min C) (𝓐 Min B) (And.right hminc) (
                And.left (min_po_prop 𝓐 C h𝓐 (And.left hminc))
              )
          )
theorem max_inter_prop : ∀ 𝓐 B I i, i ∈ I → (PartOrd 𝓐) → (B IndxFun I) → ((𝓐 Max (B _ i)) ∈ (⋂[ i in I ] B at i)) → (𝓐 MaxExi (B _ i)) → ((𝓐 MaxExi (⋂[ i in I ] B at i)) ∧ ((𝓐 Max (⋂[ i in I ] B at i)) = 𝓐 Max (B _ i))) :=
  fun (𝓐 B I i) =>
    fun (hi : i ∈ I) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBI : (B IndxFun I)) =>
          fun (hR₂max : (((𝓐 Max (B _ i)) ∈ (⋂[ i in I ] B at i)))) =>
            fun (hr₂ : (𝓐 MaxExi (B _ i))) =>
              let u := max_um_inter_prop 𝓐 B I (𝓐 Max (B _ i)) hBI hR₂max (
                Exists.intro i (And.intro (hi) (
                  max_po_prop 𝓐 (B _ i) h𝓐 (hr₂)
                ))
              )
              let v := Exists.intro (𝓐 Max (B _ i)) u
              And.intro (v) (
                max_um_unique 𝓐 (⋂[ i in I ] B at i) (𝓐 Max (⋂[ i in I ] B at i)) (𝓐 Max (B _ i)) h𝓐 (
                  max_po_prop 𝓐 (⋂[ i in I ] B at i) h𝓐 v) (u)

              )
theorem min_inter_prop : ∀ 𝓐 B I i, i ∈ I → (PartOrd 𝓐) → (B IndxFun I) → ((𝓐 Min (B _ i)) ∈ (⋂[ i in I ] B at i)) → (𝓐 MinExi (B _ i)) → ((𝓐 MinExi (⋂[ i in I ] B at i)) ∧ ((𝓐 Min (⋂[ i in I ] B at i)) = 𝓐 Min (B _ i))) :=
  fun (𝓐 B I i) =>
    fun (hi : i ∈ I) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBI : (B IndxFun I)) =>
          fun (hR₂min : (((𝓐 Min (B _ i)) ∈ (⋂[ i in I ] B at i)))) =>
            fun (hr₂ : (𝓐 MinExi (B _ i))) =>
              let u := min_um_inter_prop 𝓐 B I (𝓐 Min (B _ i)) hBI hR₂min (
                Exists.intro i (And.intro (hi) (
                  min_po_prop 𝓐 (B _ i) h𝓐 (hr₂)
                ))
              )
              let v := Exists.intro (𝓐 Min (B _ i)) u
              And.intro (v) (
                min_um_unique 𝓐 (⋂[ i in I ] B at i) (𝓐 Min (⋂[ i in I ] B at i)) (𝓐 Min (B _ i)) h𝓐 (
                  min_po_prop 𝓐 (⋂[ i in I ] B at i) h𝓐 v) (u)
              )
theorem max_un_prop : ∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) → (∀ i j ∈ I; (𝓐 Max (B _ i)) = (𝓐 Max (B _ j))) → ((𝓐 MaxExi (⋃[ i in I ] B at i)) ∧ (∀ s ∈ I; (𝓐 Max ((⋃[ i in I ] B at i))) = (𝓐 Max (B _ s)))) :=
  fun (𝓐 B I) =>
    fun (hI : (I ≠ ∅)) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (himax : ((∀ i ∈ I; (𝓐 MaxExi (B _ i))))) =>
            fun (hij : (∀ i j ∈ I; (𝓐 Max (B _ i)) = (𝓐 Max (B _ j)))) =>
              let hIpr := Iff.mp (set_non_empty_iff_non_empty I) hI
              Exists.elim hIpr (
                fun (s) =>
                  fun (hs : s ∈ I) =>
                    let u := max_um_un_prop 𝓐 B I (𝓐 Max (B _ s)) hI hBI (
                      fun (i) =>
                        fun (hi : i ∈ I) =>
                          let v := hij i hi s hs
                          eq_subst (fun (t) => is_maximum 𝓐 (B _ i) t) (𝓐 Max (B _ i)) (𝓐 Max (B _ s)) (v) (
                            max_po_prop 𝓐 (B _ i) h𝓐 (himax i hi)
                          )

                    )
                    let v := Exists.intro (𝓐 Max (B _ s)) u
                    And.intro (v) (
                      fun (t) =>
                        fun (ht : t ∈ I) =>
                          max_um_unique 𝓐 ((⋃[ i in I ] B at i)) (𝓐 Max (⋃[ i in I ] B at i)) (𝓐 Max (B _ t)) h𝓐 (
                            max_po_prop 𝓐 ((⋃[ i in I ] B at i)) h𝓐 v
                          ) (
                            eq_subst (fun (m) => is_maximum 𝓐 (⋃[ i in I ] B at i) m) (𝓐 Max (B _ s)) (
                              𝓐 Max (B _ t)) (hij s hs t ht) u
                          )

                    )
              )
theorem min_un_prop : ∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) → (∀ i j ∈ I; (𝓐 Min (B _ i)) = (𝓐 Min (B _ j))) → ((𝓐 MinExi (⋃[ i in I ] B at i)) ∧ (∀ s ∈ I; (𝓐 Min ((⋃[ i in I ] B at i))) = (𝓐 Min (B _ s)))) :=
  fun (𝓐 B I) =>
    fun (hI : (I ≠ ∅)) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (himin : ((∀ i ∈ I; (𝓐 MinExi (B _ i))))) =>
            fun (hij : (∀ i j ∈ I; (𝓐 Min (B _ i)) = (𝓐 Min (B _ j)))) =>
              let hIpr := Iff.mp (set_non_empty_iff_non_empty I) hI
              Exists.elim hIpr (
                fun (s) =>
                  fun (hs : s ∈ I) =>
                    let u := min_um_un_prop 𝓐 B I (𝓐 Min (B _ s)) hI hBI (
                      fun (i) =>
                        fun (hi : i ∈ I) =>
                          let v := hij i hi s hs
                          eq_subst (fun (t) => is_minimum 𝓐 (B _ i) t) (𝓐 Min (B _ i)) (𝓐 Min (B _ s)) (v) (
                            min_po_prop 𝓐 (B _ i) h𝓐 (himin i hi)
                          )

                    )
                    let v := Exists.intro (𝓐 Min (B _ s)) u
                    And.intro (v) (
                      fun (t) =>
                        fun (ht : t ∈ I) =>
                          min_um_unique 𝓐 ((⋃[ i in I ] B at i)) (𝓐 Min (⋃[ i in I ] B at i)) (𝓐 Min (B _ t)) h𝓐 (
                            min_po_prop 𝓐 ((⋃[ i in I ] B at i)) h𝓐 v
                          ) (
                            eq_subst (fun (m) => is_minimum 𝓐 (⋃[ i in I ] B at i) m) (𝓐 Min (B _ s)) (
                              𝓐 Min (B _ t)) (hij s hs t ht) u
                          )

                    )
              )
theorem supr_subset : ∀ 𝓐 B C, (PartOrd 𝓐) → (B ⊆ C) → (𝓐 SuprExi C) → (𝓐 SuprExi B) → (¬ ((𝓐 Supr C) . (≺(𝓐)) . (𝓐 Supr B))) :=
  fun (𝓐 B C) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      fun (hBC : (B ⊆ C)) =>
        fun (hsuprc₂ : (𝓐 SuprExi C)) =>
          fun (hsuprb₂ : (𝓐 SuprExi B)) =>
            sup_subset 𝓐 B C (𝓐 Supr C) (𝓐 Supr B) h𝓐 hBC (
              supr_po_prop 𝓐 C h𝓐 hsuprc₂
            ) (supr_po_prop 𝓐 B h𝓐 hsuprb₂)
theorem infm_subset : ∀ 𝓐 B C, (PartOrd 𝓐) → (B ⊆ C) → (𝓐 InfmExi C) → (𝓐 InfmExi B) → (¬ ((𝓐 Infm B) . (≺(𝓐)) . (𝓐 Infm C))) :=
    fun (𝓐 B C) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBC : (B ⊆ C)) =>
          fun (hinfc₂ : (𝓐 InfmExi C)) =>
            fun (hinfb₂ : (𝓐 InfmExi B)) =>
              inf_subset 𝓐 B C (𝓐 Infm C) (𝓐 Infm B) h𝓐 hBC (
                inf_po_prop 𝓐 C h𝓐 hinfc₂
              ) (inf_po_prop 𝓐 B h𝓐 hinfb₂)
theorem supr_union : ∀ 𝓐 B, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; 𝓐 SuprExi (B _ i)) → (∀ i j ∈ I; (𝓐 Supr (B _ i)) = (𝓐 Supr (B _ j))) → ((𝓐 SuprExi (⋃[i in I] B at i)) ∧(∀ s ∈ I; (𝓐 Supr (⋃[i in I] B at i)) = (𝓐 Supr (B _ s)))) :=
  fun (𝓐 B) =>
    fun (hI : (I ≠ ∅)) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hisupr : (∀ i ∈ I; 𝓐 SuprExi (B _ i))) =>
            fun (hij : (∀ i j ∈ I; (𝓐 Supr (B _ i)) = (𝓐 Supr (B _ j))) ) =>
              Exists.elim (Iff.mp (set_non_empty_iff_non_empty I) (hI)) (
                fun (i) =>
                  fun (hi : i ∈ I) =>
                    let u := sup_union 𝓐 B I (𝓐 Supr (B _ i)) hI hBI (
                      fun (t) =>
                        fun (ht : t ∈ I) =>
                          eq_subst (fun (k) => is_supremum 𝓐 (B _ t) k) (𝓐 Supr (B _ t)
                          ) (𝓐 Supr (B _ i)) (hij t ht i hi) (
                            supr_po_prop 𝓐 (B _ t) h𝓐 (hisupr t ht)
                          )
                    )
                    let v := Exists.intro (𝓐 Supr (B _ i)) u
                    And.intro (v) (
                      fun (m) =>
                        fun (hm : m ∈ I) =>
                          let res := Iff.mp (supr_po_crit 𝓐 (⋃[i in I] B at i) (𝓐 Supr (B _ m)) h𝓐 v) (
                            eq_subst (fun (k) => is_supremum 𝓐 (⋃[i in I] B at i) k) (𝓐 Supr (B _ i)) (𝓐 Supr (B _ m)) (
                              hij i hi m hm) u
                          )
                          Eq.symm (res)

                    )
              )
theorem infm_union : ∀ 𝓐 B, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; 𝓐 InfmExi (B _ i)) → (∀ i j ∈ I; (𝓐 Infm (B _ i)) = (𝓐 Infm (B _ j))) → ((𝓐 InfmExi (⋃[i in I] B at i)) ∧ (∀ s ∈ I; (𝓐 Infm (⋃[i in I] B at i)) = (𝓐 Infm (B _ s)))) :=
  fun (𝓐 B) =>
    fun (hI : (I ≠ ∅)) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hisupr : (∀ i ∈ I; 𝓐 InfmExi (B _ i))) =>
            fun (hij : (∀ i j ∈ I; (𝓐 Infm (B _ i)) = (𝓐 Infm (B _ j))) ) =>
              Exists.elim (Iff.mp (set_non_empty_iff_non_empty I) (hI)) (
                fun (i) =>
                  fun (hi : i ∈ I) =>
                    let u := inf_union 𝓐 B I (𝓐 Infm (B _ i)) hI hBI (
                      fun (t) =>
                        fun (ht : t ∈ I) =>
                          eq_subst (fun (k) => is_infimum 𝓐 (B _ t) k) (𝓐 Infm (B _ t))
                           (𝓐 Infm (B _ i)) (hij t ht i hi) (
                            inf_po_prop 𝓐 (B _ t) h𝓐 (hisupr t ht)
                          )
                    )
                    let v := Exists.intro (𝓐 Infm (B _ i)) u
                    And.intro (v) (
                      fun (m) =>
                        fun (hm : m ∈ I) =>
                          let res := Iff.mp (infm_po_crit
                           𝓐 (⋃[i in I] B at i) (𝓐 Infm (B _ m)) h𝓐 v) (
                            eq_subst (fun (k) => is_infimum 𝓐 (⋃[i in I] B at i) k) (
                              𝓐 Infm (B _ i)) (𝓐 Infm (B _ m)) (
                              hij i hi m hm) u
                          )
                          Eq.symm (res)

                    )
              )



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


theorem lro_two_sub :
∀ 𝓐 a b c d, (PartOrd 𝓐) → ( ⦗ a ; b ⦘ of 𝓐 ) ⊆ ( ⦗ c ; d ⦘ of 𝓐 ) ↔ ((c . (≼(𝓐)) . a) ∧ (d . (≼(𝓐)) . b)) :=
  fun (𝓐 a b c d) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      Iff.intro
      ()
      (
        fun (hacbd : (c . (≼(𝓐)) . a) ∧ (d . (≼(𝓐)) . b)) =>
          fun (x) =>
            fun (hx : x ∈ ⦗ a ; b ⦘ of 𝓐) =>
              let u := lro_sub_all 𝓐 a b x hx
              let u₂ := Iff.mp (lro_is_lro 𝓐 a b x u) hx
              Iff.mpr (lro_is_lro 𝓐 c d x u) (
                And.intro (
                  let u₃ := trans_R₂ 𝓐 h𝓐 c a x (sorry) (sorry)
                ) (sorry)
              )
      )


def is_lattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ x y ∈ (setPO(𝓐)); (𝓐 SuprExi ({x, y})) ∧ (𝓐 InfmExi ({x, y})))
syntax "Latt" term : term
macro_rules
| `(Latt $𝓐:term) => `(is_lattice $𝓐)


theorem boolean_Latt : ∀ A, (Latt (BoolPO A)) :=
  fun (A) =>

    And.intro (boolean_PO A) (
      fun (X) => fun (hX : X ∈ (𝒫 A)) =>
        fun (Y) => fun (hY : Y ∈ (𝒫 A)) =>
          let u := Iff.mp (boolean_set_is_boolean A X) hX
          let v := Iff.mp (boolean_set_is_boolean A Y) hY
          let v₂ := Iff.mpr (boolean_set_is_boolean A (X ∪ Y)) (
                  sub_sub_union_sub X Y A u v
                )

          let v₂₂ := setPO_is_setPO (𝒫 A) (subneq_binrel A) (sub_binrel A)

          let BR := less_eq_PO (BoolPO A)

          let v₂₁ := lesseqPO_is_lesseqPO (𝒫 A) (subneq_binrel A) (sub_binrel A)

          let AA := setPO( (BoolPO A))

          let v₂₃ := eq_subst (fun (t) => (X ∪ Y) ∈ t) (𝒫 A) (setPO( (BoolPO A) )) (Eq.symm v₂₂) v₂

          let v₃ := Iff.mpr (boolean_set_is_boolean A (X ∩ Y)) (
            subset_trans (X ∩ Y) X A (And.left (interset2sets_subset_prop X Y)) (
            Iff.mp (boolean_set_is_boolean A X) hX))

          let v₄ := union2sets_subset_prop X Y

          And.intro (
            Exists.intro (X ∪ Y) (
              upp_and_sm_upp_sup (BoolPO A) {X, Y} (X ∪ Y) (
                let u := fun (t) =>
                    fun (ht : t ∈ {X, Y}) =>
                      let a₁ := Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair X Y t) ht) (
                        fun (htx : t = X) =>
                          eq_subst (fun (m) => (m, X ∪ Y) ∈ (sub_binrel A)) X t (Eq.symm htx) (
                            Iff.mpr (NSPO_bool_pair_prop_pa A X (X ∪ Y)) (
                              And.intro (And.left v₄) (And.intro (hX) (v₂))
                            )
                          )


                      ) (
                        fun (hty : t = Y) =>
                          eq_subst (fun (m) => (m, X ∪ Y) ∈ (sub_binrel A)) Y t (Eq.symm hty) (
                            Iff.mpr (NSPO_bool_pair_prop_pa A Y (X ∪ Y)) (
                              And.intro (And.right v₄) (And.intro (hY) (v₂))
                            )
                          )


                      )

                      let a₂ := eq_subst (fun (m) => (t, X ∪ Y) ∈ m) (sub_binrel A) (BR) (Eq.symm v₂₁) (a₁)
                      Iff.mp (po_lesseq_moreeq (BoolPO(A)) (boolean_PO A) t (X ∪ Y)) a₂


                And.intro (v₂₃) (u)
              ) (
                fun (s) =>
                  fun (hS : is_upper_bound (BoolPO(A)) {X, Y} s) =>

                    sorry
              )
            )
          ) (
            Exists.intro (X ∩ Y) (
              low_and_big_low_inf (𝒫 A) {X, Y} (sub_binrel A) (X ∩ Y) (
                And.intro (v₃) (
                  fun (t) =>
                    fun (ht : t ∈ {X, Y}) =>
                      Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair X Y t) ht)
                      (
                        fun (htx : t = X) =>
                          eq_subst (fun (m) => (X ∩ Y, m) ∈ (sub_binrel A)) X t (Eq.symm htx) (
                            Iff.mpr (NSPO_bool_pair_prop_pa A (X ∩ Y) X) (
                              And.intro (
                                And.left (interset2sets_subset_prop X Y)
                              ) (And.intro (v₃) (hX))
                            )
                          )
                      )
                      (
                        fun (hty : t = Y) =>
                          eq_subst (fun (m) => (X ∩ Y, m) ∈ (sub_binrel A)) Y t (Eq.symm hty) (
                            Iff.mpr (NSPO_bool_pair_prop_pa A (X ∩ Y) Y) (
                              And.intro (
                                And.right (interset2sets_subset_prop X Y)
                              ) (And.intro (v₃) (hY))
                            )
                          )
                      )
                )
              ) (
                fun (s) =>
                  fun (hs : is_lower_bound (𝒫 A) {X, Y} (sub_binrel A) s) =>
                    Iff.mpr (NSPO_bool_pair_prop_pa A s (X ∩ Y)) (
                      And.intro (
                        let m₁ := And.right hs X (left_unordered_pair X Y)
                        let m₂ := And.right hs Y (right_unordered_pair X Y)
                        let m₃ := And.left (Iff.mp (NSPO_bool_pair_prop_pa A s X) m₁)
                        let m₄ := And.left (Iff.mp (NSPO_bool_pair_prop_pa A s Y) m₂)

                        sub_sub_inter_sub X Y s (m₃) (m₄)
                      ) (And.intro (
                        And.left hs
                      ) (v₃))
                    )
              )
            )
          )
    )


def is_complete_lattice (A R₁ R₂ : Set) : Prop := (R₁ with R₂ PO A) ∧ (∀ X, (X ⊆ A) → (R₂ SuprExi X In A))
syntax term "with" term "CompLatt" term : term
macro_rules
| `($R₁:term with $R₂:term CompLatt $A:term) => `(is_complete_lattice $A $R₁ $R₂)


theorem compl_latt_inf_crit : ∀ A R₁ R₂, ((R₁ with R₂ CompLatt A) ↔ ((R₁ with R₂ PO A) ∧ (∀ X, (X ⊆ A) → (R₂ InfmExi X In A)))) :=
  fun (A R₁ R₂) =>
    Iff.intro
    (
      fun (hR : (R₁ with R₂ CompLatt A)) =>
        let RPO := And.left hR
        And.intro (RPO) (
          fun (X) =>
            fun (hX : X ⊆ A) =>
              let suplowX := (R₂ Supr (R₂ LowBou X in A) In A)
              Exists.intro (suplowX) (

                let P := fun (z) => is_lower_bound A X R₂ z
                let v := And.right hR (R₂ LowBou X in A) (specification_set_subset P A)
                let v₂ := supr_po_prop A (R₂ LowBou X in A) R₁ R₂ RPO v
                let v₃ := And.left (Iff.mp (upp_bou_set_is_upp_bou A (R₂ LowBou X in A) R₂ suplowX) (And.left v₂))

                low_and_big_low_inf A X R₂ suplowX (

                  And.intro (v₃) (
                    fun (s) =>
                      fun (hs : s ∈ X) =>
                        let v₄ := sub_upp_low A X R₂ hX s hs
                        And.right v₂ s v₄
                  )

                ) (
                  fun (y) =>
                    fun (hy : is_lower_bound A X R₂ y) =>
                      let u := And.right hR (R₂ LowBou X in A) (specification_set_subset P A)
                      let r₁ := supr_po_prop A (R₂ LowBou X in A) R₁ R₂ RPO u
                      And.right (sup_is_upp A (R₂ LowBou X in A) R₂ (suplowX) r₁) y (Iff.mpr (low_bou_set_is_low_bou A X R₂ y)
                      hy)


                )
              )
        )
    )
    (
      fun (hR : (R₁ with R₂ PO A) ∧ (∀ X, X ⊆ A → (R₂ InfmExi X In A)) ) =>
        let RPO := And.left hR
        And.intro (RPO) (
            fun (X) =>
              fun (hX : X ⊆ A) =>
              let suplowX := (R₂ Infm (R₂ UppBou X in A) In A)
              Exists.intro (suplowX) (

                let P := fun (z) => is_upper_bound A X R₂ z
                let v := And.right hR (R₂ UppBou X in A) (specification_set_subset P A)
                let v₂ := inf_po_prop A (R₂ UppBou X in A) R₁ R₂ RPO v
                let v₃ := And.left (Iff.mp (low_bou_set_is_low_bou A (R₂ UppBou X in A) R₂ suplowX) (And.left v₂))

                upp_and_sm_upp_sup A X R₂ suplowX (

                  And.intro (v₃) (
                    fun (s) =>
                      fun (hs : s ∈ X) =>
                        let v₄ := sub_low_upp A X R₂ hX s hs
                        And.right v₂ s v₄
                  )

                ) (
                  fun (y) =>
                    fun (hy : is_upper_bound A X R₂ y) =>
                      let u := And.right hR (R₂ UppBou X in A) (specification_set_subset P A)
                      let r₁ := inf_po_prop A (R₂ UppBou X in A) R₁ R₂ RPO u
                      And.right (inf_is_low A (R₂ UppBou X in A) R₂ (suplowX) r₁) y (Iff.mpr (upp_bou_set_is_upp_bou A X R₂ y)
                      hy)


                )
              )
        )
    )



theorem compl_latt_is_latt : ∀ A R₁ R₂, ((R₁ with R₂ CompLatt A) → (R₁ with R₂ Latt A)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ CompLatt A)) =>
      And.intro (And.left hR) (
        fun (x) => fun (hx : x ∈ A) =>
          fun (y) => fun (hy : y ∈ A) =>
            let v := fun (s) =>
              fun (hs : s ∈ {x, y}) =>
                Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair x y s) hs)
                (
                  fun (hsx : s = x) =>
                    eq_subst (fun (m) => m ∈ A) x s (Eq.symm hsx) (hx)
                )
                (
                  fun (hsy : s = y) =>
                    eq_subst (fun (m) => m ∈ A) y s (Eq.symm hsy) (hy)
                )
            And.intro (
              And.right hR {x, y} (v)
            ) (
              And.right (Iff.mp (compl_latt_inf_crit A R₁ R₂) hR) {x, y} (v)
            )
      )


theorem boolean_CompLatt : ∀ A, ((subneq_binrel A) with ((sub_binrel A)) CompLatt (𝒫 A)) :=
  fun (A) =>
    And.intro (boolean_PO A) (
      fun (X) =>
        fun (hX : X ⊆ 𝒫 A) =>
          Exists.intro (⋃ X) (
            let u := sub_bool_un_mem_bool X A hX
            upp_and_sm_upp_sup (𝒫 A) X (sub_binrel A) (⋃ X) (
              And.intro (u) (
                fun (Y) =>
                  fun (hY : Y ∈ X) =>
                    let v := hX Y hY
                    Iff.mpr (NSPO_bool_pair_prop_pa A Y (⋃ X)) (
                      And.intro (elem_subset_union X Y hY) (And.intro (v) (u))
                    )
              )
            ) (
              fun (S) =>
                fun (hS : is_upper_bound (𝒫 A) X (sub_binrel A) S) =>
                  let v := And.left hS
                  Iff.mpr (NSPO_bool_pair_prop_pa A (⋃ X) S) (
                    And.intro (
                      let m := fun (t) => fun (ht : t ∈ X) =>
                        And.left (Iff.mp (NSPO_bool_pair_prop_pa A t S) (And.right hS t ht))


                      all_ss_then_union_ss X S (m)
                    ) (And.intro (u) (v))
                  )
            )
          )
    )

def monotonic_func_rel (A R f : Set) : Prop := (f Fun A To A) ∧ (∀ x y ∈ A; (x . R . y) → ((f⦅x⦆) . R . (f⦅y⦆)))
noncomputable def fix_point_set (A f) := {x ∈ A | f⦅x⦆ = x}
syntax term "FixOn" term : term
macro_rules
| `($f:term FixOn $A) => `(fix_point_set $A $f)


theorem Knaster_Tarski_lemma₁ : ∀ A R₁ R₂ f, (R₁ with R₂ CompLatt A) → (monotonic_func_rel A R₂ f) → (R₂ MaxExi (f FixOn A)) :=
  fun (A R₁ R₂ f) =>
    fun (hR : (R₁ with R₂ CompLatt A)) =>
      fun (hmon : (monotonic_func_rel A R₂ f)) =>
          let P := fun (z) => (f⦅z⦆ = z)
          let P₂ := fun (x) => (x . R₂ . (f⦅x⦆))
          let S := {x ∈ A | (x . R₂ . (f⦅x⦆) )}
          let Z := R₂ Supr S In A
          let first := specification_set_subset P₂ A
          let u := And.right hR (S) first
          let v := supr_po_prop A (S) R₁ R₂ (And.left hR) u
          let RPO := And.left hR

          Exists.intro Z (

            let v₁ := And.left v
            let Q := fun (z) => is_upper_bound A (S) R₂ z
            let ZinA := specification_set_subset Q A Z v₁

            let m₁ := And.right (And.right (And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) RPO))))
            let second := fun (x) =>
              fun (hx : x ∈ S) =>
                let h₀ := first x hx
                let h₁ := And.right (sup_is_upp A S R₂ Z v) x hx
                let h₂ := And.right (hmon) x h₀ Z ZinA h₁
                let h₃ := And.right m₁
                let h₄ := And.right (Iff.mp (spec_is_spec P₂ A x) hx)
                h₃ x (f⦅x⦆) (f⦅Z⦆) (And.intro (h₄) (h₂))


            let zinfix : Z ∈ (f FixOn A) := Iff.mpr (spec_is_spec P A Z) (
              And.intro (
                ZinA

              ) (


                  let third := val_in_B f A A (And.left hmon) Z ZinA
                  let fourth := And.intro third second
                  let fifth := sup_is_sm_upp A S R₂ Z v (f⦅Z⦆) fourth

                  let sixth := And.right hmon Z ZinA (f⦅Z⦆) third fifth
                  let seventh := Iff.mpr (spec_is_spec P₂ A (f⦅Z⦆)) (
                    And.intro third (sixth)
                  )

                  let eighth := And.right (sup_is_upp A S R₂ Z v) (f⦅Z⦆) seventh

                  And.left m₁ (f⦅Z⦆) Z (And.intro (eighth) (fifth))
                )
            )

            And.intro (zinfix) (
              fun (y) =>
                fun (hy : y ∈ (f FixOn A)) =>
                  And.right (sup_is_upp A S R₂ Z v) y (

                    let yinA := specification_set_subset P A y hy
                    let fyinA := val_in_B f A A (And.left hmon) y yinA
                    Iff.mpr (spec_is_spec P₂ A y) (
                      And.intro (yinA) (part_ord_pair_prop_eqR₂ A R₁ R₂ RPO y yinA (f⦅y⦆) fyinA (
                        Eq.symm (And.right (Iff.mp (spec_is_spec P A y) hy))
                      ))
                    )
                  )

            )
          )


theorem Knaster_Tarski_lemma₂ : ∀ A R₁ R₂ f, (R₁ with R₂ CompLatt A) → (monotonic_func_rel A R₂ f) → ((f FixOn A) ≠ ∅) :=
  fun (A R₁ R₂ f) =>
    fun (hR : (R₁ with R₂ CompLatt A)) =>
      fun (hmon : (monotonic_func_rel A R₂ f)) =>
        Iff.mpr (set_non_empty_iff_non_empty ((f FixOn A))) (

          Exists.elim (Knaster_Tarski_lemma₁ A R₁ R₂ f hR hmon) (
            fun (x) =>
              fun (hx : is_maximum R₂ (f FixOn A) x) =>
                Exists.intro x (And.left hx)
          )
        )
