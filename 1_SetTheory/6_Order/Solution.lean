import «Header»


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

open Classical

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



theorem strcon_iff_wkcon_refl :
∀ A R, binary_relation_on A R → ((str_conn R A) ↔ (wkl_conn R A ∧ refl R A)) :=
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



theorem emp_refl_irrefl :
∀ A R, binary_relation_on A R → ((A = ∅) ↔ (refl R A ∧ irrefl R)) :=
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


theorem emp_symm_asymm :
∀ A R, binary_relation_on A R → ((R = ∅) ↔ (symm R ∧ asymm R)) :=
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



theorem trans_irrefl_antisymm :
∀ A R, binary_relation_on A R → (transit R) → (irrefl R) → (antisymm R) :=
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


theorem trans_irrefl_asymm :
∀ A R, binary_relation_on A R → (transit R) → (irrefl R) → (asymm R) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      fun (htr : (transit R)) =>
        fun (hirr : (irrefl R)) =>
          Iff.mpr (assym_iff_antisymm_irrefl A R hAR) (
            And.intro (trans_irrefl_antisymm A R hAR htr hirr) (hirr)
          )


theorem refl_symm_antisymm :
∀ A R, binary_relation_on A R → (((refl R A) ∧ (symm R) ∧ (antisymm R)) ↔ (R = (id_ A))) :=
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


theorem symm_compos_prop : ∀ P Q, (P BinRelOn A) → (Q BinRelOn A) → (symm P) → (symm Q) → (((P ∘ Q)⁻¹) = (Q ∘ P)) :=
  fun (P Q) =>
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


theorem irrefl_inr_right : ∀ P Q, (irrefl Q) → (irrefl (P ∩ Q)) :=
  fun (P Q) =>
    fun (hirreflQ : (irrefl Q)) =>
      fun (x) =>
        fun (hx : (x . (P ∩ Q) . x)) =>
          (hirreflQ x) (And.right (Iff.mp (intersect_2sets_prop P Q (x, x)) (hx)))


theorem symm_inr : ∀ P Q, (symm P) → (symm Q) → (symm (P ∩ Q)) :=
  fun (P Q) =>
    fun (hsymmP : (symm P)) =>
      fun (hsymmQ : (symm Q)) =>
        fun (x y) =>
          fun (hxyPQ : (x . (P ∩ Q) . y)) =>
            let u := Iff.mp (intersect_2sets_prop P Q (x, y)) hxyPQ
            Iff.mpr (intersect_2sets_prop P Q (y, x)) (
              And.intro (hsymmP x y (And.left u)) (hsymmQ x y (And.right u))
            )


theorem antisym_inr_left : ∀ P Q, (antisymm P) → (antisymm (P ∩ Q)) :=
  fun (P Q) =>
    fun (hantisymmP : (antisymm P)) =>
        fun (x y) =>
          fun (hxy : (x . (P ∩ Q) . y) ∧ (y . (P ∩ Q) . x)) =>
            let u := Iff.mp (intersect_2sets_prop P Q (x, y)) (And.left hxy)
            let v := Iff.mp (intersect_2sets_prop P Q (y, x)) (And.right hxy)
            hantisymmP x y (And.intro (And.left u) (And.left v))


theorem antisym_inr_right : ∀ P Q, (antisymm Q) → (antisymm (P ∩ Q)) :=
  fun (P Q) =>
    fun (hantisymmP : (antisymm Q)) =>
        fun (x y) =>
          fun (hxy : (x . (P ∩ Q) . y) ∧ (y . (P ∩ Q) . x)) =>
            let u := Iff.mp (intersect_2sets_prop P Q (x, y)) (And.left hxy)
            let v := Iff.mp (intersect_2sets_prop P Q (y, x)) (And.right hxy)
            hantisymmP x y (And.intro (And.right u) (And.right v))


theorem trans_inr : ∀ P Q, (transit P) → (transit Q) → (transit (P ∩ Q)) :=
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



noncomputable def str (A R) := R \ (id_ A)
noncomputable def nonstr (A R) := R ∪ (id_ A)


def spo_then_nspo : ∀ A R, (R SPO A) → ((nonstr A R) NSPO A) :=
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


def nspo_then_spo : ∀ A R, (R NSPO A) → ((str A R) SPO A) :=
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



noncomputable def SPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R SPO A) }
noncomputable def NSPOS (A : Set) := { R ∈ 𝒫 (A × A) | (R NSPO A) }


theorem SPOS_NSPOS_equinum : ∀ A, (SPOS A) ~ (NSPOS A) :=
  fun (A) =>
    let φ := lam_fun (SPOS A) (NSPOS A) (nonstr A)

    Exists.intro φ (

      Iff.mp (rev_criterion φ (SPOS A) (NSPOS A)) (

        let func_prop₁ := lam_then_fun_prop (nonstr A) (SPOS A) (NSPOS A) (
          fun (R) =>
            fun (hR : R ∈ (SPOS A)) =>
              Iff.mpr (specification_set_is_specification (fun (P) => (P NSPO A)) (𝒫 (A × A)) (nonstr A R)) (
                let spo_R :=Iff.mp (specification_set_is_specification (fun (P) => (P SPO A)) (𝒫 (A × A)) R) hR
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
                  Iff.mpr (specification_set_is_specification (fun (P) => (P SPO A)) (𝒫 (A × A)) (str A R)) (
                    let nspo_R := Iff.mp (specification_set_is_specification (fun (P) => (P NSPO A)) (𝒫 (A × A)) R) hR
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
                      let spo_x := And.right (Iff.mp (specification_set_is_specification (fun (R) => R SPO A)
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
                            specification_set_is_specification (fun (R) => R NSPO A) (𝒫 (A × A)) (nonstr A x)) (
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
                      let nspo_x := And.right (Iff.mp (specification_set_is_specification (fun (R) => R NSPO A)
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
                            specification_set_is_specification (fun (R) => R SPO A) (𝒫 (A × A)) (str A x)) (
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

def is_partial_order (A R₁ R₂ : Set) : Prop := (A ≠ ∅) ∧ (R₁ SPO A) ∧ (R₂ = nonstr A R₁)
syntax term "with" term "PO" term  : term
macro_rules
| `($R₁:term with $R₂:term PO $A:term) => `(is_partial_order $A $R₁ $R₂)


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


theorem part_ord_pair_prop :
∀ A R₁ R₂, (R₁ with R₂ PO A) →
(∀ x y ∈ A; ((x . R₁ . y) ↔ ((x . R₂ . y) ∧ x ≠ y)) ∧ ((x . R₂ . y) ↔ ((x . R₁ . y) ∨ x = y))) :=
  fun (A R₁ R₂) =>
    fun (hRA : (R₁ with R₂ PO A)) =>
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


theorem part_ord_pair_prop_R₁_A :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₁ . y) → ((x ∈ A) ∧ (y ∈ A))) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (x y) =>
        fun (hxy : (x . R₁ . y)) =>
          let u := And.left (And.left (And.right hR)) (x, y) hxy
          Iff.mp (cartesian_product_pair_prop A A x y) u


theorem part_ord_pair_prop_R₂_A :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₂ . y) → ((x ∈ A) ∧ (y ∈ A))) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (x y) =>
        fun (hxy : (x . R₂ . y)) =>
          let u := And.left (And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR))) (x, y) hxy
          Iff.mp (cartesian_product_pair_prop A A x y) u



theorem part_ord_pair_prop_R₁R₂ :
∀ A R₁ R₂, (R₁ with R₂ PO A) → ∀ x y, ((x . R₁ . y) → ((x . R₂ . y))) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (x y) =>
        fun (hxy : (x . R₁ . y)) =>
          let u₁ := And.left (And.left (And.right hR)) (x, y) hxy
          let u₂ := Iff.mp (cartesian_product_pair_prop A A x y) u₁
          And.left (Iff.mp (And.left (part_ord_pair_prop A R₁ R₂ hR x (And.left u₂) y (And.right u₂))) hxy)


theorem part_ord_pair_prop_R₁neq :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y ∈ A; (x . R₁ . y) → (x ≠ y)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (x) => fun (hx : x ∈ A) =>
        fun (y) => fun (hy : y ∈ A) =>
          fun (hxy : (x . R₁ . y)) =>
              And.right (Iff.mp (And.left (part_ord_pair_prop A R₁ R₂ hR x hx y hy)) hxy)


theorem part_ord_pair_prop_eqR₂ :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y ∈ A; (x = y) → (x . R₂ . y)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (x) => fun (hx : x ∈ A) =>
        fun (y) => fun (hy : y ∈ A) =>
          fun (hxy : (x = y)) =>
            Iff.mpr (And.right (part_ord_pair_prop A R₁ R₂ hR x hx y hy)) (
              Or.inr hxy
            )


theorem part_ord_pair_prop_neqR₂R₁ :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, ((x . R₂ . y) ∧ (x ≠ y)) → ((x . R₁ . y))) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (x y) =>
        fun (hxyR₂ : (x . R₂ . y) ∧ (x ≠ y)) =>
          let u₁ := And.left (And.left (And.right (And.right (Iff.mp (part_ord_crit A R₁ R₂) hR)))) (x, y) (And.left hxyR₂)
          let u₂ := Iff.mp (cartesian_product_pair_prop A A x y) u₁
          let u₃ := Iff.mp (And.right (part_ord_pair_prop A R₁ R₂ hR x (And.left u₂) y (And.right u₂))) (And.left hxyR₂)
          Or.elim u₃
          (
            fun (hxyR₁ : (x . R₁ . y)) =>
              hxyR₁
          )
          (
            fun (hxy : (x = y)) =>
              False.elim (And.right hxyR₂ (hxy))
          )


theorem irrefl_R₁ :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x, ¬ (x . R₁ . x)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
        And.left (And.right (And.left (And.right hR)))


theorem asymm_R₁ :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₁ . y) → ¬ (y . R₁ . x)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      let u := And.left (And.right hR)
      spo_asymm A R₁ u


theorem trans_R₁ :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y z, (x . R₁ . y) → (y . R₁ . z) → (x . R₁ . z)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      let u := And.left (And.right hR)
      let v := And.right (And.right u)
      fun (x y z) =>
        fun (hxy : (x . R₁ . y)) =>
          fun (hyz : (y . R₁ . z)) =>
            v x y z (And.intro hxy hyz)


theorem refl_R₂ :
 ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x ∈ A; (x . R₂ . x)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
        And.left (And.right (And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR))))


theorem antisymm_R₂ :
 ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, (x . R₂ . y) → (y . R₂ . x) → (x = y)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      let u := And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR))
      let v := And.left (And.right (And.right u))
      fun (x y) =>
        fun (hxyR₂ : (x . R₂ . y)) =>
          fun (hyxR₂ : (y . R₂ . x)) =>
            v x y (And.intro (hxyR₂) (hyxR₂))



theorem trans_R₂ :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y z, (x . R₂ . y) → (y . R₂ . z) → (x . R₂ . z)) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      let u := And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR))
      let v := And.right (And.right (And.right u))
      fun (x y z) =>
        fun (hxyR₂ : (x . R₂ . y)) =>
          fun (hyzR₂ : (y . R₂ . z)) =>
            v x y z (And.intro hxyR₂ hyzR₂)


theorem stabil_R₂ :
∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y z, (x . R₂ . y) → (y . R₂ . z) → (x = z) → ((x = y) ∧ (y = z))) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
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
                            let u := part_ord_pair_prop_neqR₂R₁ A R₁ R₂ hR y z (And.intro (hyz) (hyzneq₂))
                            let v := eq_subst (fun (t) => (t, z) ∈ R₁) y x (Eq.symm hxyeq) (u)
                            let m := part_ord_pair_prop_R₁_A A R₁ R₂ hR x z v
                            let t := part_ord_pair_prop_R₁neq A R₁ R₂ hR x (And.left m) z (And.right m) v
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
                            let u := part_ord_pair_prop_neqR₂R₁ A R₁ R₂ hR x y (And.intro (hxy) (hxyneq))
                            let v := eq_subst (fun (t) => (x, t) ∈ R₁) y z (hyzeq) (u)
                            let t := eq_subst (fun (t) => (x, t) ∈ R₁) z x (Eq.symm (hxz)) (v)
                            irrefl_R₁ A R₁ R₂ hR x t

                        )
                      ) (hyzeq)
                  )
                  (
                    fun (hnyzeq : y ≠ z) =>
                      let u := part_ord_pair_prop_neqR₂R₁ A R₁ R₂ hR y z (And.intro (hyz) (hnyzeq))
                      let v := part_ord_pair_prop_neqR₂R₁ A R₁ R₂ hR x y (And.intro (hxy) (hxyneq))
                      let s := trans_R₁ A R₁ R₂ hR x y z v u
                      let t := eq_subst (fun (t) => (x, t) ∈ R₁) z x (Eq.symm (hxz)) (s)

                     False.elim ( irrefl_R₁ A R₁ R₂ hR x t)
                  )
              )


theorem no_symm_R₁_R₂ : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y, ¬ ((x . R₁ . y) ∧ (y . R₂ . x))) :=
  fun (A R₁ R₂) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (x y) =>
        fun (hxy : (x . R₁ . y) ∧ (y . R₂ . x)) =>
          let u := And.left hxy
          let v := part_ord_pair_prop_R₁R₂ A R₁ R₂ hR x y u
          let t := antisymm_R₂ A R₁ R₂ hR x y v (And.right hxy)
          irrefl_R₁ A R₁ R₂ hR x (
            eq_subst (fun (t) => (x . R₁ . t)) y x (Eq.symm (t)) (u)
          )





noncomputable def sub_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊆ C ∧ z = (B, C) }
noncomputable def subneq_binrel (A) := {z ∈ (𝒫 A) × (𝒫 A) | ∃ B C, B ⊊ C ∧ z = (B, C) }

theorem NSPO_bool_pair_prop : ∀ A, ∀ B C ∈ 𝒫 A; (B, C) ∈ (sub_binrel A) ↔ (B ⊆ C) :=
  fun (A) =>
    fun (B) =>
      fun (hB : B ∈ 𝒫 A) =>
        fun (C) =>
          fun (hC : C ∈ 𝒫 A) =>
            Iff.intro
            (
              fun (hbc : (B, C) ∈ (sub_binrel A)) =>
                let u := And.right (Iff.mp (specification_set_is_specification (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A))
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
                Iff.mpr (specification_set_is_specification (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) (B, C)) (
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
                let u := And.right (Iff.mp (specification_set_is_specification (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A))
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
                Iff.mpr (specification_set_is_specification (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) (B, C)) (
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
        let u := And.left (Iff.mp (specification_set_is_specification (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C))
        ((𝒫 A) × (𝒫 A)) (B, C)) hbc)
        let v := Iff.mp (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) u
        And.intro (Iff.mp (NSPO_bool_pair_prop A B (And.left v) C (And.right v)) hbc) (v)
    )
    (
      fun (hbc : (B ⊆ C ∧ B ∈ 𝒫 A ∧ C ∈ 𝒫 A)) =>
        Iff.mpr (specification_set_is_specification (fun (P) => ∃ B C, B ⊆ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) (B, C)) (
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
        let u := And.left (Iff.mp (specification_set_is_specification (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C))
        ((𝒫 A) × (𝒫 A)) (B, C)) hbc)
        let v := Iff.mp (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) u
        And.intro (Iff.mp (SPO_bool_pair_prop A B (And.left v) C (And.right v)) hbc) (v)
    )
    (
      fun (hbc : (B ⊊ C ∧ B ∈ 𝒫 A ∧ C ∈ 𝒫 A)) =>
        Iff.mpr (specification_set_is_specification (fun (P) => ∃ B C, B ⊊ C ∧ P = (B, C)) ((𝒫 A) × (𝒫 A)) (B, C)) (
          And.intro (Iff.mpr (cartesian_product_pair_prop (𝒫 A) (𝒫 A) B C) (And.intro (And.left (And.right hbc)) (
            And.right (And.right hbc)
          ))) (
            Exists.intro B (Exists.intro C (And.intro (And.left hbc) (Eq.refl (B, C))))
          )
        )
    )


theorem boolean_PO : ∀ A, ((subneq_binrel A) with ((sub_binrel A)) PO (𝒫 A)) :=
  fun (A) =>
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


theorem inv_is_PO : ∀ A R₁ R₂, (R₁ with R₂ PO A) → ((R₁⁻¹) with (R₂⁻¹) PO A) :=
  fun (A R₁ R₂) =>
    fun (hAR : (R₁ with R₂ PO A)) =>
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


theorem inter_is_PO : ∀ A P₁ P₂ Q₁ Q₂, (P₁ with P₂ PO A) → (Q₁ with Q₂ PO A) → ((P₁ ∩ Q₁) with (P₂ ∩ Q₂) PO A) :=
  fun (A P₁ P₂ Q₁ Q₂) =>
    fun (hP : (P₁ with P₂ PO A)) =>
      fun (hQ : (Q₁ with Q₂ PO A)) =>
        let u := And.left (And.left (And.right hP))
        let vP := And.right (And.left (And.right hP))
        let sP := And.right (And.right hP)
        let sQ := And.right (And.right hQ)
        let vQ := And.right (And.left (And.right hQ))
        let reflP₂ := refl_R₂ A P₁ P₂ hP
        let first := And.left (And.left (And.right (Iff.mp (part_ord_nspo_crit A P₁ P₂) hP)))
        And.intro (And.left hP) (
          And.intro (And.intro (int_binon_left A P₁ Q₁ (u)) (
            And.intro (irrefl_int_left P₁ Q₁ (And.left vP)) (
              trans_inr P₁ Q₁ (And.right vP) (And.right vQ)
            )
          )) (
            let u₁ := eq_subst (fun (t) => P₂ ∩ Q₂ = t ∩ Q₂) P₂ (nonstr A P₁) (sP) (Eq.refl (P₂ ∩ Q₂))
            let u₂ := eq_subst (fun (t) => (nonstr A P₁) ∩ Q₂ = (nonstr A P₁) ∩ t) Q₂ (nonstr A Q₁) (sQ) (
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
                                      let Q_irr := irrefl_R₁ A Q₁ Q₂ hQ
                                      let Q_bin := And.left (And.left (And.right hQ))
                                      let Q_irr_crit := Iff.mp (irrefl_crit A Q₁ Q_bin) Q_irr


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




def is_maximal (R x : Set) : Prop := ∀ y, ¬ (x . R . y)
def is_minimal (R x : Set) : Prop := ∀ y, ¬ (y . R . x)
def is_maximal_sub (R B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (x . R . y))
def is_minimal_sub (R B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; ¬ (y . R . x))
def is_maximum (R A x : Set) : Prop := ∀ y ∈ A; (y . R . x)
def is_minimum (R A x : Set) : Prop := ∀ y ∈ A; (x . R . y)
def is_maximum_sub (R B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (y . R . x))
def is_minimum_sub (R B x : Set) : Prop := (x ∈ B) ∧ (∀ y ∈ B; (x . R . y))
def noncomparable (R x y : Set) : Prop := (¬ (x . R . y)) ∧ (¬ (y . R . x))


noncomputable def max_set (A R) := {z ∈ A | is_maximal R z}
noncomputable def min_set (A R) := {z ∈ A | is_minimal R z}
noncomputable def max_set_sub (A B R) := {z ∈ A | is_maximal_sub R B z }
noncomputable def min_set_sub (A B R) := {z ∈ A | is_minimal_sub R B z }


theorem max_set_is_max_set : ∀ A R x, ((x ∈ (max_set A R)) ↔ (x ∈ A ∧ is_maximal R x)) :=
  fun (A R x) =>
    Iff.intro
    (
      fun (hxmax : x ∈ (max_set A R) ) =>
        Iff.mp (specification_set_is_specification (fun (t) => is_maximal R t) A x) hxmax
    )
    (
      fun (hxmax : (x ∈ A ∧ is_maximal R x)) =>
        Iff.mpr (specification_set_is_specification (fun (t) => is_maximal R t) A x) hxmax
    )



theorem min_set_is_min_set : ∀ A R x, ((x ∈ (min_set A R)) ↔ (x ∈ A ∧ is_minimal R x)) :=
  fun (A R x) =>
    Iff.intro
    (
      fun (hxmin : x ∈ (min_set A R) ) =>
        Iff.mp (specification_set_is_specification (fun (t) => is_minimal R t) A x) hxmin
    )
    (
      fun (hxmin : (x ∈ A ∧ is_minimal R x)) =>
        Iff.mpr (specification_set_is_specification (fun (t) => is_minimal R t) A x) hxmin
    )


theorem max_set_sub_is_max_set_sub : ∀ A B R x, (B ⊆ A) → ((x ∈ (max_set_sub A B R)) ↔ (is_maximal_sub R B x)) :=
  fun (A B R x) =>
      fun (hBA : B ⊆ A) =>
        Iff.intro
        (
          fun (hxmax : (x ∈ (max_set_sub A B R))) =>
            And.right (Iff.mp (specification_set_is_specification (fun (t) => is_maximal_sub R B t) A x) hxmax)

        )
        (
          fun (hxmax : (is_maximal_sub R B x)) =>
            Iff.mpr (specification_set_is_specification (fun (t) => is_maximal_sub R B t) A x) (
              And.intro (hBA x (And.left hxmax)) (hxmax)
            )

        )



theorem min_set_sub_is_min_set_sub : ∀ A B R x, (B ⊆ A) → ((x ∈ (min_set_sub A B R)) ↔ (is_minimal_sub R B x)) :=
  fun (A B R x) =>
      fun (hBA : B ⊆ A) =>
        Iff.intro
        (
          fun (hxmin : (x ∈ (min_set_sub A B R))) =>
            And.right (Iff.mp (specification_set_is_specification (fun (t) => is_minimal_sub R B t) A x) hxmin)

        )
        (
          fun (hxmin : (is_minimal_sub R B x)) =>
            Iff.mpr (specification_set_is_specification (fun (t) => is_minimal_sub R B t) A x) (
              And.intro (hBA x (And.left hxmin)) (hxmin)
            )

        )






theorem PO_noncomp : ∀ A R₁ R₂, (R₁ with R₂ PO A) → (∀ x y ∈ A; (noncomparable R₂ x y) ↔ (x ≠ y ∧ (noncomparable R₁ x y))) :=
  fun (A R₁ R₂) =>
    fun (hRA : (R₁ with R₂ PO A)) =>
      fun (x) =>
        fun (hx : x ∈ A) =>
          fun (y) =>
            fun (hy : y ∈ A) =>
              Iff.intro
              (
                fun (hxy : (noncomparable R₂ x y)) =>
                  And.intro (
                    fun (hxyeq : (x = y)) =>
                      And.left hxy (
                        part_ord_pair_prop_eqR₂ A R₁ R₂ hRA x hx y hy (hxyeq)
                      )
                  ) (And.intro (
                    fun (xhyR₁ : (x . R₁ . y)) =>
                      And.left hxy (
                        part_ord_pair_prop_R₁R₂ A R₁ R₂ hRA x y xhyR₁
                      )
                  ) (
                    fun (xhyR₁ : (y . R₁ . x)) =>
                    (And.right hxy) (part_ord_pair_prop_R₁R₂ A R₁ R₂ hRA y x xhyR₁)
                  ))
              )
              (
                fun (hxy : (x ≠ y) ∧ (noncomparable R₁ x y)) =>
                  And.intro (

                    fun (hxyR₁ : (x . R₂ . y)) =>
                      And.left (And.right hxy) (
                        part_ord_pair_prop_neqR₂R₁ A R₁ R₂ hRA x y (And.intro (hxyR₁) (And.left hxy))
                      )

                  ) (
                    fun (hxyR₂ : (y . R₂ . x)) =>
                      And.right (And.right hxy) (
                        part_ord_pair_prop_neqR₂R₁ A R₁ R₂ hRA y x (And.intro (hxyR₂) (
                          fun (hyx : y = x) =>
                            And.left hxy (Eq.symm hyx)
                          ))
                      )
                  )
              )


theorem min_max_inv_al : ∀ R x, (BinRel R) → ((is_minimal R x) ↔ (is_maximal (R⁻¹) x)) :=
  fun (R x) =>
    fun (hR : (BinRel R)) =>
      Iff.intro
      (
        fun (hmin : (is_minimal R x)) =>
          fun (y) =>
            fun (hy : (x . (R⁻¹) . y)) =>
              let u := Iff.mpr (inv_pair_prop R hR y x) hy
              hmin y u
      )
      (
        fun (hmax : (is_maximal (R⁻¹) x)) =>
          fun (y) =>
            fun (hy : (y . R . x)) =>
              let u := Iff.mp (inv_pair_prop R hR y x) hy
              hmax y u

      )

theorem min_max_sub_inv_al : ∀ R B x, (BinRel R) → ((is_minimal_sub R B x) ↔ (is_maximal_sub (R⁻¹) B x)) :=
  fun (R B x) =>
    fun (hR : (BinRel R)) =>
      Iff.intro
      (
        fun (hminsub : (is_minimal_sub R B x)) =>
          And.intro (And.left hminsub) (
            fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hy : (x . (R⁻¹) . y)) =>
                  let u := Iff.mpr (inv_pair_prop R hR y x) hy
                  (And.right hminsub) y hyB u
          )
      )
      (
        fun (hmaxsub : (is_maximal_sub (R⁻¹) B x)) =>
          And.intro (And.left hmaxsub) (
            fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hy : (y . R . x)) =>
                    let u := Iff.mp (inv_pair_prop R hR y x) hy
                    (And.right hmaxsub) y hyB u
          )
      )


theorem max_min_inv_al : ∀ R x, (BinRel R) → ((is_maximal R x) ↔ (is_minimal (R⁻¹) x)) :=
  fun (R x) =>
    fun (hR : (BinRel R)) =>
      let u := min_max_inv_al (R⁻¹) x (inv_is_rel R (hR))
      let v := eq_subst (fun (t) => ( is_minimal (R⁻¹) x ↔ is_maximal (t) x) ) ((R⁻¹)⁻¹) R (inv_prop R hR) (u)
      Iff.intro (Iff.mpr v) (Iff.mp v)


theorem max_min_sub_inv_al : ∀ R B x, (BinRel R) → ((is_maximal_sub R B x) ↔ (is_minimal_sub (R⁻¹) B x)) :=
  fun (R B x) =>
    fun (hR : (BinRel R)) =>
      let u := min_max_sub_inv_al (R⁻¹) B x (inv_is_rel R (hR))
      let v := eq_subst (fun (t) => ( is_minimal_sub (R⁻¹) B  x ↔ is_maximal_sub (t) B x) ) ((R⁻¹)⁻¹) R (inv_prop R hR) (u)

      Iff.intro (Iff.mpr v) (Iff.mp v)



theorem min_max_inv_um : ∀ A R x, (BinRel R) → ((is_minimum R A x) ↔ (is_maximum (R⁻¹) A x)) :=
  fun (A R x) =>
    fun (hR : (BinRel R)) =>
      Iff.intro
      (
        fun (hminsub : (is_minimum R A x)) =>
            fun (y) =>
              fun (hy : y ∈ A) =>
                Iff.mp (inv_pair_prop R (hR) x y) (
                  hminsub y hy
                )
      )
      (
        fun (hmaxsub : (is_maximum (R⁻¹) A x)) =>
          fun (y) =>
            fun (hy : y ∈ A) =>
              Iff.mpr (inv_pair_prop R hR x y) (
                hmaxsub y hy
              )
      )


theorem min_max_sub_inv_um : ∀ R B x, (BinRel R) → ((is_minimum_sub R B x) ↔ (is_maximum_sub (R⁻¹) B x)) :=
  fun (R B x) =>
    fun (hR : (BinRel R)) =>
      Iff.intro
      (
        fun (hminsub : (is_minimum_sub R B x)) =>
          let u := And.left hminsub
          And.intro (u) (
            fun (y) =>
              fun (hy : y ∈ B) =>
                Iff.mp (inv_pair_prop R (hR) x y) (
                  And.right hminsub y hy
                )
          )
      )
      (
        fun (hmaxsub : (is_maximum_sub (R⁻¹) B x)) =>
          let u := And.left hmaxsub
          And.intro u (
            fun (y) =>
              fun (hy : y ∈ B) =>
                Iff.mpr (inv_pair_prop R hR x y) (
                  And.right hmaxsub y hy
                )
          )
      )


theorem max_min_inv_um : ∀ A R x, (BinRel R) → ((is_maximum R A x) ↔ (is_minimum (R⁻¹) A x)) :=
  fun (A R x) =>
    fun (hR : (BinRel R)) =>
      let u := min_max_inv_um A (R⁻¹) x (inv_is_rel R hR)
      let v := eq_subst (fun (t) => is_minimum (inv R) A x ↔ is_maximum (t) A x) ((R⁻¹)⁻¹) R (inv_prop R hR) (u)
      Iff.intro (Iff.mpr v) (Iff.mp v)

theorem max_min_sub_inv_um : ∀ R B x, (BinRel R) → ((is_maximum_sub R B x) ↔ (is_minimum_sub (R⁻¹) B x)) :=
  fun (R B x) =>
    fun (hR : (BinRel R)) =>
      let u := min_max_sub_inv_um (R⁻¹) B x (inv_is_rel R hR)
      let v := eq_subst (fun (t) => is_minimum_sub (inv R) B x ↔ is_maximum_sub (t) B x) ((R⁻¹)⁻¹) R (inv_prop R hR) (u)
      Iff.intro (Iff.mpr v) (Iff.mp v)


theorem min_max_set_inv_sub : ∀ A B R, (BinRel R) → (B ⊆ A) → (max_set_sub A B R = min_set_sub A B (R⁻¹)) :=
  fun (A B R) =>
    fun (hR : (BinRel R)) =>
      fun (hBA : B ⊆ A) =>
        extensionality (max_set_sub A B R) (min_set_sub A B (R⁻¹)) (
          fun (t) =>
            Iff.intro
            (
              fun (ht : t ∈ (max_set_sub A B R)) =>
                let u := Iff.mp (max_set_sub_is_max_set_sub A B R t hBA) ht
                let v := Iff.mp (max_min_sub_inv_al R B t hR) u
                Iff.mpr (min_set_sub_is_min_set_sub A B (R⁻¹) t hBA) v
            )
            (
              fun (ht : t ∈ (min_set_sub A B (R⁻¹))) =>
                let u := Iff.mp (min_set_sub_is_min_set_sub A B (R⁻¹) t hBA) ht
                let v := Iff.mpr (max_min_sub_inv_al R B t hR) u
                Iff.mpr (max_set_sub_is_max_set_sub A B R t hBA) v
            )
        )





theorem max_min_set_inv_sub : ∀ A B R, (BinRel R) → (B ⊆ A) → (min_set_sub A B R = max_set_sub A B (R⁻¹)) :=
  fun (A B R) =>
    fun (hR : (BinRel R)) =>
      fun (hBA : B ⊆ A) =>
        let u := min_max_set_inv_sub A B (R⁻¹) (inv_is_rel R hR) hBA
        let v := eq_subst (fun (t) => max_set_sub A B (inv R) = min_set_sub A B (t)) ((R⁻¹)⁻¹) R (inv_prop R hR) (u)
        Eq.symm v


theorem min_max_set_inv : ∀ A R, (BinRel R) → (max_set A R = min_set A (R⁻¹)) :=
  fun (A R) =>
    fun (hR : (BinRel R)) =>
      extensionality (max_set A R) (min_set A (R⁻¹)) (
        fun (t) =>
          Iff.intro
          (
            fun (ht : t ∈ (max_set A R)) =>
              let u := Iff.mp (max_set_is_max_set A R t) ht
              let v := Iff.mp (max_min_inv_al R t hR) (And.right u)
              Iff.mpr (min_set_is_min_set A (R⁻¹) t) (And.intro (And.left u) v)
          )
          (
            fun (ht : t ∈ (min_set A (R⁻¹))) =>
              let u := Iff.mp (min_set_is_min_set A (R⁻¹) t) ht
              let v := Iff.mpr (max_min_inv_al R t hR) (And.right u)
              Iff.mpr (max_set_is_max_set A R t) (And.intro (And.left u) (v))
          )
      )


theorem max_min_set_inv : ∀ A R, (BinRel R) → (min_set A R = max_set A (R⁻¹)) :=
  fun (A R) =>
    fun (hR : (BinRel R)) =>
      let u := min_max_set_inv A (R⁻¹) (inv_is_rel R hR)
      let v := eq_subst (fun (t) => max_set A (inv R) = min_set A (t)) (((R)⁻¹)⁻¹) R (inv_prop R hR) (u)
      Eq.symm v



theorem max_sub_A_is_max_al : ∀ A R, (R BinRelOn A) → ∀ x ∈ A; (is_maximal R x) ↔ (is_maximal_sub R A x) :=
  fun (A R) =>
    fun (hAR : (R BinRelOn A)) =>
      fun (x) =>
        fun (hx : x ∈ A) =>
          Iff.intro
          (
            fun (hxmax : (is_maximal R x)) =>
              And.intro (hx) (
                fun (y) =>
                  fun (_ : y ∈ A) =>
                    hxmax y
              )
          )
          (
            fun (hxmax : (is_maximal_sub R A x)) =>

              fun (y) =>
                fun (hxy : (x . R . y)) =>
                  let v := And.right (Iff.mp (cartesian_product_pair_prop A A x y) (
                    hAR (x, y) hxy
                  ))
                  And.right hxmax y v hxy
          )


theorem min_sub_A_is_min_al : ∀ A R, (R BinRelOn A) → ∀ x ∈ A; (is_minimal R x) ↔ (is_minimal_sub R A x) :=
  fun (A R) =>
    fun (hAR : (R BinRelOn A)) =>
      fun (x) =>
        fun (hx : x ∈ A) =>
          Iff.intro
          (
            fun (hxmin : (is_minimal R x)) =>
              And.intro (hx) (
                fun (y) =>
                  fun (_ : y ∈ A) =>
                    hxmin y
              )
          )
          (
            fun (hxmin : (is_minimal_sub R A x)) =>

              fun (y) =>
                fun (hxy : (y . R . x)) =>
                  let v := And.left (Iff.mp (cartesian_product_pair_prop A A y x) (
                    hAR (y, x) hxy
                  ))
                  And.right hxmin y v hxy
          )





theorem max_sub_A_is_max_um : ∀ A R, ∀ x ∈ A; (is_maximum R A x) ↔ (is_maximum_sub R A x) :=
  fun (A R) =>
    fun (x) =>
      fun (hx : x ∈ A) =>
        Iff.intro
        (
          fun (hxmax : (is_maximum R A x)) =>
            And.intro (hx) (
            fun (y) =>
              fun (hy : y ∈ A) =>
                hxmax y hy
            )
        )
        (
          fun (hxmax : (is_maximum_sub R A x)) =>
              And.right hxmax
        )


theorem min_sub_A_is_min_um : ∀ A R, ∀ x ∈ A; (is_minimum R A x) ↔ (is_minimum_sub R A x) :=
  fun (A R) =>
    fun (x) =>
      fun (hx : x ∈ A) =>
        Iff.intro
        (
          fun (hxmin : (is_minimum R A x)) =>
            And.intro (hx) (
            fun (y) =>
              fun (hy : y ∈ A) =>
                hxmin y hy
            )
        )
        (
          fun (hxmin : (is_minimum_sub R A x)) =>
              And.right hxmin
        )




theorem max_set_sub_A_is_max_set : ∀ A R, (R BinRelOn A) → (max_set_sub A A R = max_set A R) :=
  fun (A R) =>
    fun (hAR : (R BinRelOn A)) =>
      extensionality (max_set_sub A A R) (max_set A R) (
        fun (t) =>
          Iff.intro
          (
            fun (ht : (t ∈ (max_set_sub A A R))) =>
              let u := Iff.mp (max_set_sub_is_max_set_sub A A R t (subset_refl A)) ht
              let v := Iff.mpr (max_sub_A_is_max_al A R hAR t (And.left u)) u
              Iff.mpr (max_set_is_max_set A R t) (And.intro (And.left u) (v))
          )
          (
            fun (ht : (t ∈ (max_set A R))) =>
              let u := Iff.mp (max_set_is_max_set A R t) ht
              Iff.mpr (max_set_sub_is_max_set_sub A A R t (subset_refl A)) (
                And.intro (And.left u) (
                  fun (y) =>
                    fun (_ : y ∈ A) =>
                      And.right u y
                )
              )
          )
      )

theorem min_set_sub_A_is_min_set : ∀ A R, (R BinRelOn A) →  (min_set_sub A A R = min_set A R) :=
  fun (A R) =>
    fun (hAR : (R BinRelOn A)) =>
      extensionality (min_set_sub A A R) (min_set A R) (
        fun (t) =>
          Iff.intro
          (
            fun (ht : (t ∈ (min_set_sub A A R))) =>
              let u := Iff.mp (min_set_sub_is_min_set_sub A A R t (subset_refl A)) ht
              let v := Iff.mpr (min_sub_A_is_min_al A R hAR t (And.left u)) u
              Iff.mpr (min_set_is_min_set A R t) (And.intro (And.left u) (v))
          )
          (
            fun (ht : (t ∈ (min_set A R))) =>
              let u := Iff.mp (min_set_is_min_set A R t) ht
              Iff.mpr (min_set_sub_is_min_set_sub A A R t (subset_refl A)) (
                And.intro (And.left u) (
                  fun (y) =>
                    fun (_ : y ∈ A) =>
                      And.right u y
                )
              )
          )
      )





theorem max_um_is_al_sub : ∀ A R₁ R₂ B x, (R₁ with R₂ PO A) → (is_maximum_sub R₂ B x) → (is_maximal_sub R₁ B x) :=
  fun (A R₁ R₂ B x) =>
    fun (h : (R₁ with R₂ PO A)) =>
        fun (hm_um_sub : (is_maximum_sub R₂ B x)) =>
          And.intro (And.left hm_um_sub) (
            let u := And.right hm_um_sub

            fun (y) =>
              fun (hyB : y ∈ B) =>
                fun (hxy : (x . R₁ . y)) =>
                  let u₂ := u y hyB
                  no_symm_R₁_R₂ A R₁ R₂ h x y (
                    And.intro (hxy) (u₂)
                  )
          )


theorem min_um_is_al_sub : ∀ A R₁ R₂ B x, (R₁ with R₂ PO A) → (is_minimum_sub R₂ B x) → (is_minimal_sub R₁ B x) :=
  fun (A R₁ R₂ B x) =>
    fun (h : (R₁ with R₂ PO A)) =>
      fun (hmin : (is_minimum_sub R₂ B x)) =>
        And.intro (And.left hmin) (
          fun (y) =>
            fun (hyB : y ∈ B) =>
              fun (hyx : (y . R₁ . x)) =>
                let u := And.right hmin y hyB

                no_symm_R₁_R₂ A R₁ R₂ h y x (
                  And.intro (hyx) (u)
                )
        )



theorem max_um_is_al : ∀ A R₁ R₂ x, (R₁ with R₂ PO A) → (is_maximum R₂ A x) → (is_maximal R₁ x) :=
  fun (A R₁ R₂ x) =>
    fun (h : (R₁ with R₂ PO A)) =>
      fun (hmax : (is_maximum R₂ A x)) =>
        fun (y) =>
          fun (hxy : (x . R₁ . y)) =>
            let v := part_ord_pair_prop_R₁_A A R₁ R₂ h x y hxy
            let u := hmax y
            no_symm_R₁_R₂ A R₁ R₂ h x y (
              And.intro hxy (u (And.right v))
            )



theorem min_um_is_al : ∀ A R₁ R₂ x, (R₁ with R₂ PO A) → (is_minimum R₂ A x) → (is_minimal R₁ x) :=
  fun (A R₁ R₂ x) =>
    fun (h : (R₁ with R₂ PO A)) =>
      fun (hmin : (is_minimum R₂ A x)) =>
        fun (y) =>
          fun (hxy : (y . R₁ . x)) =>
            let v := part_ord_pair_prop_R₁_A A R₁ R₂ h y x hxy
            let u := hmin y
            no_symm_R₁_R₂ A R₁ R₂ h y x (
              And.intro hxy (u (And.left v))
            )


theorem max_um_unique_sub :
 ∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_maximum_sub R₂ B x) → (is_maximum_sub R₂ B y) → (x = y) :=
  fun (A R₁ R₂ B x y) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (hmaxub₁ : (is_maximum_sub R₂ B x)) =>
        fun (hmaxub₂ : (is_maximum_sub R₂ B y)) =>
          let u := And.right (hmaxub₁) y (And.left hmaxub₂)
          let v := And.right (hmaxub₂) x (And.left hmaxub₁)
          antisymm_R₂ A R₁ R₂ hR x y v u


theorem min_um_unique_sub :
∀ A R₁ R₂ B x y, (R₁ with R₂ PO A) → (is_minimum_sub R₂ B x) → (is_minimum_sub R₂ B y) → (x = y) :=
  fun (A R₁ R₂ B x y) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (hminub₁ : (is_minimum_sub R₂ B x)) =>
        fun (hminub₂ : (is_minimum_sub R₂ B y)) =>
          let u := And.right (hminub₁) y (And.left hminub₂)
          let v := And.right (hminub₂) x (And.left hminub₁)
          Eq.symm (antisymm_R₂ A R₁ R₂ hR y x v u)



theorem max_um_unique : ∀ A R₁ R₂, ∀ x y ∈ A; (R₁ with R₂ PO A) → (is_maximum R₂ A x) → (is_maximum R₂ A y) → (x = y) :=
  fun (A R₁ R₂ x) =>
    fun (hx : x ∈ A) => fun (y) =>
      fun (hy : y ∈ A) =>
        fun (hR : (R₁ with R₂ PO A)) =>
          fun (hmaxur₂ : ((is_maximum R₂ A x))) =>
            fun (hmaxur₁ : (is_maximum R₂ A y)) =>
              let u := hmaxur₂ y
              let v := hmaxur₁ x
              antisymm_R₂ A R₁ R₂ hR x y (v (hx)) (u (hy))



theorem min_um_unique : ∀ A R₁ R₂, ∀ x y ∈ A; (R₁ with R₂ PO A) → (is_minimum R₂ A x) → (is_minimum R₂ A y) → (x = y) :=
  fun (A R₁ R₂ x) =>
   fun (hx : x ∈ A) => fun (y) =>
      fun (hy : y ∈ A) =>
        fun (hR : (R₁ with R₂ PO A)) =>
          fun (hminur₂ : (is_minimum R₂ A x)) =>
            fun (hminur₁ : (is_minimum R₂ A y)) =>
              let u := hminur₂ y
              let v := hminur₁ x
              Eq.symm (antisymm_R₂ A R₁ R₂ hR y x (v hx) (u hy))



theorem max_um_maxset_singl_sub :
∀ A R₁ R₂ B x, (R₁ with R₂ PO A) → (B ⊆ A) → (is_maximum_sub R₂ B x) → (max_set_sub A B R₁ = {x}) :=
  fun (A R₁ R₂ B x) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      fun (hBA : (B ⊆ A)) =>
        fun (hmaxum : (is_maximum_sub R₂ B x)) =>
          extensionality (max_set_sub A B R₁) {x} (
            fun (y) =>
              Iff.intro
              (
                fun (hy : y ∈ (max_set_sub A B R₁)) =>
                  let first := Iff.mp (max_set_sub_is_max_set_sub A B R₁ y hBA) hy
                  let u := And.right (first) x (And.left hmaxum)

                  let v := And.right hmaxum y (And.left first)



                  eq_subst (fun (t) => t ∈ {x}) x y (
                    byContradiction (
                      fun (hxyneq : x ≠ y) =>
                        let s := part_ord_pair_prop_neqR₂R₁ A R₁ R₂ hR y x (And.intro (v) (
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
                  Iff.mpr (max_set_sub_is_max_set_sub A B R₁ y hBA) (
                    eq_subst (fun (t) => is_maximal_sub R₁ B t) x y (Eq.symm u) (

                      And.intro (And.left hmaxum) (
                        fun (z) =>
                          fun (hz : z ∈ B) =>
                            fun (hxyR₁ : (x . R₁ . z)) =>
                              let u₂ := And.right hmaxum z hz
                              no_symm_R₁_R₂ A R₁ R₂ hR x z (
                                And.intro (hxyR₁) (u₂)
                              )
                      )
                    )
                  )
              )
          )



theorem min_um_minset_singl_sub :
∀ A R₁ R₂ B x, (R₁ with R₂ PO A) → (B ⊆ A) → (is_minimum_sub R₂ B x) → (min_set_sub A B R₁ = {x}) :=
    fun (A R₁ R₂ B x) =>
    fun (hR : (R₁ with R₂ PO A)) =>
      let u := And.left (And.left (And.right (Iff.mp (part_ord_nspo_crit A R₁ R₂) hR)))
      let u₂ := And.left (And.left (And.right hR))
      fun (hBA : (B ⊆ A)) =>
        fun (hmaxum : (is_minimum_sub R₂ B x)) =>
            let v := Iff.mp (min_max_sub_inv_um R₂ B x (bin_on_is_bin A R₂ u)) hmaxum
            let s := max_um_maxset_singl_sub A (R₁⁻¹) (R₂⁻¹) B x (inv_is_PO A R₁ R₂ hR) hBA v
            let u := max_min_set_inv_sub A B R₁ (bin_on_is_bin A R₁ u₂) hBA
            Eq.trans u s



def is_upper_bound (A B R x : Set) := x ∈ A ∧ ∀ y ∈ B; (y . R . x)
def is_lower_bound (A B R x : Set) := x ∈ A ∧ ∀ y ∈ B; (x . R . y)

noncomputable def lower_bounds (A B R) := {z ∈ A | is_lower_bound A B R z}
noncomputable def upper_bounds (A B R) := {z ∈ A | is_upper_bound A B R z}

syntax term "LowBou" term "in" term : term
syntax term "UppBou" term "in" term : term
macro_rules
| `($R:term LowBou $B:term in $A:term) => `(lower_bounds $A $B $R)
| `($R:term UppBou $B:term in $A:term) => `(upper_bounds $A $B $R)


theorem inv_low_upp_bou : ∀ A B R, (BinRel R) → ∀ x, (is_upper_bound A B R x) ↔ (is_lower_bound A B (R⁻¹) x) :=
  fun (A B R) =>
    fun (hR : (BinRel R)) =>
      fun (x) =>
        Iff.intro
        (
          sorry
        )
        (
          sorry
        )


theorem inv_upp_low_bou : ∀ A B R, (BinRel R) → ∀ x, (is_lower_bound A B R x) ↔ (is_upper_bound A B (R⁻¹) x) :=
  fun (A B R) =>
    fun (hR : (BinRel R)) =>
      fun (x) =>
        Iff.intro
        (
          sorry
        )
        (
          sorry
        )


theorem low_bou_set_is_low_bou : ∀ A B R, ∀ x, (x ∈ (R LowBou B in A) ↔ (is_lower_bound A B R x)) :=
  fun (A B R) =>
    fun (x) =>
      Iff.intro
      (
        fun (hx : (x ∈ R LowBou B in A)) =>
          And.right (Iff.mp (specification_set_is_specification (fun (P) => is_lower_bound A B R P) (A) x) hx)
      )
      (
        fun (hx : (is_lower_bound A B R x)) =>
          Iff.mpr (specification_set_is_specification (fun (P) => is_lower_bound A B R P) (A) x) (
            And.intro (And.left hx) (hx)
          )
      )
