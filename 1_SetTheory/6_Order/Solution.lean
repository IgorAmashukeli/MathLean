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



theorem assym_then_antisymm : ∀ A R, binary_relation_on A R → ((asymm R) ↔ (antisymm R ∧ irrefl R)) :=
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


theorem trans_irrefl_ansymm :
∀ A R, binary_relation_on A R → (transit R) → (irrefl R) → (asymm R) :=
  fun (A R) =>
    fun (hAR : (binary_relation_on A R)) =>
      fun (htr : (transit R)) =>
        fun (hirr : (irrefl R)) =>
          Iff.mpr (assym_then_antisymm A R hAR) (
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
