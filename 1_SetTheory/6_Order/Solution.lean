import «Header»
open Classical

noncomputable def rel_specification (R B) := R ∩ (B × B)
syntax term "spec" term : term
macro_rules
| `($R spec $B) => `(rel_specification $R $B)

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

noncomputable def subs_part_ord (𝓐 X) := ⁅X; ≺(𝓐) spec X; ≼(𝓐) spec X⁆
syntax term "SubsPO" term : term
macro_rules
| `($𝓐 SubsPO $X) => `(subs_part_ord $𝓐 $X)

noncomputable def inter_part_ord (𝓐 𝓑) := ⁅setPO(𝓐); ≺(𝓐) ∩ ≺(𝓑); ≼(𝓐) ∩ ≼(𝓑)⁆
syntax term "InterPO" term : term
macro_rules
| `($𝓐 InterPO $𝓑) => `(inter_part_ord $𝓐 $𝓑)


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

theorem po_emp : ∀ 𝓐, (PartOrd 𝓐) → (setPO(𝓐) ≠ ∅) :=
  fun (𝓐) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
      Exists.elim h𝓐 (
        fun (A) =>
          fun (ha) =>
            Exists.elim (ha) (
              fun (R₁) =>
                fun (hR₁) =>
                  Exists.elim hR₁ (
                    fun (R₂) =>
                      fun (hR₂) =>
                        let v := And.right hR₂
                        let t := And.left v
                        let u := And.left hR₂
                        let u₀ := setPO_is_setPO A R₁ R₂
                        let u₁ := eq_subst (fun (t) => setPO(t) = A) ⁅A; R₁; R₂⁆ (𝓐) (Eq.symm u) (u₀)

                        eq_subst (fun (t) => t ≠ ∅) (A) (setPO(𝓐)) (Eq.symm u₁) (t)
                  )
            )
      )




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
            let m := par_ord_pair_prop_R₂_A 𝓐 h𝓐 x z u
            Iff.mpr (And.left (part_ord_pair_prop 𝓐 h𝓐 x (And.left m) z (And.right m))) (
              And.intro u (
                fun (hxz : (x = z)) =>
                  no_symm_R₁_R₂ 𝓐 h𝓐 y z (
                    And.intro (hyz) (
                      eq_subst (fun (t) => (t . (≼(𝓐)) . y)) x z hxz (hxy)
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

noncomputable def po_set_cart (𝓐 𝓑) := setPO(𝓐) × setPO(𝓑)

def po_set_prop (𝓐 𝓑) := fun (s) => ∃ x₁ ∈ setPO(𝓐); ∃ y₁ ∈ setPO(𝓑); ∃ x₂ ∈ setPO(𝓐); ∃ y₂ ∈ setPO(𝓑);
(s = ((x₁, y₁), (x₂, y₂))) ∧ (x₁ . ≼(𝓐) . x₂) ∧ (y₁ . ≼(𝓑) . y₂)

noncomputable def leq_cart (𝓐 𝓑) := {s ∈ (po_set_cart 𝓐 𝓑) × (po_set_cart 𝓐 𝓑) | po_set_prop 𝓐 𝓑 s}

noncomputable def le_cart (𝓐 𝓑) := str (setPO(𝓐) × setPO(𝓑)) (leq_cart 𝓐 𝓑)

noncomputable def cartesian_part_ord (𝓐 𝓑) := ⁅setPO(𝓐) × setPO(𝓑); le_cart 𝓐 𝓑; leq_cart 𝓐 𝓑⁆
syntax term "CartPO" term : term
macro_rules
| `($𝓐 CartPO $𝓑) => `(cartesian_part_ord $𝓐 $𝓑)


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



theorem cart_PO_PO : ∀ 𝓐 𝓑, (PartOrd 𝓐) → (PartOrd 𝓑) → (PartOrd (𝓐 CartPO 𝓑)) :=
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
              And.intro (Eq.refl (𝓐 CartPO 𝓑)) (

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
      fun (hm_um : (is_maximum 𝓐 B x)) =>
        And.intro (And.left hm_um) (
          fun (y) =>
            fun (hyB : y ∈ B) =>
              fun (hxyless : (x . (≺(𝓐)) . y)) =>
                let u := And.right hm_um y hyB
                no_symm_R₁_R₂ 𝓐 h𝓐 x y (
                  And.intro (hxyless) (u)
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


theorem min_um_sub_cmp : ∀ 𝓐 B C x y, (C ⊆ B) → (is_minimum 𝓐 B x) → (is_minimum 𝓐 C y) → (x . ≼(𝓐) . y) :=
  fun (𝓐 B C x y) =>
      fun (hCB : (C ⊆ B)) =>
        fun (hminB : (is_minimum 𝓐 B x)) =>
          fun (hminC : (is_minimum 𝓐 C y) ) =>
            And.right hminB y (hCB y (And.left hminC))


theorem max_um_sub_cmp : ∀ 𝓐 B C x y, (C ⊆ B) → (is_maximum 𝓐 B x) → (is_maximum 𝓐 C y) → (y . ≼(𝓐) . x) :=
  fun (𝓐 B C x y) =>
      fun (hCB : (C ⊆ B)) =>
        fun (hminB : (is_maximum 𝓐 B x)) =>
          fun (hminC : (is_maximum 𝓐 C y) ) =>
            And.right hminB y (hCB y (And.left hminC))


theorem um_min_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (is_minimum 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_minimum 𝓐 ((B _ i)) y) → (y . ≼(𝓐) . x) :=
  fun (𝓐 B I x) =>
    fun (hBI : (B IndxFun I)) =>
      fun (hminx : (is_minimum 𝓐 ((⋂[ i in I ] B at i)) x)) =>
        fun (i) =>
          fun (hi : i ∈ I) =>
            fun (y) =>
              fun (hminy : (is_minimum 𝓐 ((B _ i)) y) ) =>
                let u := indexed_intersection_sub_indexed B I hBI i hi
                min_um_sub_cmp 𝓐 (B _ i) ((⋂[ i in I ] B at i)) y x u hminy hminx


theorem um_max_inter_prop : ∀ 𝓐 B I x, (B IndxFun I) → (is_maximum 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_maximum 𝓐 ((B _ i)) y) → (x . ≼(𝓐) . y) :=
  fun (𝓐 B I x) =>
    fun (hBI : (B IndxFun I)) =>
      fun (hminx : (is_maximum 𝓐 ((⋂[ i in I ] B at i)) x)) =>
        fun (i) =>
          fun (hi : i ∈ I) =>
            fun (y) =>
              fun (hminy : (is_maximum 𝓐 ((B _ i)) y) ) =>
                let u := indexed_intersection_sub_indexed B I hBI i hi
                max_um_sub_cmp 𝓐 (B _ i) ((⋂[ i in I ] B at i)) y x u hminy hminx



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
theorem sub_low_upp :∀ 𝓐 B, (B ⊆ (setPO(𝓐))) → (B ⊆ (𝓐 ▾ (𝓐 ▴ B))) :=
  fun (𝓐 B) =>
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
theorem upp_low_upp_is_low : ∀ 𝓐 B, (B ⊆ (setPO(𝓐))) → (𝓐 ▴ (𝓐 ▾ (𝓐 ▴ B))) = (𝓐 ▴ B) :=
  fun (𝓐 B) =>
      fun (hBA : (B ⊆ (setPO(𝓐)))) =>
        sub_sub_then_eq (𝓐 ▴ (𝓐 ▾ (𝓐 ▴ B))) (𝓐 ▴ B) (
          upp_bou_set_subset 𝓐 B (𝓐 ▾ (𝓐 ▴ B)) (sub_low_upp 𝓐 B hBA)
        ) (
          let P := fun (t) => is_upper_bound 𝓐 B t
          sub_upp_low 𝓐 (𝓐 ▴ B) (specification_set_subset P (setPO(𝓐)))
        )


theorem low_upp_low_is_upp : ∀ 𝓐 B, (B ⊆ (setPO(𝓐))) → (𝓐 ▾ (𝓐 ▴ (𝓐 ▾ B))) = (𝓐 ▾ B) :=
  fun (𝓐 B) =>
      fun (hBA : (B ⊆ (setPO(𝓐)))) =>
        sub_sub_then_eq (𝓐 ▾ (𝓐 ▴ (𝓐 ▾ B))) (𝓐 ▾ B) (
          low_bou_set_subset 𝓐 B (𝓐 ▴ (𝓐 ▾ B)) (sub_upp_low 𝓐 B hBA)
        ) (
          let P := fun (t) => is_lower_bound 𝓐 B t
          sub_low_upp 𝓐 (𝓐 ▾ B) (specification_set_subset P (setPO(𝓐)))
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


theorem partmin_um_un_prop : ∀ 𝓐 B I x, (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_minimum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_minimum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimum 𝓐 (B _ i) y} x)
  ) :=
  fun (𝓐 B I x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hminexi : ((∀ i ∈ I; (𝓐 MinExi (B _ i))))) =>
            fun (hiset : (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))) =>
              Iff.intro
              (
                fun (hx : (is_minimum 𝓐 (⋃[i in I] B at i) x)) =>
                  let u₀ := And.right hx x (And.left hx)
                  let u₁ := And.left (par_ord_pair_prop_R₂_A 𝓐 (h𝓐) x x u₀)
                  let u₃ := Iff.mp (indexed_union_is_union B I (hBI) x) (And.left hx)
                  Exists.elim u₃ (
                    fun (i) =>
                      fun (hi : i ∈ I ∧ x ∈ (B _ i)) =>
                        let u := Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_minimum 𝓐 (B _ i) P) (setPO(𝓐)) x) (
                          And.intro (u₁) (Exists.intro i (
                            And.intro (And.left hi) (
                              And.intro (And.right hi) (
                                fun (y) =>
                                  fun (hy : y ∈ (B _ i)) =>
                                    And.right hx y (
                                      indexed_sub_indexed_union B I hBI i (And.left hi) y hy
                                    )
                              )
                            )
                          ))
                        )
                        And.intro (u) (
                          fun (s) =>
                            fun (hs : s ∈ {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimum 𝓐 (B _ i) y}) =>
                              let u₄ := And.right (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_minimum 𝓐 (B _ i) P)
                              (setPO(𝓐)) s) hs)

                              Exists.elim u₄ (
                                fun (j) =>
                                  fun (hj : j ∈ I ∧ is_minimum 𝓐 (B _ j) s) =>
                                    let u₅ := And.left (And.right hj)
                                    let u₆ := indexed_sub_indexed_union B I hBI j (And.left hj) s u₅
                                    And.right hx s (
                                      u₆
                                    )
                              )
                        )
                  )
              )
              (
                fun (hx : is_minimum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimum 𝓐 (B _ i) y} x) =>
                  let u₀ := And.right (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_minimum 𝓐 (B _ i) P)
                              (setPO(𝓐)) x) (And.left hx))
                  Exists.elim u₀ (
                    fun (j) =>
                      fun (hj : j ∈ I ∧ is_minimum 𝓐 (B _ j) x) =>
                        let u₁ := And.left (And.right hj)
                        let u₂ := indexed_sub_indexed_union B I hBI j (And.left hj) x u₁

                        And.intro (u₂) (
                        fun (y) =>
                          fun (hy : y ∈ (⋃[i in I] B at i)) =>
                            let u₃ := Iff.mp (indexed_union_is_union B I (hBI) y ) hy
                            Exists.elim u₃ (

                              fun (i) =>
                                fun (hi : i ∈ I ∧ y ∈ (B _ i)) =>
                                  let v₀ := hminexi i (And.left hi)
                                  Exists.elim v₀ (
                                    fun (s) =>
                                      fun (hs : is_minimum 𝓐 (B _ i) s) =>

                                        trans_R₂ 𝓐 (h𝓐) x s y (
                                          And.right hx s (

                                            Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_minimum 𝓐 (B _ i) P)
                                          (setPO(𝓐)) s) (
                                            And.intro (hiset i (And.left hi) s (And.left hs))
                                            (Exists.intro i (And.intro (And.left hi) (hs)))
                                          )
                                          )
                                        ) (And.right hs y (And.right hi))
                                  )


                            )

                        )

                  )
              )


theorem partmax_um_un_prop : ∀ 𝓐 B I x, (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_maximum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_maximum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximum 𝓐 (B _ i) y} x)) :=
fun (𝓐 B I x) =>
    fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hminexi : ((∀ i ∈ I; (𝓐 MaxExi (B _ i))))) =>
            fun (hiset : (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))) =>
              Iff.intro
              (
                fun (hx : (is_maximum 𝓐 (⋃[i in I] B at i) x)) =>
                  let u₀ := And.right hx x (And.left hx)
                  let u₁ := And.left (par_ord_pair_prop_R₂_A 𝓐 (h𝓐) x x u₀)
                  let u₃ := Iff.mp (indexed_union_is_union B I (hBI) x) (And.left hx)
                  Exists.elim u₃ (
                    fun (i) =>
                      fun (hi : i ∈ I ∧ x ∈ (B _ i)) =>
                        let u := Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_maximum 𝓐 (B _ i) P) (setPO(𝓐)) x) (
                          And.intro (u₁) (Exists.intro i (
                            And.intro (And.left hi) (
                              And.intro (And.right hi) (
                                fun (y) =>
                                  fun (hy : y ∈ (B _ i)) =>
                                    And.right hx y (
                                      indexed_sub_indexed_union B I hBI i (And.left hi) y hy
                                    )
                              )
                            )
                          ))
                        )
                        And.intro (u) (
                          fun (s) =>
                            fun (hs : s ∈ {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximum 𝓐 (B _ i) y}) =>
                              let u₄ := And.right (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_maximum 𝓐 (B _ i) P)
                              (setPO(𝓐)) s) hs)

                              Exists.elim u₄ (
                                fun (j) =>
                                  fun (hj : j ∈ I ∧ is_maximum 𝓐 (B _ j) s) =>
                                    let u₅ := And.left (And.right hj)
                                    let u₆ := indexed_sub_indexed_union B I hBI j (And.left hj) s u₅
                                    And.right hx s (
                                      u₆
                                    )
                              )
                        )
                  )
              )
              (
                fun (hx : is_maximum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximum 𝓐 (B _ i) y} x) =>
                  let u₀ := And.right (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_maximum 𝓐 (B _ i) P)
                              (setPO(𝓐)) x) (And.left hx))
                  Exists.elim u₀ (
                    fun (j) =>
                      fun (hj : j ∈ I ∧ is_maximum 𝓐 (B _ j) x) =>
                        let u₁ := And.left (And.right hj)
                        let u₂ := indexed_sub_indexed_union B I hBI j (And.left hj) x u₁

                        And.intro (u₂) (
                        fun (y) =>
                          fun (hy : y ∈ (⋃[i in I] B at i)) =>
                            let u₃ := Iff.mp (indexed_union_is_union B I (hBI) y ) hy
                            Exists.elim u₃ (

                              fun (i) =>
                                fun (hi : i ∈ I ∧ y ∈ (B _ i)) =>
                                  let v₀ := hminexi i (And.left hi)
                                  Exists.elim v₀ (
                                    fun (s) =>
                                      fun (hs : is_maximum 𝓐 (B _ i) s) =>

                                        trans_R₂ 𝓐 (h𝓐) y s x (And.right hs y (And.right hi)) (
                                          And.right hx s (

                                            Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_maximum 𝓐 (B _ i) P)
                                          (setPO(𝓐)) s) (
                                            And.intro (hiset i (And.left hi) s (And.left hs))
                                            (Exists.intro i (And.intro (And.left hi) (hs)))
                                          )
                                          )
                                        )
                                  )


                            )

                        )

                  )
              )



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

theorem po_max_subset_prop : ∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MaxExi B) → (𝓐 MaxExi C) → ((𝓐 Max C) . (≼(𝓐)) . (𝓐 Max B)) :=
  fun (𝓐 B C hCB h𝓐 hBexi hCexi) =>
    let u₁ := max_po_prop 𝓐 B h𝓐 hBexi
    let u₂ := max_po_prop 𝓐 C h𝓐 hCexi
    let u₃ := hCB (𝓐 Max C) (And.left (u₂))
    And.right u₁ (𝓐 Max C) u₃


theorem po_min_subset_prop : ∀ 𝓐 B C, (C ⊆ B) → (PartOrd 𝓐) → (𝓐 MinExi B) → (𝓐 MinExi C) → ((𝓐 Min B) . (≼(𝓐)) . (𝓐 Min C)) :=
  fun (𝓐 B C hCB h𝓐 hBexi hCexi) =>
    let u₁ := min_po_prop 𝓐 B h𝓐 hBexi
    let u₂ := min_po_prop 𝓐 C h𝓐 hCexi
    let u₃ := hCB (𝓐 Min C) (And.left (u₂))
    And.right u₁ (𝓐 Min C) u₃


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


theorem supr_union : ∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; 𝓐 SuprExi (B _ i)) → (∀ i j ∈ I; (𝓐 Supr (B _ i)) = (𝓐 Supr (B _ j))) → ((𝓐 SuprExi (⋃[i in I] B at i)) ∧(∀ s ∈ I; (𝓐 Supr (⋃[i in I] B at i)) = (𝓐 Supr (B _ s)))) :=
  fun (𝓐 B I) =>
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


theorem infm_union : ∀ 𝓐 B I, (I ≠ ∅) → (PartOrd 𝓐) → (B Indx I) → (∀ i ∈ I; 𝓐 InfmExi (B _ i)) → (∀ i j ∈ I; (𝓐 Infm (B _ i)) = (𝓐 Infm (B _ j))) → ((𝓐 InfmExi (⋃[i in I] B at i)) ∧ (∀ s ∈ I; (𝓐 Infm (⋃[i in I] B at i)) = (𝓐 Infm (B _ s)))) :=
  fun (𝓐 B I) =>
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


theorem lrc_min : ∀ 𝓐, ∀ a ∈ setPO(𝓐); ∀ b, (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_minimum 𝓐 (⟦ a ; b ⟧ of 𝓐) a) :=
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


theorem lrc_max : ∀ 𝓐 a, ∀ b ∈ setPO(𝓐); (PartOrd 𝓐) → (a . ≼(𝓐) . b) → (is_maximum 𝓐 (⟦ a ; b ⟧ of 𝓐) b) :=
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


def is_lattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ x y ∈ (setPO(𝓐)); (𝓐 SuprExi ({x, y})) ∧ (𝓐 InfmExi ({x, y})))
syntax "Latt" term : term
macro_rules
| `(Latt $𝓐:term) => `(is_lattice $𝓐)


theorem boolean_Latt : ∀ A, (Latt (BoolPO A)) :=
  fun (A) =>
    And.intro (boolean_PO A) (
      fun (X) => fun (hx : X ∈ setPO(BoolPO A)) =>
        fun (Y) => fun (hy : Y ∈ setPO(BoolPO A)) =>
          let u₁ := setPO_is_setPO (𝒫 A) (subneq_binrel A) (sub_binrel A)
          let u₂ := eq_subst (fun (t) => X ∈ t) setPO(BoolPO A) (𝒫 A) u₁ hx
          let u₃ := eq_subst (fun (t) => Y ∈ t) setPO(BoolPO A) (𝒫 A) u₁ hy
          let u₄ := Iff.mp (boolean_set_is_boolean A X) u₂
          let u₅ := Iff.mp (boolean_set_is_boolean A Y) u₃
          let u₆ := sub_sub_union_sub X Y A u₄ u₅
          let u₇ := subset_trans (X ∩ Y) X A (And.left (interset2sets_subset_prop X Y)) (u₄)
          let u₈ := Iff.mpr (boolean_set_is_boolean A (X ∪ Y)) u₆
          let u₉ := Iff.mpr (boolean_set_is_boolean A (X ∩ Y)) u₇
          let u₁₀ := eq_subst (fun (t) => X ∪ Y ∈ t) (𝒫 A) setPO(BoolPO A) (Eq.symm u₁) u₈
          let u₁₁ := eq_subst (fun (t) => X ∩ Y ∈ t) (𝒫 A) setPO(BoolPO A) (Eq.symm u₁) u₉
          let u₁₂ := And.left (union2sets_subset_prop X Y)
          let u₁₃ := Iff.mpr (NSPO_bool_pair_prop A X u₂ (X ∪ Y) u₈) u₁₂
          let u₁₄ := And.right (union2sets_subset_prop X Y)
          let u₁₅ := Iff.mpr (NSPO_bool_pair_prop A Y u₃ (X ∪ Y) u₈) u₁₄
          let u₁₆ := lesseqPO_is_lesseqPO (𝒫 A) (subneq_binrel A) (sub_binrel A)
          let u₁₇ := eq_subst (fun (t) => (X, X ∪ Y) ∈ t) (sub_binrel A) (≼(BoolPO A)) (Eq.symm u₁₆) (u₁₃)
          let u₁₈ := eq_subst (fun (t) => (Y, X ∪ Y) ∈ t) (sub_binrel A) (≼(BoolPO A)) (Eq.symm u₁₆) (u₁₅)
          let u₁₉ := And.left (interset2sets_subset_prop X Y)
          let u₂₀ := And.right (interset2sets_subset_prop X Y)
          let u₂₁ := Iff.mpr (NSPO_bool_pair_prop A (X ∩ Y) u₉ X u₂) u₁₉
          let u₂₂ := Iff.mpr (NSPO_bool_pair_prop A (X ∩ Y) u₉ Y u₃) u₂₀
          let u₂₃ := eq_subst (fun (t) => (X ∩ Y, X) ∈ t) (sub_binrel A) (≼(BoolPO A)) (Eq.symm u₁₆) (u₂₁)
          let u₂₄ := eq_subst (fun (t) => (X ∩ Y, Y) ∈ t) (sub_binrel A) (≼(BoolPO A)) (Eq.symm u₁₆) (u₂₂)

          And.intro (
            Exists.intro (X ∪ Y) (
              And.intro (
                Iff.mpr (upp_bou_set_is_upp_bou (BoolPO A) {X, Y} (X ∪ Y)) (
                  And.intro (u₁₀) (
                    fun (a) =>
                      fun (ha : a ∈ {X, Y}) =>
                        let v₁ := Iff.mp (unordered_pair_set_is_unordered_pair X Y a) ha
                        Or.elim (v₁)
                        (
                          fun (v₂ : a = X) =>
                            eq_subst (fun (t) => (t, X ∪ Y) ∈ ≼(BoolPO A)) X a (Eq.symm v₂) (
                              u₁₇
                            )
                        )
                        (
                          fun (v₂ : a = Y) =>
                            eq_subst (fun (t) => (t, X ∪ Y) ∈ ≼(BoolPO A)) Y a (Eq.symm v₂) (u₁₈)
                        )
                  )
                )
              ) (
                fun (a) =>
                  fun (ha : a ∈ (BoolPO A) ▴ {X, Y}) =>
                    let v₁ := Iff.mp (upp_bou_set_is_upp_bou (BoolPO A) {X, Y} a) ha
                    let v₂ := And.right v₁ X (left_unordered_pair X Y)
                    let v₂₀ := And.left v₁
                    let v₂₁ := eq_subst (fun (t) => a ∈ t) (setPO(BoolPO A)) (𝒫 A) u₁ v₂₀
                    let v₂₃ := And.right v₁ Y (right_unordered_pair X Y)
                    let v₃ := eq_subst (fun (t) => (X, a) ∈ t) ≼(BoolPO A) (sub_binrel A) (u₁₆) (v₂)
                    let v₄ := Iff.mp (NSPO_bool_pair_prop A X u₂ a (v₂₁)) v₃
                    let v₅ := eq_subst (fun (t) => (Y, a) ∈ t) ≼(BoolPO A) (sub_binrel A) (u₁₆) (v₂₃)
                    let v₆ := Iff.mp (NSPO_bool_pair_prop A Y u₃ a (v₂₁)) v₅
                    let v₇ := sub_sub_union_sub X Y a v₄ v₆
                    let v₈ := Iff.mpr (NSPO_bool_pair_prop A (X ∪ Y) u₈ a (v₂₁)) v₇

                    eq_subst (fun (t) => (X ∪ Y, a) ∈ t) (sub_binrel A) ≼(BoolPO A) (Eq.symm u₁₆) (v₈)
              )
            )
          ) (
            Exists.intro (X ∩ Y) (
              And.intro (
                Iff.mpr (low_bou_set_is_low_bou (BoolPO A) {X, Y} (X ∩ Y)) (
                  And.intro (u₁₁) (
                    fun (a) =>
                      fun (ha : a ∈ {X, Y}) =>
                        let v₁ := Iff.mp (unordered_pair_set_is_unordered_pair X Y a) ha
                        Or.elim (v₁)
                        (
                          fun (v₂ : a = X) =>
                            eq_subst (fun (t) => (X ∩ Y, t) ∈ ≼(BoolPO A)) X a (Eq.symm v₂) (
                              u₂₃
                            )
                        )
                        (
                          fun (v₂ : a = Y) =>
                            eq_subst (fun (t) => (X ∩ Y, t) ∈ ≼(BoolPO A)) Y a (Eq.symm v₂) (
                              u₂₄
                            )
                        )
                  )
                )
              ) (
                fun (a) =>
                  fun (ha : a ∈ (BoolPO A) ▾ {X, Y}) =>
                    let v₁ := Iff.mp (low_bou_set_is_low_bou (BoolPO A) {X, Y} a) ha
                    let v₂ := And.right v₁ X (left_unordered_pair X Y)
                    let v₃ := And.right v₁ Y (right_unordered_pair X Y)
                    let v₄ := And.left v₁
                    let v₅ := eq_subst (fun (t) => a ∈ t) (setPO(BoolPO A)) (𝒫 A) u₁ (v₄)
                    let v₆ := eq_subst (fun (t) => (a, X) ∈ t) ≼(BoolPO A) (sub_binrel A) (u₁₆) (v₂)
                    let v₇ := eq_subst (fun (t) => (a, Y) ∈ t) ≼(BoolPO A) (sub_binrel A) (u₁₆) (v₃)
                    let v₈ := Iff.mp (NSPO_bool_pair_prop A a v₅ X u₂) (v₆)
                    let v₉ := Iff.mp (NSPO_bool_pair_prop A a v₅ Y u₃) (v₇)
                    let v₁₀ := sub_sub_inter_sub X Y a v₈ v₉
                    let v₁₁ := Iff.mpr (NSPO_bool_pair_prop A a v₅ (X ∩ Y) u₉) v₁₀
                    eq_subst (fun (t) => (a, X ∩ Y) ∈ t) (sub_binrel A) ≼(BoolPO A) (Eq.symm u₁₆) (v₁₁)

              )
            )
          )
    )


def is_complete_lattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ X, (X ⊆ setPO(𝓐)) → (𝓐 SuprExi X))
syntax "CompLatt" term : term
macro_rules
| `(CompLatt $𝓐) => `(is_complete_lattice $𝓐)



theorem compl_latt_inf_crit : ∀ 𝓐, (PartOrd 𝓐) → ((CompLatt 𝓐) ↔ (∀ X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X))) :=
  fun (𝓐) =>
    fun (hPart : (PartOrd 𝓐)) =>
    Iff.intro
    (
      fun (h𝓐 : (CompLatt 𝓐)) =>
        fun (X) =>
          fun (hX : (X ⊆ setPO(𝓐))) =>
            let Xlow := 𝓐 ▾ X
            let h₀ := specification_set_subset (fun (z) => is_lower_bound 𝓐 X z) (setPO(𝓐))
            let h₁ := And.right h𝓐 (𝓐 ▾ X) h₀
            Exists.elim h₁ (
              fun (α) =>
                fun (hα : is_supremum 𝓐 Xlow α) =>
                  let u₁ := And.left hα
                  let u₂ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 Xlow α) u₁
                  let u₃ := And.left u₂
                  Exists.intro α (And.intro (
                    Iff.mpr (low_bou_set_is_low_bou 𝓐 X α) (
                      And.intro (u₃) (
                        fun (m) =>
                          fun (hm : m ∈ X) =>
                            let u₄ := Iff.mpr (low_bou_set_is_low_bou 𝓐 (𝓐 ▴ (𝓐 ▾ X)) α) (
                              And.intro (u₃) (
                                fun (y) =>
                                  fun (hy : y ∈ (𝓐 ▴ (𝓐 ▾ X))) =>
                                    And.right hα y hy
                              )
                            )

                            let u₅ := eq_subst (fun (t) => α ∈ t) (𝓐 ▾ (𝓐 ▴ (𝓐 ▾ X))) (𝓐 ▾ X) (
                              low_upp_low_is_upp 𝓐 X hX
                            ) (u₄)

                            And.right (Iff.mp (low_bou_set_is_low_bou 𝓐 X α) u₅) m hm

                      )
                    )
                  ) (
                    fun (x) =>
                      fun (hx : x ∈ 𝓐 ▾ X) =>
                        let u₁ := And.left hα
                        And.right (Iff.mp (upp_bou_set_is_upp_bou 𝓐 Xlow α) u₁) x hx
                  ))
            )
    )
    (
      fun (h𝓐 : ∀ X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X)) =>
      And.intro (hPart) (
        fun (X) =>
          fun (hX : (X ⊆ setPO(𝓐))) =>
              let Xup := 𝓐 ▴ X
              let h₀ := specification_set_subset (fun (z) => is_upper_bound 𝓐 X z) (setPO(𝓐))
              let h₁ := h𝓐 (𝓐 ▴ X) h₀
              Exists.elim h₁ (
                fun (α) =>
                  fun (hα : is_infimum 𝓐 Xup α) =>
                    let u₁ := And.left hα
                    let u₂ := Iff.mp (low_bou_set_is_low_bou 𝓐 Xup α) u₁
                    let u₃ := And.left u₂
                    Exists.intro α (And.intro (
                      Iff.mpr (upp_bou_set_is_upp_bou 𝓐 X α) (
                        And.intro (u₃) (
                          fun (m) =>
                            fun (hm : m ∈ X) =>
                              let u₄ := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 (𝓐 ▾ (𝓐 ▴ X)) α) (
                                And.intro (u₃) (
                                  fun (y) =>
                                    fun (hy : y ∈ (𝓐 ▾ (𝓐 ▴ X))) =>
                                      And.right hα y hy
                                )
                              )

                              let u₅ := eq_subst (fun (t) => α ∈ t) (𝓐 ▴ (𝓐 ▾ (𝓐 ▴ X))) (𝓐 ▴ X) (
                                upp_low_upp_is_low 𝓐 X hX
                              ) (u₄)

                              And.right (Iff.mp (upp_bou_set_is_upp_bou 𝓐 X α) u₅) m hm

                        )
                      )
                    ) (
                      fun (x) =>
                        fun (hx : x ∈ 𝓐 ▴ X) =>
                          let u₁ := And.left hα
                          And.right (Iff.mp (low_bou_set_is_low_bou 𝓐 Xup α) u₁) x hx
                    ))
              )
            )
    )


theorem compl_latt_is_latt : ∀ 𝓐, (CompLatt 𝓐) → (Latt 𝓐) :=
  fun (𝓐) =>
    fun (h𝓐 : (CompLatt 𝓐)) =>
      And.intro (And.left h𝓐) (
        fun (x) =>
          fun (hx : x ∈ setPO(𝓐)) =>
            fun (y) =>
              fun (hy : y ∈ setPO(𝓐)) =>
                let u₀ := fun (t) =>
                  fun (ht : t ∈ {x, y}) =>
                    Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair x y t) ht)
                    (
                      fun (ht₁ : t = x) =>
                        eq_subst (fun (r) => r ∈ setPO(𝓐)) x t (Eq.symm ht₁) (hx)
                    )
                    (
                      fun (ht₂ : t = y) =>
                        eq_subst (fun (r) => r ∈ setPO(𝓐)) y t (Eq.symm ht₂) (hy)
                    )
                let u₁ := And.right h𝓐 {x, y} (u₀)
                let u₂ := Iff.mp (compl_latt_inf_crit 𝓐 (And.left h𝓐)) h𝓐 {x, y} (u₀)
                And.intro u₁ u₂
      )



theorem boolean_CompLatt : ∀ A, (CompLatt (BoolPO A)) :=
  fun (A) =>
    And.intro (boolean_PO A) (
      fun (X) =>
        fun (hX : X ⊆ setPO(BoolPO A)) =>
          let u₁ := setPO_is_setPO (𝒫 A) (subneq_binrel A) (sub_binrel A)
          let u₂ := eq_subst (fun (t) => X ⊆ t) (setPO(BoolPO A)) (𝒫 A) u₁ hX
          let u₃ := sub_bool_un_mem_bool X A u₂
          let u₄ := eq_subst (fun (t) => ⋃ X ∈ t) (𝒫 A) (setPO(BoolPO A)) (Eq.symm u₁) (u₃)
          let u₅ := lesseqPO_is_lesseqPO (𝒫 A) (subneq_binrel A) (sub_binrel A)
          Exists.intro (⋃ X) (
            And.intro (
              Iff.mpr (upp_bou_set_is_upp_bou (BoolPO A) X (⋃ X)) (
                And.intro (u₄) (
                  fun (y) =>
                    fun (hy : y ∈ X) =>
                      let u₆ := elem_subset_union X y hy
                      let u₇ := u₂ y hy
                      let u₈ := Iff.mpr (NSPO_bool_pair_prop A y u₇ (⋃ X) u₃) u₆
                      eq_subst (fun (t) => (y, ⋃ X) ∈ t) (sub_binrel A) (≼(BoolPO A)) (Eq.symm u₅) (u₈)
                )
              )
            ) (
              fun (y) =>
                fun (hy : y ∈ (BoolPO A) ▴ X) =>
                  let u₆ := Iff.mp (upp_bou_set_is_upp_bou (BoolPO A) X y) hy
                  let u₇ := eq_subst (fun (t) => y ∈ t) (setPO(BoolPO A)) (𝒫 A) (u₁) (And.left u₆)
                  let u₈ := And.right u₆

                  let v₁ := all_ss_then_union_ss X y (
                    fun (x) =>
                      fun (hx : x ∈ X) =>
                        let u₉ := eq_subst (fun (t) => x ∈ t) (setPO(BoolPO A)) (𝒫 A) (u₁) (hX x hx)
                        let u₁₀ := u₈ x hx
                        let u₁₁ := eq_subst (fun t => (x, y) ∈ t) (≼(BoolPO(A))) (sub_binrel A) (u₅) (u₁₀)
                        Iff.mp (NSPO_bool_pair_prop A x u₉ y u₇) (u₁₁)
                  )

                  eq_subst (fun (t) => (⋃ X, y) ∈ t) (sub_binrel A) (≼(BoolPO A)) (Eq.symm u₅) (
                    Iff.mpr (NSPO_bool_pair_prop A (⋃ X) u₃ y u₇) (v₁)
                  )
            )
          )

    )


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



theorem Knaster_Tarski_lemma₀ :
∀ 𝓐, ∀ a b ∈ setPO(𝓐); (a . ≼(𝓐) . b) → (CompLatt 𝓐) → (CompLatt (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐))) :=
  fun (𝓐) =>
    fun (a) =>
      fun (ha : a ∈ setPO(𝓐)) =>
        fun (b) =>
          fun (hb : b ∈ setPO(𝓐)) =>
            fun (hab : (a . ≼(𝓐) . b)) =>
              fun (h𝓐 : (CompLatt 𝓐)) =>
                let S := (⟦ a ; b ⟧ of 𝓐)
                let T := 𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)
                let u := Iff.mpr (lrc_nemp 𝓐 a ha b (And.left h𝓐)) hab
                let is_po := sub_is_PO 𝓐 (⟦ a ; b ⟧ of 𝓐) u (And.left h𝓐) (lrc_sub_all 𝓐 a b)
                let a_in_int := Iff.mpr (lrc_is_lrc 𝓐 a b a ha) (And.intro (refl_R₂ 𝓐 (And.left h𝓐) a ha) (hab))
                let eq₁ := lesseqPO_is_lesseqPO (⟦ a ; b ⟧ of 𝓐) (≺(𝓐) spec (⟦ a ; b ⟧ of 𝓐)) (≼(𝓐) spec (⟦ a ; b ⟧ of 𝓐))


                And.intro (is_po) (
                  fun (X) =>
                    fun (hX : X ⊆ (setPO(𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)))) =>
                      let u₀ := setPO_is_setPO (⟦ a ; b ⟧ of 𝓐) (≺(𝓐) spec (⟦ a ; b ⟧ of 𝓐)) (≼(𝓐) spec (⟦ a ; b ⟧ of 𝓐))
                      let u₁ := eq_subst (fun (t) => X ⊆ t) (setPO(𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐))) (⟦ a ; b ⟧ of 𝓐) u₀ hX
                      let u₂ := specification_set_subset (fun (r) => is_upper_bound (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) X r) (
                        setPO(𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐))
                      )
                      let u₃ := eq_subst (fun (m) => ((𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) ▴ X) ⊆ m) setPO(𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) (⟦ a ; b ⟧ of 𝓐) u₀ u₂


                      Or.elim (em (X = ∅))
                      (
                        fun (hemp : (X = ∅)) =>
                          let v₁ :=
                            fun (s) =>
                              fun (hs : s ∈ (⟦ a ; b ⟧ of 𝓐)) =>
                                Iff.mpr (upp_bou_set_is_upp_bou (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) X s) (
                                  eq_subst (fun (t) => is_upper_bound (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) t s) ∅ X (Eq.symm hemp) (
                                    And.intro (
                                      eq_subst (fun (v) => s ∈ v) (⟦ a ; b ⟧ of 𝓐) (setPO(𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐))) (
                                        Eq.symm u₀) hs
                                    ) (
                                      fun (r) =>
                                        fun (hr : r ∈ ∅) =>
                                          False.elim (
                                            empty_set_is_empty r (hr)
                                          )
                                    )
                                  )
                                )

                          let v₂ := sub_sub_then_eq ((𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) ▴ X) (⟦ a ; b ⟧ of 𝓐) (
                            u₃
                          ) (v₁)

                          let v₄ := And.intro (a_in_int) (
                            fun (x) =>
                              fun (hx : x ∈ (⟦ a ; b ⟧ of 𝓐)) =>
                                let u := lrc_sub_all 𝓐 a b x hx

                                let v := Iff.mp (lrc_is_lrc 𝓐 a b x u) hx

                                let v₂ := Iff.mpr (cartesian_product_pair_prop (⟦ a ; b ⟧ of 𝓐) (⟦ a ; b ⟧ of 𝓐) a x) (
                                    And.intro (a_in_int) (hx))
                                let specax := Iff.mpr (intersect_2sets_prop (≼(𝓐)) ((⟦ a ; b ⟧ of 𝓐) × (⟦ a ; b ⟧ of 𝓐)) (a, x)) (
                                  And.intro (And.left v) (v₂)
                                )


                                eq_subst (fun (t) => (a, x) ∈ t) (≼(𝓐) spec (⟦ a ; b ⟧ of 𝓐)) (
                                  ≼(𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐))) (Eq.symm (eq₁)) (specax)
                          )

                          let v₅ := eq_subst (fun (t) => is_minimum (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) t a) (
                            (⟦ a ; b ⟧ of 𝓐)) ((𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) ▴ X) (Eq.symm v₂) (v₄)


                          Exists.intro a (
                            v₅
                          )
                      )
                      (
                        fun (hnemp : (X ≠ ∅)) =>
                          let v₁ := Iff.mp (set_non_empty_iff_non_empty X) hnemp
                          Exists.elim v₁ (
                            fun (k) =>
                              fun (hk : k ∈ X) =>
                                let v₂ := lrc_sub_all 𝓐 a b
                                let v₃ := subset_trans X (⟦ a ; b ⟧ of 𝓐) (setPO(𝓐)) u₁ v₂

                                let v₄ := And.right h𝓐 X v₃

                                Exists.elim v₄ (
                                  fun (m) =>
                                    fun (hm : is_supremum 𝓐 X m) =>

                                      let v₅ := And.left hm
                                      let v₆ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 X m) v₅
                                      let v₇ := And.left v₆
                                      let v₈ := And.right v₆ k hk
                                      let v₉ := u₁ k hk
                                      let v₁₀ := v₂ k v₉
                                      let v₁₁ := And.left (Iff.mp (lrc_is_lrc 𝓐 a b k v₁₀) v₉)
                                      let v₁₂ := trans_R₂ 𝓐 (And.left h𝓐) a k m v₁₁ v₈
                                      let v₁₄ := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 X b) (
                                        And.intro (hb) (
                                          fun (r) =>
                                            fun (hr : r ∈ X) =>
                                              let v₁₅ := u₁ r hr
                                              let v₁₆ := v₂ r v₁₅
                                              And.right (Iff.mp (lrc_is_lrc 𝓐 a b r v₁₆) v₁₅)
                                        )
                                      )
                                      let v₁₇ := And.right hm b v₁₄
                                      let v₁₈ := Iff.mpr (lrc_is_lrc 𝓐 a b m v₇) (And.intro (v₁₂) (v₁₇))
                                      let v₁₉ := eq_subst (fun (t) => m ∈ t) (⟦ a ; b ⟧ of 𝓐) setPO(T) (Eq.symm u₀) (v₁₈)



                                      Exists.intro m (

                                        And.intro (

                                          Iff.mpr (upp_bou_set_is_upp_bou T X m) (

                                            And.intro (v₁₉) (
                                              fun (y) =>
                                                fun (hy : y ∈ X) =>
                                                  eq_subst (fun (t) => (y, m) ∈ t) (≼(𝓐) spec S) (≼(T)) (
                                                    Eq.symm eq₁) (
                                                      Iff.mpr (intersect_2sets_prop (≼(𝓐)) (S × S) (y, m)) (
                                                        And.intro (And.right v₆ y hy) (
                                                          Iff.mpr (cartesian_product_pair_prop S S y m) (
                                                            And.intro (u₁ y hy) (v₁₈)
                                                          )
                                                        )
                                                      )
                                                    )
                                            )
                                          )

                                        ) (
                                          fun (y) =>
                                            fun (hy : y ∈ (T ▴ X)) =>
                                              let v₂₀ := specification_set_subset (fun (t) => is_upper_bound T X t) (setPO(T)) y hy
                                              let v₂₁ := eq_subst (fun (t) => y ∈ t) (setPO(T)) (S) (u₀) (v₂₀)
                                              let v₂₂ := And.right (Iff.mp (upp_bou_set_is_upp_bou T X y) hy)
                                              let v₂₃ := lrc_sub_all 𝓐 a b y v₂₁

                                              let v₂₄ := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 X y) (
                                                And.intro (v₂₃) (
                                                  fun (i) =>
                                                    fun (hi : i ∈ X) =>
                                                      let v₂₅ := v₂₂ i hi
                                                      let v₂₆ := eq_subst (fun (t) => (i, y) ∈ t) (≼(T)) (≼(𝓐) spec S) eq₁ (v₂₅)
                                                      And.left (interset2sets_subset_prop (≼(𝓐)) (S × S)) (i, y) v₂₆

                                                )
                                              )
                                              let v₂₇ := And.right hm y v₂₄
                                              eq_subst (fun (t) => (m, y) ∈ t) (≼(𝓐) spec S) (≼(T)) (Eq.symm eq₁) (
                                                Iff.mpr (intersect_2sets_prop (≼(𝓐)) (S × S) (m, y)) (
                                                  And.intro (v₂₇) (
                                                    Iff.mpr (cartesian_product_pair_prop S S m y) (
                                                      And.intro (v₁₈) (v₂₁)
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


theorem Knaster_Tarski_lemma₁ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (𝓐 MaxExi (f FixOn 𝓐)) :=
  fun (𝓐) =>
    fun (f) =>
      fun (h𝓐 : (CompLatt 𝓐)) =>
        fun (hf : (f MotFunRelOn 𝓐)) =>
          let L := {m ∈ setPO(𝓐) | (m . (≼(𝓐)) . (f⦅m⦆)) }
          let u₀ := specification_set_subset (fun (t) => (t . (≼(𝓐)) . (f⦅t⦆))) (setPO(𝓐))
          let u₁ := And.right h𝓐 L (u₀)
          Exists.elim u₁ (
            fun (n) =>
              fun (hn : is_supremum 𝓐 L n) =>
                Exists.intro n (
                  And.intro (

                      Iff.mpr (spec_is_spec (fun (r) => f⦅r⦆ = r) (setPO(𝓐)) n) (

                        let u₂ := And.left hn
                        let u₃ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 L n) u₂
                        let u₄ := And.left u₃
                        And.intro (u₄) (

                          let u₅ := fun (x) =>
                            fun (hx : x ∈ L) =>
                              let v₀ := (Iff.mp (spec_is_spec (fun (r) => (r . (≼(𝓐)) . (f⦅r⦆))) (setPO(𝓐)) x) hx)
                              let v₁ := And.right v₀
                              let v₂ := And.left v₀
                              let v₃ := And.right u₃ x hx
                              let v₄ := And.right hf x v₂ n u₄ v₃
                              let v₅ := trans_R₂ 𝓐 (And.left h𝓐) x (f⦅x⦆) (f⦅n⦆) v₁ v₄
                              And.intro v₃ v₅

                          let u₄₁ := And.left hf
                          let u₄₂ := val_in_B f (setPO(𝓐)) (setPO(𝓐)) u₄₁ n u₄


                          let u₆ := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 (L) (f⦅n⦆)) (
                            And.intro (u₄₂) (fun (t) => fun (ht : t ∈ L) => And.right (u₅ t ht))
                          )

                          let u₇ := And.right hn (f⦅n⦆) u₆

                          let u₈ := And.right hf n u₄ (f⦅n⦆) u₄₂ u₇

                          let u₉ := Iff.mpr (spec_is_spec (fun (r) => (r . (≼(𝓐)) . (f⦅r⦆))) (setPO(𝓐)) (f⦅n⦆)) (
                            And.intro (u₄₂) (u₈)
                          )

                          let u₁₀ := And.left (u₅ (f⦅n⦆) u₉)

                          antisymm_R₂ 𝓐 (And.left h𝓐) (f⦅n⦆) n u₁₀ u₇

                        )

                      )

                  ) (
                    fun (m) =>
                      fun (hm : m ∈ (f FixOn 𝓐)) =>
                        let u₂ := And.left hn
                        let u₃ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 (L) n) u₂
                        And.right u₃ m (
                          let u₄ := Iff.mp ( (spec_is_spec (fun (t) => (f⦅t⦆ = t))) (setPO(𝓐)) m ) hm
                          let u₅ := And.left u₄
                          let u₆ := And.right u₄
                          Iff.mpr (spec_is_spec (fun (t) => (t . (≼(𝓐)) . (f⦅t⦆)) ) (setPO(𝓐)) m) (
                            And.intro (u₅) (
                              eq_subst (fun (q) => (m . (≼(𝓐)) . q)) m (f⦅m⦆) (Eq.symm u₆) (
                                refl_R₂ 𝓐 (And.left h𝓐) m u₅
                              )
                            )
                          )
                        )
                  )
                )
          )



theorem Knaster_Tarski_lemma₂ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (𝓐 MinExi (f FixOn 𝓐)) :=
  fun (𝓐) =>
    fun (f) =>
      fun (h𝓐 : (CompLatt 𝓐)) =>
        fun (hf : (f MotFunRelOn 𝓐)) =>
          let L := {m ∈ setPO(𝓐) | ((f⦅m⦆) . (≼(𝓐)) . (m)) }
          let u₀ := specification_set_subset (fun (t) => ((f⦅t⦆) . (≼(𝓐)) . (t))) (setPO(𝓐))
          let u₁ := Iff.mp (compl_latt_inf_crit 𝓐 (And.left h𝓐)) h𝓐 L u₀
          Exists.elim u₁ (
            fun (n) =>
              fun (hn : is_infimum 𝓐 L n) =>
                Exists.intro n (
                  And.intro (

                      Iff.mpr (spec_is_spec (fun (r) => f⦅r⦆ = r) (setPO(𝓐)) n) (

                        let u₂ := And.left hn
                        let u₃ := Iff.mp (low_bou_set_is_low_bou 𝓐 L n) u₂
                        let u₄ := And.left u₃
                        And.intro (u₄) (

                          let u₅ := fun (x) =>
                            fun (hx : x ∈ L) =>
                              let v₀ := (Iff.mp (spec_is_spec (fun (r) => ((f⦅r⦆) . (≼(𝓐)) . r)) (setPO(𝓐)) x) hx)
                              let v₁ := And.right v₀
                              let v₂ := And.left v₀
                              let v₃ := And.right u₃ x hx
                              let v₄ := And.right hf n u₄ x v₂ v₃
                              let v₅ := trans_R₂ 𝓐 (And.left h𝓐) (f⦅n⦆) (f⦅x⦆) x v₄ v₁
                              And.intro v₃ v₅

                          let u₄₁ := And.left hf
                          let u₄₂ := val_in_B f (setPO(𝓐)) (setPO(𝓐)) u₄₁ n u₄


                          let u₆ := Iff.mpr (low_bou_set_is_low_bou 𝓐 (L) (f⦅n⦆)) (
                            And.intro (u₄₂) (fun (t) => fun (ht : t ∈ L) => And.right (u₅ t ht))
                          )

                          let u₇ := And.right hn (f⦅n⦆) u₆

                          let u₈ := And.right hf (f⦅n⦆) u₄₂ n u₄ u₇

                          let u₉ := Iff.mpr (spec_is_spec (fun (r) => ((f⦅r⦆) . (≼(𝓐)) . r)) (setPO(𝓐)) (f⦅n⦆)) (
                            And.intro (u₄₂) (u₈)
                          )

                          let u₁₀ := And.left (u₅ (f⦅n⦆) u₉)

                          antisymm_R₂ 𝓐 (And.left h𝓐) (f⦅n⦆) n u₇ u₁₀

                        )

                      )

                  ) (
                    fun (m) =>
                      fun (hm : m ∈ (f FixOn 𝓐)) =>
                        let u₂ := And.left hn
                        let u₃ := Iff.mp (low_bou_set_is_low_bou 𝓐 (L) n) u₂
                        And.right u₃ m (
                          let u₄ := Iff.mp ( (spec_is_spec (fun (t) => (f⦅t⦆ = t))) (setPO(𝓐)) m ) hm
                          let u₅ := And.left u₄
                          let u₆ := And.right u₄
                          Iff.mpr (spec_is_spec (fun (t) => (((f⦅t⦆) . (≼(𝓐)) . t)) ) (setPO(𝓐)) m) (
                            And.intro (u₅) (
                              eq_subst (fun (q) => (q . (≼(𝓐)) . m)) m (f⦅m⦆) (Eq.symm u₆) (
                                refl_R₂ 𝓐 (And.left h𝓐) m u₅
                              )
                            )
                          )
                        )
                  )
                )
          )




theorem Knaster_Tarski_lemma₃ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → ((f FixOn 𝓐) ≠ ∅) :=
  fun (𝓐) =>
    fun (f) =>
      fun (h𝓐 : (CompLatt 𝓐)) =>
        fun (hf : (f MotFunRelOn 𝓐)) =>
          let u₁ := Knaster_Tarski_lemma₁ 𝓐 f h𝓐 hf
          Exists.elim u₁ (
            fun (maxel) =>
              fun (hmaxel : is_maximum 𝓐 (f FixOn 𝓐) maxel) =>
                let u₂ := And.left hmaxel
                fun (hemp : (f FixOn 𝓐) = ∅) =>
                  let u₃ := eq_subst (fun (t) => maxel ∈ t) (f FixOn 𝓐) (∅) (hemp) (u₂)
                  let u₄ := empty_set_is_empty maxel
                  u₄ u₃
          )



theorem Knaster_Tarski_theorem : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (CompLatt (𝓐 SubsPO (f FixOn 𝓐))) :=
  fun (𝓐) =>
    fun (f) =>
      fun (h𝓐 : (CompLatt 𝓐)) =>
        fun (hf : (f MotFunRelOn 𝓐)) =>
          And.intro (sub_is_PO 𝓐 (f FixOn 𝓐) (Knaster_Tarski_lemma₃ 𝓐 f h𝓐 hf) (And.left h𝓐) (
            specification_set_subset (fun (t) => f⦅t⦆ = t) (setPO(𝓐))
          ))
          (
            fun (X) =>
              fun (hX : X ⊆ setPO(𝓐 SubsPO (f FixOn 𝓐))) =>
                let Fix := (f FixOn 𝓐)
                let Sub := 𝓐 SubsPO (f FixOn 𝓐)
                let u₀ := specification_set_subset (fun (r) => (f⦅r⦆) = r) (setPO(𝓐))

                let u₁ := setPO_is_setPO (f FixOn 𝓐) (≺(𝓐) spec (f FixOn 𝓐)) (≼(𝓐) spec (f FixOn 𝓐))
                let u_less := lesseqPO_is_lesseqPO (f FixOn 𝓐) (≺(𝓐) spec (f FixOn 𝓐)) (≼(𝓐) spec (f FixOn 𝓐))

                let u₂ := eq_subst (fun (t) => X ⊆ t) (setPO(𝓐 SubsPO (f FixOn 𝓐))) (f FixOn 𝓐) (u₁) (hX)
                let u₃ := subset_trans X (f FixOn 𝓐) (setPO(𝓐)) u₂ u₀

                let u₄ := And.right h𝓐 (setPO(𝓐)) (subset_refl (setPO(𝓐)))
                Exists.elim (u₄) (
                  fun (a) =>
                    fun (ha : is_supremum 𝓐 (setPO(𝓐)) a) =>
                      let u₅ := And.right h𝓐 X (u₃)
                      Exists.elim (u₅) (
                        fun (m) =>
                          fun (hm : is_supremum 𝓐 X m) =>

                            let u₇ := And.left hm
                            let u₈ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 X m) u₇
                            let u₉ := And.left u₈

                            let u₆ := fun (x) =>
                              fun (hx : x ∈ X) =>
                                let u₇₀ := u₃ x hx
                                let u₁₀ := And.right u₈ x hx
                                let u₁₁ := And.right hf x u₇₀ m u₉ u₁₀
                                let u₁₂ := u₂ x hx
                                let u₁₃ := And.right (Iff.mp (spec_is_spec (fun (r) => (f⦅r⦆) = r) (setPO(𝓐)) x) u₁₂)
                                let u₁₄ := eq_subst (fun (t) => (t . ≼(𝓐) . (f⦅m⦆))) (f⦅x⦆) x (u₁₃) (u₁₁)
                                u₁₄

                            let u₁₀ := val_in_B f (setPO(𝓐)) (setPO(𝓐)) (And.left hf) m (u₉)

                            let u₈ := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 X (f⦅m⦆)) (
                              And.intro (u₁₀) (
                                u₆
                              )
                            )

                            let u₁₁ := And.right hm (f⦅m⦆) u₈


                            let R := ⟦ m ; a ⟧ of 𝓐

                            let u₁₂ := fun (y) =>
                              fun (hy : y ∈ R) =>
                                let u₁₃ := lrc_sub_all 𝓐 m a y hy
                                let u₁₄ := Iff.mp (lrc_is_lrc 𝓐 m a y (u₁₃)) hy
                                let u₁₅ := And.left u₁₄
                                let u₁₇ := And.right hf m u₉ y u₁₃ u₁₅
                                let u₁₈ := trans_R₂ 𝓐 (And.left h𝓐) m (f⦅m⦆) ((f⦅y⦆)) u₁₁ u₁₇
                                let u₁₉ := And.left ha
                                let u₂₀ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 (setPO(𝓐)) a) u₁₉
                                let u₂₁ := val_in_B f (setPO(𝓐)) (setPO(𝓐)) (And.left hf) y (u₁₃)
                                let u₂₂ := And.right u₂₀ (f⦅y⦆) u₂₁
                                Iff.mpr (lrc_is_lrc 𝓐 m a (f⦅y⦆) u₂₁) (And.intro (u₁₈) (u₂₂))

                            let spec_f := f ⨡ R

                            let f_fun := fun_restriction_prop (setPO(𝓐)) (setPO(𝓐)) R f (And.left hf)
                            let R_sub := lrc_sub_all 𝓐 m a
                            let int_prp := Iff.mp (And.left (subset_using_equality R setPO(𝓐))) R_sub
                            let int_prp₂ := intersec2_comm (setPO(𝓐)) R
                            let int_prp₃ := Eq.trans int_prp₂ int_prp
                            let f_fun₂ := eq_subst (fun (t) => (f ⨡ R) Fun t To (setPO(𝓐))) (set_PO (𝓐) ∩ R) R (
                              int_prp₃) (f_fun)

                            let u₁₃ := fun_restriction_val (setPO(𝓐)) (setPO(𝓐)) R f R_sub (And.left hf)
                            let u₁₄ := fun (y) => fun (hy : y ∈ R) =>
                              let u₁₅ := u₁₂ y hy
                              let u₁₆ := u₁₃ y hy
                              eq_subst (fun (t) => t ∈ R) (f⦅y⦆) ((f ⨡ R)⦅y⦆) (u₁₆) (u₁₅)

                            let u₁₅ := if_val_in_C (spec_f) R (setPO(𝓐)) R f_fun₂ (u₁₄)


                            let RLat := 𝓐 SubsPO R

                            let a_set₀ := And.left ha
                            let a_set₁ := And.left (Iff.mp (upp_bou_set_is_upp_bou 𝓐 (setPO(𝓐)) a) a_set₀)

                            let a_set₂ := And.right (Iff.mp (upp_bou_set_is_upp_bou 𝓐 (setPO(𝓐)) a) a_set₀) m (u₉)

                            let is_latR : CompLatt RLat := Knaster_Tarski_lemma₀ 𝓐 m (u₉) a (a_set₁) a_set₂ (h𝓐)


                            let setpo_latR := setPO_is_setPO R ((≺(𝓐)) spec R) (≼(𝓐) spec R)
                            let spec_latR := lesseqPO_is_lesseqPO R ((≺(𝓐)) spec R) (≼(𝓐) spec R)

                            let specf_Rlat := eq_subst (fun (t) => spec_f Fun t To t) (R) (setPO(RLat)) (Eq.symm setpo_latR) (
                              u₁₅)

                            let mon_spec : (spec_f MotFunRelOn RLat) := And.intro (specf_Rlat) (fun (x) =>
                              fun (hx : x ∈ setPO(RLat)) =>
                                fun (y) =>
                                  fun (hy : y ∈  setPO(RLat)) =>
                                    fun (hxy : (x . ≼(RLat) . y)) =>
                                      let xR := eq_subst (fun (t) => x ∈ t) (setPO(RLat)) R (setpo_latR) (hx)
                                      let yR := eq_subst (fun (t) => y ∈ t) (setPO(RLat)) R (setpo_latR) (hy)
                                      eq_subst (fun (t) => ((spec_f⦅x⦆) . t . (spec_f⦅y⦆))) (≼(𝓐) spec R) (≼(RLat)) (
                                        Eq.symm spec_latR) (
                                            Iff.mpr (intersect_2sets_prop (≼(𝓐)) (R × R) ((spec_f⦅x⦆), (spec_f⦅y⦆))) (
                                              And.intro (
                                                eq_subst (fun (t) => (t . (≼(𝓐)) . (spec_f⦅y⦆))) (f⦅x⦆) (spec_f⦅x⦆) (u₁₃ x xR) (
                                                  eq_subst (fun (t) => ((f⦅x⦆) . (≼(𝓐)) . t)) (f⦅y⦆) (spec_f⦅y⦆) (u₁₃ y yR) (
                                                    let xA := R_sub x xR
                                                    let yA := R_sub y yR
                                                    And.right hf x xA y yA (
                                                      let xyRlat := eq_subst (fun (t) => (x . t . y)) (≼(RLat)) (≼(𝓐) spec R) (spec_latR) (hxy)
                                                      And.left (Iff.mp (intersect_2sets_prop (≼(𝓐)) (R × R) (x, y)) (xyRlat))
                                                    )

                                                  )
                                                )
                                              ) (
                                                Iff.mpr (cartesian_product_pair_prop R R (spec_f⦅x⦆) (spec_f⦅y⦆)) (
                                                  And.intro (
                                                    val_in_B spec_f R R u₁₅ x xR
                                                  ) (
                                                    val_in_B spec_f R R u₁₅ y yR
                                                  )
                                                )
                                              )
                                            )
                                        )
                            )


                          let min_rlat := Knaster_Tarski_lemma₂ (RLat) (spec_f) (is_latR) mon_spec
                          Exists.elim min_rlat (
                            fun (r) =>
                              fun (hr : is_minimum (RLat) (spec_f FixOn RLat) r) =>

                                let M := (spec_f FixOn RLat)
                                let N := (Sub ▴ X)

                                let u₁₆ : M ⊆ N := fun (x) =>
                                    fun (hx : x ∈ M) =>
                                      let u₁₇ := specification_set_subset (fun (t) => (spec_f⦅t⦆ = t)) (setPO(RLat)) x hx
                                      let u₁₈ := eq_subst (fun (t) => x ∈ t) (setPO(RLat)) R (setpo_latR) (u₁₇)
                                      let u₁₉ := R_sub x u₁₈
                                      let u₂₀ := And.left (Iff.mp (lrc_is_lrc 𝓐 m a x u₁₉) u₁₈)
                                      let v₂ := And.right (Iff.mp (spec_is_spec (fun (t) => (spec_f⦅t⦆ = t)) (setPO(RLat)) x)
                                             hx)
                                      let v₃ := u₁₃ x u₁₈



                                      let v₄ := eq_subst (fun (t) => f⦅x⦆ = t) (spec_f⦅x⦆) x v₂ v₃
                                      let v₀ := eq_subst (fun (t) => x ∈ t) (f FixOn 𝓐) (setPO(Sub)) (Eq.symm u₁) (

                                        Iff.mpr (spec_is_spec (fun (P) => (f⦅P⦆) = P) (setPO(𝓐)) x) (
                                          And.intro (u₁₉) (
                                            v₄


                                          )
                                        )
                                      )
                                      let u₂₃ := Iff.mpr (upp_bou_set_is_upp_bou Sub X x) (
                                        And.intro (v₀) (

                                          fun (e) =>
                                            fun (he : e ∈ X) =>
                                              eq_subst (fun (t) => (e, x) ∈ t) (≼(𝓐) spec Fix) (≼(Sub)) (Eq.symm u_less) (

                                                Iff.mpr (intersect_2sets_prop (≼(𝓐)) (Fix × Fix) (e, x)) (
                                                  And.intro (

                                                    trans_R₂ 𝓐 (And.left h𝓐) e m x (
                                                      let v₅ := And.left hm
                                                      And.right (Iff.mp (upp_bou_set_is_upp_bou 𝓐 X m) v₅) e he
                                                    ) (
                                                        u₂₀
                                                    )
                                                  ) (
                                                    Iff.mpr (cartesian_product_pair_prop Fix Fix e x) (
                                                      And.intro (u₂ e he) (
                                                        Iff.mpr (spec_is_spec (fun (P) => f⦅P⦆ = P) (setPO(𝓐)) x) (
                                                          And.intro (u₁₉) (v₄)
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                        )
                                      )
                                      u₂₃

                                let u₁₇ : N ⊆ M := fun (x) =>
                                  fun (hx : x ∈ N) =>
                                    let upp_x := Iff.mp (upp_bou_set_is_upp_bou Sub X x) hx
                                    let upp_x₀ := And.left upp_x
                                    let upp_x₁ := eq_subst (fun (t) => x ∈ t) (setPO(Sub)) (Fix) (u₁) (upp_x₀)
                                    let upp_x₂ := u₀ x upp_x₁
                                    Iff.mpr (spec_is_spec (fun (P) => spec_f⦅P⦆ = P) (setPO(RLat)) x) (

                                      let xR := Iff.mpr (lrc_is_lrc 𝓐 m a x (upp_x₂)) (
                                            And.intro (

                                              And.right hm x (
                                                Iff.mpr (upp_bou_set_is_upp_bou 𝓐 X x) (
                                                  And.intro (upp_x₂) (
                                                    fun (s) =>
                                                      fun (hs : s ∈ X) =>
                                                        let u₁₈ := And.right upp_x s hs

                                                        let u₁₉ := eq_subst (fun (t) => (s, x) ∈ t) (≼(Sub)) (≼(𝓐) spec Fix) (u_less) (u₁₈)

                                                        And.left (interset2sets_subset_prop (≼(𝓐)) (Fix × Fix)) (s, x) u₁₉
                                                  )
                                                )
                                              )
                                            ) (
                                              let u₁₈ := And.left ha
                                              And.right ((Iff.mp (upp_bou_set_is_upp_bou 𝓐 (setPO(𝓐)) a)) u₁₈) x (upp_x₂)
                                            )
                                          )

                                      And.intro (
                                        eq_subst (fun (t) => x ∈ t) (R) (setPO(RLat)) (Eq.symm setpo_latR) (
                                          xR
                                        )
                                      ) (

                                        let u₁₈ := And.right (Iff.mp (spec_is_spec (fun (P) => f⦅P⦆ = P) (setPO(𝓐)) x) upp_x₁)

                                        let u₁₉ := Eq.symm (u₁₃ x (

                                          xR
                                        ))

                                        Eq.trans u₁₉ (u₁₈)
                                      )
                                    )


                                    let u₁₈ := sub_sub_then_eq M N (u₁₆) (u₁₇)

                                    let hr_N := eq_subst (fun (t) => is_minimum RLat t r) M N (u₁₈) (hr)
                                    let hr_N₀ := And.left hr_N
                                    let rupp := And.left (Iff.mp (upp_bou_set_is_upp_bou Sub X r) hr_N₀)
                                    let rwhe := eq_subst (fun (P) => r ∈ P) (setPO(Sub)) (Fix) (u₁) (rupp)
                                    let hr_N₁ := fun (t) =>
                                      fun (ht : t ∈ N) =>
                                        let tupp := And.left (Iff.mp (upp_bou_set_is_upp_bou Sub X t) ht)
                                        let twhe := eq_subst (fun (P) => t ∈ P) (setPO(Sub)) (Fix) (u₁) tupp
                                        let u₁₉ := And.right hr_N t ht
                                        let u₂₀ := eq_subst (fun (P) => (r, t) ∈ P) (≼(RLat)) (≼(𝓐) spec R) (spec_latR) (u₁₉)
                                        let u₂₁ := And.left (interset2sets_subset_prop (≼(𝓐)) (R × R)) (r, t) u₂₀
                                        let u₂₂ := Iff.mpr (intersect_2sets_prop (≼(𝓐)) (Fix × Fix) (r, t)) (
                                          And.intro (u₂₁) (
                                            Iff.mpr (cartesian_product_pair_prop Fix Fix r t) (
                                              And.intro (rwhe) (twhe)
                                            )
                                          )
                                        )
                                        let u₂₃ := eq_subst (fun (P) => (r, t) ∈ P) (≼(𝓐) spec Fix) (≼(Sub)) (Eq.symm (u_less)) (
                                          u₂₂
                                        )
                                        u₂₃

                                    let hr_N₂ : is_minimum Sub (Sub ▴ X) r := And.intro hr_N₀ hr_N₁

                                Exists.intro r (
                                  hr_N₂
                                )
                          )
                      )
                )
          )



def is_linear_order (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧ (str_conn ≼(𝓐) setPO(𝓐))
syntax "LinOrd" term : term
macro_rules
| `(LinOrd $𝓐) => `(is_linear_order $𝓐)



theorem lin_ord_prop : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∨ (y . (≼(𝓐)) . x)) :=
  fun (𝓐) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (x) =>
        fun (hx : x ∈ setPO(𝓐)) =>
          fun (y) =>
            fun (hy : y ∈ setPO(𝓐)) =>
              And.right h𝓐 x hx y hy

theorem lin_ord_wk_prop : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (x ≠ y) → ((x . ≺(𝓐) . y) ∨ (y . (≺(𝓐)) . x))) :=
  fun (𝓐) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (x) =>
        fun (hx : (x ∈ setPO(𝓐))) =>
          fun (y) =>
            fun (hy : (y ∈ setPO(𝓐))) =>
              fun (hnxy : (x ≠ y)) =>
                let u := lin_ord_prop 𝓐 h𝓐 x hx y hy
                Or.elim u
                (
                  fun (hxy : (x . (≼(𝓐)) . y)) =>
                    let v₀ := Iff.mpr (And.left (part_ord_pair_prop 𝓐 (And.left h𝓐) x hx y hy)) (And.intro hxy hnxy)
                    Or.inl v₀
                )
                (
                  fun (hxy : (y . (≼(𝓐)) . x)) =>
                    let v₀ := Iff.mpr (And.left (part_ord_pair_prop 𝓐 (And.left h𝓐) y hy x hx)) (And.intro hxy (
                      fun (hyx : (y = x)) =>
                        hnxy (Eq.symm hyx)
                    ))
                    Or.inr v₀
                )

theorem lin_ord_nR₁ : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (¬ (x . (≺(𝓐)) . y)) → (y . (≼(𝓐)) . x)) :=
  fun (𝓐) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (x) =>
        fun (hx : x ∈ setPO(𝓐)) =>
          fun (y) =>
            fun (hy : y ∈ setPO(𝓐)) =>
              fun (hnxy : ¬ (x . (≺(𝓐)) . y)) =>
                let u := lin_ord_prop 𝓐 h𝓐 x hx y hy
                Or.elim u
                (
                  fun (hxy : (x . (≼(𝓐)) . y)) =>

                    let v := Iff.mp (And.right (part_ord_pair_prop 𝓐 (And.left h𝓐) x hx y hy)) hxy
                    Or.elim v
                    (
                      fun (hxly : (x . (≺(𝓐)) . y)) =>
                        False.elim (
                          hnxy (hxly)
                        )
                    )
                    (
                      fun (hxey : (x = y)) =>
                        let s := refl_R₂ 𝓐 (And.left h𝓐) x hx
                        eq_subst (fun (t) => (t, x) ∈ (≼(𝓐))) x y (hxey) (s)

                    )
                )
                (
                  fun (hyx : (y . (≼(𝓐)) . x)) =>
                    hyx
                )


theorem lin_ord_nR₂ : ∀ 𝓐, (LinOrd 𝓐) → (∀ x y ∈ setPO(𝓐); (¬ (x . (≼(𝓐)) . y)) → (y . (≺(𝓐)) . x)) :=
  fun (𝓐) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (x) =>
        fun (hx : (x ∈ setPO(𝓐))) =>
          fun (y) =>
            fun (hy : (y ∈ setPO(𝓐))) =>
              fun (hnxy : ¬ (x . (≼(𝓐)) . y)) =>
                let u := lin_ord_prop 𝓐 h𝓐 x hx y hy
                Or.elim u
                (
                  fun (hxley : (x . ≼(𝓐) . y)) =>
                    False.elim (
                      hnxy hxley
                    )
                )
                (
                  fun (hylex : (y . ≼(𝓐) . x)) =>
                    Iff.mpr (And.left (part_ord_pair_prop 𝓐 (And.left h𝓐) y hy x hx)) (
                      And.intro (hylex) (
                        fun (hyx : y = x) =>
                          hnxy (
                            eq_subst (fun (t) => (x . (≼(𝓐)) . t)) x y (Eq.symm hyx) (
                              refl_R₂ 𝓐 (And.left h𝓐) x hx
                            )
                          )
                      )
                    )
                )


theorem inv_is_LO : ∀ 𝓐, (LinOrd 𝓐) → (LinOrd (invPO 𝓐)) :=
  fun (𝓐) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      And.intro (inv_is_PO 𝓐 (And.left h𝓐)) (
        fun (x) =>
          fun (hx : x ∈ setPO( invPO 𝓐)) =>
            fun (y) =>
              fun (hy : y ∈ setPO( invPO 𝓐 )) =>
                let v₁ := eq_subst (fun (t) => x ∈ t) (setPO( invPO 𝓐 )) (setPO(𝓐)) (setPO_is_setPO setPO(𝓐) ≻(𝓐) ≽(𝓐)) (hx)
                let v₂ := eq_subst (fun (t) => y ∈ t) (setPO( invPO 𝓐 )) (setPO(𝓐)) (setPO_is_setPO setPO(𝓐) ≻(𝓐) ≽(𝓐)) (hy)
                let u := lin_ord_prop 𝓐 h𝓐 x v₁ y v₂
                Or.elim u
                (
                  fun (hxy : (x . (≼(𝓐)) . y)) =>
                    let u₀ := Iff.mp (po_lesseq_moreeq 𝓐 (And.left h𝓐) x y) hxy
                    let u₁ := eq_subst (fun (t) => (y, x) ∈ t) (≽(𝓐)) (≼(invPO 𝓐)) (Eq.symm (
                      lesseqPO_is_lesseqPO setPO(𝓐) ≻(𝓐) ≽(𝓐)
                    )) (u₀)
                    Or.inr u₁
                )
                (
                  fun (hyx :(y . (≼(𝓐)) . x)) =>
                    let u₀ := Iff.mp (po_lesseq_moreeq 𝓐 (And.left h𝓐) y x) hyx
                    let u₁ := eq_subst (fun (t) => (x, y) ∈ t) (≽(𝓐)) (≼(invPO 𝓐)) (Eq.symm (
                      lesseqPO_is_lesseqPO setPO(𝓐) ≻(𝓐) ≽(𝓐)
                    )) (u₀)
                    Or.inl u₁
                )
      )


theorem sub_is_LO : ∀ 𝓐 B, (B ≠ ∅) → (LinOrd 𝓐) → (B ⊆ setPO(𝓐)) → (LinOrd (𝓐 SubsPO B)) :=
  fun (𝓐 B) =>
    fun (hB : (B ≠ ∅)) =>
      fun (h𝓐 : (LinOrd 𝓐)) =>
        fun (hBA : (B ⊆ setPO(𝓐))) =>
          And.intro (sub_is_PO 𝓐 B hB (And.left h𝓐) hBA) (
            fun (x) =>
              fun (hx : x ∈ setPO(𝓐 SubsPO B)) =>
                fun (y) =>
                  fun (hy : y ∈ setPO(𝓐 SubsPO B)) =>
                    let setposub := setPO_is_setPO (B) (≺(𝓐) spec B) (≼(𝓐) spec B)
                    let lesseqsub := lesseqPO_is_lesseqPO (B) (≺(𝓐) spec B) (≼(𝓐) spec B)
                    let hxB := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 SubsPO B)) B (setposub) (hx)
                    let hyB := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 SubsPO B)) B (setposub) (hy)
                    let hx𝓐 := hBA x hxB
                    let hy𝓐 := hBA y hyB
                    let u := lin_ord_prop 𝓐 h𝓐 x (hx𝓐) y (hy𝓐)
                    Or.elim u
                    (
                      fun (hxy : (x . (≼(𝓐)) . y)) =>

                        Or.inl (eq_subst (fun (t) => (x, y) ∈ t) (≼(𝓐) spec B) (≼(𝓐 SubsPO B)) (Eq.symm lesseqsub) (
                          Iff.mpr (intersect_2sets_prop (≼(𝓐)) (B × B) (x, y)) (
                            And.intro (hxy) (
                              Iff.mpr (cartesian_product_pair_prop B B x y) (And.intro hxB hyB)
                            )
                          )
                        ))
                    )
                    (
                      fun (hyx : (y . (≼(𝓐)) . x)) =>
                        Or.inr (eq_subst (fun (t) => (y, x) ∈ t) (≼(𝓐) spec B) (≼(𝓐 SubsPO B)) (Eq.symm lesseqsub) (
                          Iff.mpr (intersect_2sets_prop (≼(𝓐)) (B × B) (y, x)) (
                            And.intro (hyx) (
                              Iff.mpr (cartesian_product_pair_prop B B y x) (And.intro hyB hxB)
                            )
                          )
                        ))
                    )
          )





theorem linmin_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_minimal 𝓐 X x) ↔ (is_minimum 𝓐 X x)) :=
  fun (𝓐 X x) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (hX : X ⊆ setPO(𝓐)) =>
      Iff.intro (
        fun (hx : (is_minimal 𝓐 X x)) =>
          And.intro (And.left hx) (
            fun (y) =>
              fun (hy : y ∈ X) =>
                lin_ord_nR₁ 𝓐 h𝓐 y (hX y hy) x (hX x (And.left hx)) (
                  And.right hx y hy
                )
          )
      )
      (
        min_um_is_al 𝓐 X x (And.left h𝓐)
      )



theorem linmax_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_maximal 𝓐 X x) ↔ (is_maximum 𝓐 X x)):=
  fun (𝓐 X x) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (hX : X ⊆ setPO(𝓐)) =>
        Iff.intro (
        fun (hx : (is_maximal 𝓐 X x)) =>
          And.intro (And.left hx) (
            fun (y) =>
              fun (hy : y ∈ X) =>
                lin_ord_nR₁ 𝓐 h𝓐 x (hX x (And.left hx)) y (hX y hy) (
                  And.right hx y hy
                )
          )
        )
        (
          max_um_is_al 𝓐 X x (And.left h𝓐)
        )


theorem linmin_al_sub_cmp : ∀ 𝓐 B C x y, (LinOrd 𝓐) →
(C ⊆ B) → (B ⊆ setPO(𝓐)) → (is_minimal 𝓐 B x) → (is_minimal 𝓐 C y) → (x . ≼(𝓐) . y) :=
  fun (𝓐 B C x y) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (hCB : (C ⊆ B)) =>
        fun (hB𝓐 : (B ⊆ setPO(𝓐))) =>
          fun (hminB : (is_minimal 𝓐 B x)) =>
            fun (hminC : (is_minimal 𝓐 C y) ) =>
              let hminumB := Iff.mp (linmin_al_um 𝓐 B x h𝓐 hB𝓐) hminB
              And.right (hminumB) y (hCB y (And.left hminC))


theorem linmax_al_sub_cmp : ∀ 𝓐 B C x y, (LinOrd 𝓐) →
(C ⊆ B) → (B ⊆ setPO(𝓐)) → (is_maximal 𝓐 B x) → (is_maximal 𝓐 C y) → (y . ≼(𝓐) . x) :=
  fun (𝓐 B C x y) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (hCB : (C ⊆ B)) =>
        fun (hB𝓐 : (B ⊆ setPO(𝓐))) =>
          fun (hmaxB : (is_maximal 𝓐 B x)) =>
            fun (hmaxC : (is_maximal 𝓐 C y) ) =>
              let hmaxumB := Iff.mp (linmax_al_um 𝓐 B x h𝓐 hB𝓐) hmaxB
              And.right (hmaxumB) y (hCB y (And.left hmaxC))



theorem lin_al_min_inter_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))
→ (B IndxFun I) → (is_minimal 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_minimal 𝓐 ((B _ i)) y) → (y . ≼(𝓐) . x) :=
   fun (𝓐 B I x) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (hsub : (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))) =>
        fun (hBI : (B IndxFun I)) =>
          fun (hminx : (is_minimal 𝓐 ((⋂[ i in I ] B at i)) x)) =>
            fun (i) =>
              fun (hi : i ∈ I) =>
                fun (y) =>
                  fun (hminy : (is_minimal 𝓐 ((B _ i)) y) ) =>
                    let u := indexed_intersection_sub_indexed B I hBI i hi
                    let u₀ := hsub i hi
                    let u₁ := subset_trans (⋂[ i in I ] B at i) (B _ i) (setPO(𝓐)) u u₀
                    let v := Iff.mp (linmin_al_um 𝓐 ((⋂[ i in I ] B at i)) x (h𝓐) u₁) hminx
                    let v₁ := Iff.mp (linmin_al_um 𝓐 (B _ i) y (h𝓐) u₀) hminy
                    min_um_sub_cmp 𝓐 (B _ i) ((⋂[ i in I ] B at i)) y x u v₁ v


theorem lin_al_max_inter_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))
→ (B IndxFun I) → (is_maximal 𝓐 ((⋂[ i in I ] B at i)) x)
 → ∀ i ∈ I; ∀ y, (is_maximal 𝓐 ((B _ i)) y) → (x . ≼(𝓐) . y) :=
   fun (𝓐 B I x) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      fun (hsub : (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))) =>
        fun (hBI : (B IndxFun I)) =>
          fun (hminx : (is_maximal 𝓐 ((⋂[ i in I ] B at i)) x)) =>
            fun (i) =>
              fun (hi : i ∈ I) =>
                fun (y) =>
                  fun (hminy : (is_maximal 𝓐 ((B _ i)) y) ) =>
                    let u := indexed_intersection_sub_indexed B I hBI i hi
                    let u₀ := hsub i hi
                    let u₁ := subset_trans (⋂[ i in I ] B at i) (B _ i) (setPO(𝓐)) u u₀
                    let v := Iff.mp (linmax_al_um 𝓐 ((⋂[ i in I ] B at i)) x (h𝓐) u₁) hminx
                    let v₁ := Iff.mp (linmax_al_um 𝓐 (B _ i) y (h𝓐) u₀) hminy
                    max_um_sub_cmp 𝓐 (B _ i) ((⋂[ i in I ] B at i)) y x u v₁ v


theorem lin_partmin_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MinExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_minimal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_minimal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimal 𝓐 (B _ i) y} x)) :=
    fun (𝓐 B I x) =>
      fun (h𝓐 : (LinOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hmin : (∀ i ∈ I; (𝓐 MinExi (B _ i)))) =>
            fun (hset : (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))) =>
              let u₀ := fun (r) =>
                fun (hr : r ∈ (⋃[i in I] B at i)) =>
                  let u₁ := Iff.mp (indexed_union_is_union B I (hBI) r) hr
                  Exists.elim u₁ (
                    fun (i) =>
                      fun (hi : i ∈ I ∧ r ∈ (B _ i)) =>
                        hset i (And.left hi) r (And.right hi)
                  )

              let T := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimum 𝓐 (B _ i) y}
              let S := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimal 𝓐 (B _ i) y}

              let TS : T ⊆ S:=
                fun (s) =>
                  fun (hs : s ∈ T) =>
                    let a := (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_minimum 𝓐 (B _ i) P) (setPO(𝓐)) s) hs)
                    Exists.elim (And.right a) (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ is_minimum 𝓐 (B _ i) s) =>
                          Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_minimal 𝓐 (B _ i) P) (setPO(𝓐)) s) (
                            And.intro (And.left a) (
                              Exists.intro i (
                                And.intro (And.left hi) (Iff.mpr (linmin_al_um 𝓐 (B _ i) s (h𝓐) (hset i (And.left hi))) (
                                  And.right hi
                                ))
                              )
                            )
                          )
                    )

              let ST := fun (s) =>
                  fun (hs : s ∈ S) =>
                    let a := (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_minimal 𝓐 (B _ i) P) (setPO(𝓐)) s) hs)
                    Exists.elim (And.right a) (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ is_minimal 𝓐 (B _ i) s) =>
                          Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_minimum 𝓐 (B _ i) P) (setPO(𝓐)) s) (
                            And.intro (And.left a) (
                              Exists.intro i (
                                And.intro (And.left hi) (Iff.mp (linmin_al_um 𝓐 (B _ i) s (h𝓐) (hset i (And.left hi))) (
                                  And.right hi
                                ))
                              )
                            )
                          )
                    )

              let TSeq := sub_sub_then_eq T S (TS) (ST)




              let u₁ := specification_set_subset (fun (P) => ∃ i ∈ I; is_minimum 𝓐 (B _ i) P) (setPO(𝓐))

              let u₂ := linmin_al_um 𝓐 (⋃[i in I] B at i) x (h𝓐) (u₀)
              let u₃ := linmin_al_um 𝓐 ({y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimum 𝓐 (B _ i) y}) x (h𝓐) (u₁)


              Iff.intro (
                fun (halx : (is_minimal 𝓐 (⋃[i in I] B at i) x) ) =>
                  let humx := Iff.mp (u₂) halx
                  let prop := Iff.mp (partmin_um_un_prop 𝓐 B I x (And.left h𝓐) hBI hmin hset) humx

                  let res := Iff.mpr u₃ (prop)

                  eq_subst (fun (t) => is_minimal 𝓐 t x) T S (TSeq) (res)

              ) (
                fun (halx : is_minimal 𝓐 S x) =>
                  let u₄ := eq_subst (fun (t) => is_minimal 𝓐 t x) S T (Eq.symm TSeq) (halx)
                  let u₅ := Iff.mp (u₃) u₄
                  let u₆ := Iff.mpr (partmin_um_un_prop 𝓐 B I x (And.left h𝓐) hBI hmin hset) u₅
                  Iff.mpr (u₂) u₆
              )



theorem lin_partmax_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 MaxExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_maximal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_maximal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximal 𝓐 (B _ i) y} x)) :=
    fun (𝓐 B I x) =>
      fun (h𝓐 : (LinOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hmin : (∀ i ∈ I; (𝓐 MaxExi (B _ i)))) =>
            fun (hset : (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))) =>
              let u₀ := fun (r) =>
                fun (hr : r ∈ (⋃[i in I] B at i)) =>
                  let u₁ := Iff.mp (indexed_union_is_union B I (hBI) r) hr
                  Exists.elim u₁ (
                    fun (i) =>
                      fun (hi : i ∈ I ∧ r ∈ (B _ i)) =>
                        hset i (And.left hi) r (And.right hi)
                  )

              let T := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximum 𝓐 (B _ i) y}
              let S := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximal 𝓐 (B _ i) y}

              let TS : T ⊆ S:=
                fun (s) =>
                  fun (hs : s ∈ T) =>
                    let a := (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_maximum 𝓐 (B _ i) P) (setPO(𝓐)) s) hs)
                    Exists.elim (And.right a) (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ is_maximum 𝓐 (B _ i) s) =>
                          Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_maximal 𝓐 (B _ i) P) (setPO(𝓐)) s) (
                            And.intro (And.left a) (
                              Exists.intro i (
                                And.intro (And.left hi) (Iff.mpr (linmax_al_um 𝓐 (B _ i) s (h𝓐) (hset i (And.left hi))) (
                                  And.right hi
                                ))
                              )
                            )
                          )
                    )

              let ST := fun (s) =>
                  fun (hs : s ∈ S) =>
                    let a := (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_maximal 𝓐 (B _ i) P) (setPO(𝓐)) s) hs)
                    Exists.elim (And.right a) (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ is_maximal 𝓐 (B _ i) s) =>
                          Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_maximum 𝓐 (B _ i) P) (setPO(𝓐)) s) (
                            And.intro (And.left a) (
                              Exists.intro i (
                                And.intro (And.left hi) (Iff.mp (linmax_al_um 𝓐 (B _ i) s (h𝓐) (hset i (And.left hi))) (
                                  And.right hi
                                ))
                              )
                            )
                          )
                    )

              let TSeq := sub_sub_then_eq T S (TS) (ST)




              let u₁ := specification_set_subset (fun (P) => ∃ i ∈ I; is_maximum 𝓐 (B _ i) P) (setPO(𝓐))

              let u₂ := linmax_al_um 𝓐 (⋃[i in I] B at i) x (h𝓐) (u₀)
              let u₃ := linmax_al_um 𝓐 ({y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximum 𝓐 (B _ i) y}) x (h𝓐) (u₁)


              Iff.intro (
                fun (halx : (is_maximal 𝓐 (⋃[i in I] B at i) x) ) =>
                  let humx := Iff.mp (u₂) halx
                  let prop := Iff.mp (partmax_um_un_prop 𝓐 B I x (And.left h𝓐) hBI hmin hset) humx

                  let res := Iff.mpr u₃ (prop)

                  eq_subst (fun (t) => is_maximal 𝓐 t x) T S (TSeq) (res)

              ) (
                fun (halx : is_maximal 𝓐 S x) =>
                  let u₄ := eq_subst (fun (t) => is_maximal 𝓐 t x) S T (Eq.symm TSeq) (halx)
                  let u₅ := Iff.mp (u₃) u₄
                  let u₆ := Iff.mpr (partmax_um_un_prop 𝓐 B I x (And.left h𝓐) hBI hmin hset) u₅
                  Iff.mpr (u₂) u₆
              )



theorem linsup_al : ∀ 𝓐 B x, (LinOrd 𝓐) → ((is_supremum 𝓐 B x) ↔ (is_minimal 𝓐 (𝓐 ▴ B) x)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
        let u₀ := specification_set_subset (fun (P) => is_upper_bound 𝓐 B P) (setPO(𝓐))
        let u := linmin_al_um 𝓐 (𝓐 ▴ B) x h𝓐 u₀
        Iff.intro (Iff.mpr u) (Iff.mp u)

theorem lininf_al : ∀ 𝓐 B x, (LinOrd 𝓐) → ((is_infimum 𝓐 B x) ↔ (is_maximal 𝓐 (𝓐 ▾ B) x)) :=
  fun (𝓐 B x) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      let u₀ := specification_set_subset (fun (P) => is_lower_bound 𝓐 B P) (setPO(𝓐))
      let u := linmax_al_um 𝓐 (𝓐 ▾ B) x h𝓐 u₀
      Iff.intro (Iff.mpr u) (Iff.mp u)


theorem lin_supr_subset : ∀ 𝓐 B C, (LinOrd 𝓐) →
 (B ⊆ C) → (𝓐 SuprExi C) → (𝓐 SuprExi B) → (((𝓐 Supr B) . (≼(𝓐)) . (𝓐 Supr C))) :=
  fun (𝓐 B C) =>
    fun (h𝓐 : (LinOrd 𝓐) ) =>
      fun (hBC : (B ⊆ C)) =>
        fun (hC : (𝓐 SuprExi C)) =>
          fun (hB : (𝓐 SuprExi B)) =>
            let u := supr_subset 𝓐 B C (And.left h𝓐) hBC hC hB
            let suprB := And.left (supr_po_prop 𝓐 B (And.left h𝓐) (hB))
            let suprBupp := And.left (Iff.mp (upp_bou_set_is_upp_bou 𝓐 B (𝓐 Supr B)) suprB)
            let suprC := And.left (supr_po_prop 𝓐 C (And.left h𝓐) (hC))
            let suprCupp := And.left (Iff.mp (upp_bou_set_is_upp_bou 𝓐 C (𝓐 Supr C)) suprC)
            lin_ord_nR₁ 𝓐 (h𝓐) (𝓐 Supr C) (suprCupp) (𝓐 Supr B) (suprBupp) u


theorem lin_infm_subset : ∀ 𝓐 B C, (LinOrd 𝓐) →
 (B ⊆ C) → (𝓐 InfmExi C) → (𝓐 InfmExi B) → (((𝓐 Infm C) . (≼(𝓐)) . (𝓐 Infm B))) :=
  fun (𝓐 B C) =>
    fun (h𝓐 : (LinOrd 𝓐) ) =>
      fun (hBC : (B ⊆ C)) =>
        fun (hC : (𝓐 InfmExi C)) =>
          fun (hB : (𝓐 InfmExi B)) =>
            let u := infm_subset 𝓐 B C (And.left h𝓐) hBC hC hB
            let suprB := And.left (inf_po_prop 𝓐 B (And.left h𝓐) (hB))
            let suprBupp := And.left (Iff.mp (low_bou_set_is_low_bou 𝓐 B (𝓐 Infm B)) suprB)
            let suprC := And.left (inf_po_prop 𝓐 C (And.left h𝓐) (hC))
            let suprCupp := And.left (Iff.mp (low_bou_set_is_low_bou 𝓐 C (𝓐 Infm C)) suprC)
            lin_ord_nR₁ 𝓐 (h𝓐) (𝓐 Infm B) (suprBupp) (𝓐 Infm C) (suprCupp) u



theorem linsup_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 SuprExi (B _ i)))
 → ((is_supremum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_supremum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_supremum 𝓐 (B _ i) y} x)) :=
    fun (𝓐 B I x) =>
      fun (h𝓐 : (LinOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hsupr : (∀ i ∈ I; (𝓐 SuprExi (B _ i)))) =>
              let A := setPO(𝓐)
              let P := fun (t) => ∃ i ∈ I; is_supremum 𝓐 (B _ i) t
              let U := ⋃[i in I] B at i
              let T := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_supremum 𝓐 (B _ i) y}
              Iff.intro
              (
                fun (hsupx : (is_supremum 𝓐 U x)) =>
                  let u := And.left hsupx
                  let v := And.left (Iff.mp (upp_bou_set_is_upp_bou 𝓐 U x) u)
                  And.intro (
                    Iff.mpr (upp_bou_set_is_upp_bou 𝓐 T x) (
                      And.intro (v) (
                        fun (y) =>
                          fun (hy : y ∈ T) =>
                            let s := And.right (Iff.mp (spec_is_spec P A y) hy)
                            Exists.elim s (
                              fun (i) =>
                                fun (hi : i ∈ I ∧ (is_supremum 𝓐 (B _ i) y)) =>
                                  let u₁ := lin_supr_subset 𝓐 (B _ i) (U) (h𝓐) (
                                    indexed_sub_indexed_union B I (hBI) i (And.left hi)
                                  ) (Exists.intro x hsupx) (Exists.intro y (And.right hi))
                                  let v₁ := Iff.mp (supr_po_crit 𝓐 U x (And.left h𝓐) (Exists.intro x hsupx)) hsupx
                                  let v₂ := Iff.mp (supr_po_crit 𝓐 (B _ i) y (And.left h𝓐) (Exists.intro y (And.right hi))) (And.right hi)
                                  let v₃ := eq_subst (fun (t) => (t, 𝓐 Supr U) ∈ (≼(𝓐))) (𝓐 Supr (B _ i)) y (Eq.symm v₂) u₁
                                  eq_subst (fun (t) => (y, t) ∈ (≼(𝓐))) (𝓐 Supr U) x (Eq.symm v₁) v₃
                            )
                      )
                    )
                  ) (
                    fun (y) =>
                      fun (hy : y ∈ (𝓐 ▴ T)) =>
                        let u := Iff.mp (upp_bou_set_is_upp_bou 𝓐 T y) hy
                        let v := And.left u
                        (And.right hsupx) y (
                          Iff.mpr (upp_bou_set_is_upp_bou 𝓐 U y) (
                            And.intro (v) (
                              fun (s) =>
                                fun (hs : s ∈ U) =>
                                  let m := Iff.mp (indexed_union_is_union B I (hBI) s) hs
                                  Exists.elim m (
                                    fun (i) =>
                                      fun (hi : i ∈ I ∧ s ∈ (B _ i)) =>
                                        let u₂ := hsupr i (And.left hi)
                                        Exists.elim u₂ (
                                          fun (sup) =>
                                            fun (hsup : is_supremum 𝓐 (B _ i) sup) =>
                                              let u₃ := And.left hsup
                                              let u₄ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 (B _ i) sup) u₃
                                              let u₅ := And.right u₄ s (And.right hi)
                                              let a := And.left u₄
                                              let u₆ := Iff.mpr (spec_is_spec P A sup) (And.intro
                                              (a) (Exists.intro i (And.intro (And.left hi) (hsup)))
                                              )
                                              let u₇ := And.right u sup u₆
                                              trans_R₂ 𝓐 (And.left h𝓐) s sup y u₅ u₇
                                        )
                                  )
                            )
                          )
                        )
                  )
              )
              (
                fun (hx : is_supremum 𝓐 T x) =>
                  let u := And.left hx
                  let v := Iff.mp (upp_bou_set_is_upp_bou 𝓐 T x) u
                  let v₁ := And.left v
                  And.intro (
                    Iff.mpr (upp_bou_set_is_upp_bou 𝓐 U x) (
                      And.intro (v₁) (
                        fun (y) =>
                          fun (hy : y ∈ U) =>
                            let u₁ := Iff.mp (indexed_union_is_union B I (hBI) y) hy
                            Exists.elim u₁ (
                              fun (i) =>
                                fun (hi : i ∈ I ∧ y ∈ (B _ i)) =>
                                  let u₂ := hsupr i (And.left hi)
                                  Exists.elim u₂ (
                                    fun (sup) =>
                                      fun (hsup : is_supremum 𝓐 (B _ i) sup) =>
                                        let u₃ := And.left hsup
                                        let u₄ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 (B _ i) sup) u₃
                                        let u₅ := And.right u₄ y (And.right hi)
                                        let u₆ := Iff.mpr (spec_is_spec P A sup) (
                                          And.intro (And.left u₄) (Exists.intro i (
                                            And.intro (And.left hi) (hsup)
                                          ))
                                        )
                                        let u₇ := And.left hx
                                        let u₈ := Iff.mp (upp_bou_set_is_upp_bou 𝓐 T x) u₇
                                        let u₉ := And.right u₈ sup u₆
                                        trans_R₂ (𝓐) (And.left h𝓐) y sup x u₅ u₉
                                  )
                            )
                      )
                    )
                  ) (
                    fun (y) =>
                      fun (hy : y ∈ (𝓐 ▴ U)) =>
                        let v := Iff.mp (upp_bou_set_is_upp_bou 𝓐 U y) hy
                        let v₁ := And.left v
                        let u := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 T y) (
                          And.intro (v₁) (
                            fun (x) =>
                              fun (hx : x ∈ T) =>
                                let v₂ := Iff.mp (spec_is_spec P A x) hx
                                let v₃ := And.right v₂
                                Exists.elim v₃ (
                                  fun (i) =>
                                    fun (hi : i ∈ I ∧ is_supremum 𝓐 (B _ i) x) =>
                                      let v₄ := Iff.mpr (upp_bou_set_is_upp_bou 𝓐 (B _ i) y) (
                                        And.intro (v₁) (
                                          fun (m) =>
                                            fun (hm : m ∈ (B _ i)) =>
                                              let v₅ := indexed_sub_indexed_union B I (hBI) i (And.left hi) m hm
                                              And.right v m v₅
                                        )
                                      )
                                      And.right (And.right hi) y v₄
                                )

                          )
                        )
                        And.right hx y u
                  )
              )




theorem lininf_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 InfmExi (B _ i)))
→ ((is_infimum 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_infimum 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_infimum 𝓐 (B _ i) y} x)) :=
  fun (𝓐 B I x) =>
      fun (h𝓐 : (LinOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hsupr : (∀ i ∈ I; (𝓐 InfmExi (B _ i)))) =>
              let A := setPO(𝓐)
              let P := fun (t) => ∃ i ∈ I; is_infimum 𝓐 (B _ i) t
              let U := ⋃[i in I] B at i
              let T := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_infimum 𝓐 (B _ i) y}
              Iff.intro
              (
                fun (hsupx : (is_infimum 𝓐 U x)) =>
                  let u := And.left hsupx
                  let v := And.left (Iff.mp (low_bou_set_is_low_bou 𝓐 U x) u)
                  And.intro (
                    Iff.mpr (low_bou_set_is_low_bou 𝓐 T x) (
                      And.intro (v) (
                        fun (y) =>
                          fun (hy : y ∈ T) =>
                            let s := And.right (Iff.mp (spec_is_spec P A y) hy)
                            Exists.elim s (
                              fun (i) =>
                                fun (hi : i ∈ I ∧ (is_infimum 𝓐 (B _ i) y)) =>
                                  let u₁ := lin_infm_subset 𝓐 (B _ i) (U) (h𝓐) (
                                    indexed_sub_indexed_union B I (hBI) i (And.left hi)
                                  ) (Exists.intro x hsupx) (Exists.intro y (And.right hi))
                                  let v₁ := Iff.mp (infm_po_crit 𝓐 U x (And.left h𝓐) (Exists.intro x hsupx)) hsupx
                                  let v₂ := Iff.mp (infm_po_crit 𝓐 (B _ i) y (And.left h𝓐) (Exists.intro y (And.right hi))) (And.right hi)
                                  let v₃ := eq_subst (fun (t) => (𝓐 Infm U, t) ∈ (≼(𝓐))) (𝓐 Infm (B _ i)) y (Eq.symm v₂) u₁
                                  eq_subst (fun (t) => (t, y) ∈ (≼(𝓐))) (𝓐 Infm U) x (Eq.symm v₁) v₃
                            )
                      )
                    )
                  ) (
                    fun (y) =>
                      fun (hy : y ∈ (𝓐 ▾ T)) =>
                        let u := Iff.mp (low_bou_set_is_low_bou 𝓐 T y) hy
                        let v := And.left u
                        (And.right hsupx) y (
                          Iff.mpr (low_bou_set_is_low_bou 𝓐 U y) (
                            And.intro (v) (
                              fun (s) =>
                                fun (hs : s ∈ U) =>
                                  let m := Iff.mp (indexed_union_is_union B I (hBI) s) hs
                                  Exists.elim m (
                                    fun (i) =>
                                      fun (hi : i ∈ I ∧ s ∈ (B _ i)) =>
                                        let u₂ := hsupr i (And.left hi)
                                        Exists.elim u₂ (
                                          fun (sup) =>
                                            fun (hsup : is_infimum 𝓐 (B _ i) sup) =>
                                              let u₃ := And.left hsup
                                              let u₄ := Iff.mp (low_bou_set_is_low_bou 𝓐 (B _ i) sup) u₃
                                              let u₅ := And.right u₄ s (And.right hi)
                                              let a := And.left u₄
                                              let u₆ := Iff.mpr (spec_is_spec P A sup) (And.intro
                                              (a) (Exists.intro i (And.intro (And.left hi) (hsup)))
                                              )
                                              let u₇ := And.right u sup u₆
                                              trans_R₂ 𝓐 (And.left h𝓐) y sup s u₇ u₅
                                        )
                                  )
                            )
                          )
                        )
                  )
              )
              (
                fun (hx : is_infimum 𝓐 T x) =>
                  let u := And.left hx
                  let v := Iff.mp (low_bou_set_is_low_bou 𝓐 T x) u
                  let v₁ := And.left v
                  And.intro (
                    Iff.mpr (low_bou_set_is_low_bou 𝓐 U x) (
                      And.intro (v₁) (
                        fun (y) =>
                          fun (hy : y ∈ U) =>
                            let u₁ := Iff.mp (indexed_union_is_union B I (hBI) y) hy
                            Exists.elim u₁ (
                              fun (i) =>
                                fun (hi : i ∈ I ∧ y ∈ (B _ i)) =>
                                  let u₂ := hsupr i (And.left hi)
                                  Exists.elim u₂ (
                                    fun (sup) =>
                                      fun (hsup : is_infimum 𝓐 (B _ i) sup) =>
                                        let u₃ := And.left hsup
                                        let u₄ := Iff.mp (low_bou_set_is_low_bou 𝓐 (B _ i) sup) u₃
                                        let u₅ := And.right u₄ y (And.right hi)
                                        let u₆ := Iff.mpr (spec_is_spec P A sup) (
                                          And.intro (And.left u₄) (Exists.intro i (
                                            And.intro (And.left hi) (hsup)
                                          ))
                                        )
                                        let u₇ := And.left hx
                                        let u₈ := Iff.mp (low_bou_set_is_low_bou 𝓐 T x) u₇
                                        let u₉ := And.right u₈ sup u₆
                                        trans_R₂ (𝓐) (And.left h𝓐) x sup y u₉ u₅
                                  )
                            )
                      )
                    )
                  ) (
                    fun (y) =>
                      fun (hy : y ∈ (𝓐 ▾ U)) =>
                        let v := Iff.mp (low_bou_set_is_low_bou 𝓐 U y) hy
                        let v₁ := And.left v
                        let u := Iff.mpr (low_bou_set_is_low_bou 𝓐 T y) (
                          And.intro (v₁) (
                            fun (x) =>
                              fun (hx : x ∈ T) =>
                                let v₂ := Iff.mp (spec_is_spec P A x) hx
                                let v₃ := And.right v₂
                                Exists.elim v₃ (
                                  fun (i) =>
                                    fun (hi : i ∈ I ∧ is_infimum 𝓐 (B _ i) x) =>
                                      let v₄ := Iff.mpr (low_bou_set_is_low_bou 𝓐 (B _ i) y) (
                                        And.intro (v₁) (
                                          fun (m) =>
                                            fun (hm : m ∈ (B _ i)) =>
                                              let v₅ := indexed_sub_indexed_union B I (hBI) i (And.left hi) m hm
                                              And.right v m v₅
                                        )
                                      )
                                      And.right (And.right hi) y v₄
                                )

                          )
                        )
                        And.right hx y u
                  )
              )


theorem lin_latt_lemma₁ : ∀ 𝓐, ∀ x y ∈ setPO(𝓐); (LinOrd 𝓐) → (x . (≼(𝓐)) . y) → (is_supremum 𝓐 {x, y} y) :=
  fun (𝓐) =>
    fun (x) =>
      fun (hx) =>
        fun (y) =>
          fun (hy) =>
            fun (h𝓐) =>
              fun (hxy) =>
                let u₀ := fun (s) =>
                        fun (hs : s ∈ {x , y}) =>
                    Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair x y s) hs)
                    (
                      fun (hx₁ : s = x) =>
                        eq_subst (fun (t) => t ∈ setPO(𝓐)) x s (Eq.symm hx₁) (hx)
                    )
                    (
                      fun (hy₁ : s = y) =>
                        eq_subst (fun (t) => t ∈ setPO(𝓐)) y s (Eq.symm hy₁) (hy)
                    )
                let u₁ := And.intro (right_unordered_pair x y) (
                  fun (s) =>
                    fun (hs : s ∈ {x, y}) =>
                      let u := Iff.mp (unordered_pair_set_is_unordered_pair x y s) hs
                      Or.elim u
                      (
                        fun (hx₁ : s = x) =>
                          eq_subst (fun (t) => (t, y) ∈ (≼(𝓐))) x s (Eq.symm hx₁) (hxy)
                      )
                      (
                        fun (hy₁ : s = y) =>
                          eq_subst (fun (t) => (t, y) ∈ (≼(𝓐))) y s (Eq.symm hy₁) (refl_R₂ 𝓐 (And.left h𝓐) y hy)
                      )
                )
                max_um_is_sup 𝓐 {x, y} y (u₀) (u₁)



theorem lin_latt_lemma₂ : ∀ 𝓐, ∀ x y ∈ setPO(𝓐); (LinOrd 𝓐) → (x . (≼(𝓐)) . y) → (is_infimum 𝓐 {x, y} x) :=
  fun (𝓐) =>
    fun (x) =>
      fun (hx) =>
        fun (y) =>
          fun (hy) =>
            fun (h𝓐) =>
              fun (hxy) =>
                let u₀ := fun (s) =>
                        fun (hs : s ∈ {x , y}) =>
                    Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair x y s) hs)
                    (
                      fun (hx₁ : s = x) =>
                        eq_subst (fun (t) => t ∈ setPO(𝓐)) x s (Eq.symm hx₁) (hx)
                    )
                    (
                      fun (hy₁ : s = y) =>
                        eq_subst (fun (t) => t ∈ setPO(𝓐)) y s (Eq.symm hy₁) (hy)
                    )

                let u₁ := And.intro (left_unordered_pair x y) (
                  fun (s) =>
                    fun (hs : s ∈ {x, y}) =>

                      let u := Iff.mp (unordered_pair_set_is_unordered_pair x y s) hs
                      Or.elim u
                      (
                        fun (hx₁ : s = x) =>
                          eq_subst (fun (t) => (x, t) ∈ (≼(𝓐))) x s (Eq.symm hx₁) (refl_R₂ 𝓐 (And.left h𝓐) x hx)
                      )
                      (
                        fun (hy₁ : s = y) =>
                          eq_subst (fun (t) => (x, t) ∈ (≼(𝓐))) y s (Eq.symm hy₁) (hxy)
                      )
                )
                min_um_is_inf 𝓐 {x, y} x (u₀) (u₁)



theorem lin_latt : ∀ 𝓐, (LinOrd 𝓐) → (Latt 𝓐) :=
  fun (𝓐) =>
    fun (h𝓐 : (LinOrd 𝓐)) =>
      And.intro (And.left h𝓐) (
        fun (x) =>
          fun (hx : (x ∈ setPO(𝓐))) =>
            fun (y) =>
              fun (hy : (y ∈ setPO(𝓐))) =>
                let u := lin_ord_prop 𝓐 (h𝓐) x hx y hy
                Or.elim u
                (
                  fun (hxy : (x . (≼(𝓐)) . y)) =>
                    And.intro (Exists.intro y (lin_latt_lemma₁ 𝓐 x hx y hy h𝓐 hxy)) (
                      Exists.intro x (lin_latt_lemma₂ 𝓐 x hx y hy h𝓐 hxy)
                    )
                )
                (
                  fun (hyx : (y . (≼(𝓐)) . x)) =>
                    let u₁ := lin_latt_lemma₁ 𝓐 y hy x hx h𝓐 hyx
                    let u₂ := lin_latt_lemma₂ 𝓐 y hy x hx h𝓐 hyx
                    let u₃ := extensionality {x, y} {y, x} (
                      fun (t) =>
                        Iff.intro
                        (
                          fun (ht : t ∈ {x, y}) =>
                              Iff.mpr (unordered_pair_set_is_unordered_pair y x t) (
                                Iff.mp (disj_comm (t = x) (t = y)) (
                                  Iff.mp (unordered_pair_set_is_unordered_pair x y t) ht
                                )
                              )
                        )
                        (
                          fun (ht : t ∈ {y, x}) =>
                              Iff.mpr (unordered_pair_set_is_unordered_pair x y t) (
                                Iff.mp (disj_comm (t = y) (t = x)) (
                                  Iff.mp (unordered_pair_set_is_unordered_pair y x t) ht
                                )
                              )
                        )
                    )
                    let u₄ := eq_subst (fun (t) => is_supremum 𝓐 t x) {y, x} {x, y} (Eq.symm u₃) u₁
                    let u₅ := eq_subst (fun (t) => is_infimum 𝓐 t y) {y, x} {x, y} (Eq.symm u₃) u₂
                    And.intro (Exists.intro x (u₄)) (
                      Exists.intro y (u₅)
                    )
                )
      )


def is_well_order 𝓐 := (LinOrd 𝓐) ∧ ∀ X, (X ⊆ setPO(𝓐)) → (X ≠ ∅) → (𝓐 MinExi X)
syntax "WellOrd" term : term
macro_rules
| `(WellOrd $𝓐) => `(is_well_order $𝓐)


def is_chain (𝓐 B) := (PartOrd 𝓐) ∧ (B ⊆ setPO(𝓐)) ∧ (LinOrd (𝓐 SubsPO B))
syntax term "Chain" term : term
macro_rules
| `($𝓐 Chain $B) => `(is_chain $𝓐 $B)

def anti_chain (𝓐 B) := (PartOrd 𝓐) ∧ (B ⊆ setPO(𝓐)) ∧ (∀ x y ∈ B; noncomparable_str 𝓐 x y)
syntax term "AntiChain" term : term
macro_rules
| `($𝓐 AntiChain $B) => `(anti_chain $𝓐 $B)

theorem lin_chain : ∀ 𝓐 B, (B ≠ ∅) → (B ⊆ setPO(𝓐)) →  (LinOrd 𝓐) → (𝓐 Chain B) :=
  fun (𝓐 B) =>
    fun (hemp : (B ≠ ∅)) =>
      fun (hB : (B ⊆ setPO(𝓐))) =>
        fun (h𝓐 : (LinOrd 𝓐)) =>
          let u := sub_is_LO 𝓐 B (hemp) (h𝓐) (hB)
          And.intro (And.left h𝓐) (And.intro (hB) (u))


theorem antichain : ∀ 𝓐 𝓑 A B, (𝓐 AntiChain A) → (𝓑 AntiChain B) → ((𝓐 CartPO 𝓑) AntiChain (A × B)) :=
  fun (𝓐 𝓑 A B) =>
    fun (h𝓐 : (𝓐 AntiChain A)) =>
      fun (h𝓑 : (𝓑 AntiChain B)) =>
        let L₀ := (≼(𝓐 CartPO 𝓑))
        let L₂ := (le_cart 𝓐 𝓑)
        let L₃ := (leq_cart 𝓐 𝓑)
        let S := setPO(𝓐) × setPO(𝓑)
        let cart_po_po := cart_PO_PO 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑)
        let ABsub₀ := cartesian_product_subset A B (setPO(𝓐)) (setPO(𝓑)) (And.left (And.right h𝓐)) (And.left (And.right h𝓑))
        let ABsub := eq_subst (fun (t) => (A × B) ⊆ t) (setPO(𝓐) × setPO(𝓑)) (setPO(𝓐 CartPO 𝓑)) (Eq.symm (setPO_is_setPO (setPO(𝓐) × setPO(𝓑))
            (le_cart 𝓐 𝓑) (leq_cart 𝓐 𝓑))) (
              ABsub₀
            )
        And.intro (cart_PO_PO 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑)) (
          And.intro (ABsub
          ) (

            fun (x) =>
              fun (hx : x ∈ A × B) =>
                fun (y) =>
                  fun (hy : y ∈ A × B) =>
                    let hxcart := ABsub x hx
                    let hycart := ABsub y hy
                    let hx𝓐₁ := And.left (And.right h𝓐) (π₁ x) (fst_coor_set A B x hx)
                    let hx𝓑₂ := And.left (And.right h𝓑) (π₂ x) (snd_coor_set A B x hx)
                    let hy𝓐₁ := And.left (And.right h𝓐) (π₁ y) (fst_coor_set A B y hy)
                    let hy𝓑₂ := And.left (And.right h𝓑) (π₂ y) (snd_coor_set A B y hy)

                    And.intro (

                      fun (hxy : (x, y) ∈ ≺(𝓐 CartPO 𝓑)) =>
                        let u₁ := Iff.mp (And.left (part_ord_pair_prop (𝓐 CartPO 𝓑) cart_po_po x hxcart y hycart)) hxy
                        let u₂ := eq_subst (fun (t) => (x, y) ∈ t) L₀ L₃ (lesseqPO_is_lesseqPO S L₂ L₃) (And.left u₁)
                        let u₃ := Iff.mp (leq_cart_prop 𝓐 𝓑 x (ABsub₀ x hx) y (ABsub₀ y hy)) u₂
                        let u₄ := And.right u₁
                        let u₅ := fst_snd_then_unique A B x hx
                        let u₆ := fst_snd_then_unique A B y hy
                        let u₇ := fun (hxyeq : (π₁ x) = (π₁ y) ∧ (π₂ x) = (π₂ y)) =>
                          let u₈ := Iff.mpr (ordered_pair_set_prop (π₁ x) (π₂ x) (π₁ y) (π₂ y)) hxyeq
                          let u₉ := Eq.trans (u₅) (u₈)
                          let u₁₀ := Eq.trans u₉ (Eq.symm u₆)
                          u₄ u₁₀
                        let u₈ : ((π₁ x) ≠ (π₁ y)) ∨ ((π₂ x) ≠ (π₂ y)) := Iff.mp (morgan_comm ((π₁ x) = (π₁ y)) ((π₂ x) = (π₂ y))) u₇
                        Or.elim u₈
                        (
                          fun (hπ₁ : (π₁ x) ≠ (π₁ y)) =>
                            let u₉ := Iff.mpr (And.left (part_ord_pair_prop 𝓐 (And.left h𝓐) (π₁ x) (hx𝓐₁) (π₁ y) (hy𝓐₁))) (
                              And.intro (And.left u₃) (hπ₁)
                            )
                            And.left (And.right (And.right h𝓐) (π₁ x) (fst_coor_set A B x hx) (π₁ y) (fst_coor_set A B y hy)) u₉
                        )
                        (
                          fun (hπ₂ : (π₂ x) ≠ (π₂ y)) =>
                            let u₉ := Iff.mpr (And.left (part_ord_pair_prop 𝓑 (And.left h𝓑) (π₂ x) (hx𝓑₂) (π₂ y) (hy𝓑₂))) (
                              And.intro (And.right u₃) (hπ₂)
                            )
                            And.left (And.right (And.right h𝓑) (π₂ x) (snd_coor_set A B x hx) (π₂ y) (snd_coor_set A B y hy)) u₉
                        )



                    ) (
                      fun (hyx : (x, y) ∈ ≻(𝓐 CartPO 𝓑)) =>
                        let hxy : (y, x) ∈ ≺(𝓐 CartPO 𝓑) := Iff.mpr (po_less_more (𝓐 CartPO 𝓑) (cart_po_po) y x) (hyx)
                        let u₁ := Iff.mp (And.left (part_ord_pair_prop (𝓐 CartPO 𝓑) cart_po_po y hycart x hxcart)) hxy
                        let u₂ := eq_subst (fun (t) => (y, x) ∈ t) L₀ L₃ (lesseqPO_is_lesseqPO S L₂ L₃) (And.left u₁)
                        let u₃ := Iff.mp (leq_cart_prop 𝓐 𝓑 y (ABsub₀ y hy) x (ABsub₀ x hx)) u₂
                        let u₄ := And.right u₁
                        let u₅ := fst_snd_then_unique A B x hx
                        let u₆ := fst_snd_then_unique A B y hy
                        let u₇ := fun (hxyeq : (π₁ y) = (π₁ x) ∧ (π₂ y) = (π₂ x)) =>
                          let u₈ := Iff.mpr (ordered_pair_set_prop (π₁ y) (π₂ y) (π₁ x) (π₂ x)) hxyeq
                          let u₉ := Eq.trans (u₆) (u₈)
                          let u₁₀ := Eq.trans u₉ (Eq.symm u₅)
                          u₄ u₁₀
                        let u₈ : ((π₁ y) ≠ (π₁ x)) ∨ ((π₂ y) ≠ (π₂ x)) := Iff.mp (morgan_comm ((π₁ y) = (π₁ x)) ((π₂ y) = (π₂ x))) u₇
                        Or.elim u₈
                        (
                          fun (hπ₁ : (π₁ y) ≠ (π₁ x)) =>
                            let u₉ := Iff.mpr (And.left (part_ord_pair_prop 𝓐 (And.left h𝓐) (π₁ y) (hy𝓐₁) (π₁ x) (hx𝓐₁))) (
                              And.intro (And.left u₃) (hπ₁)
                            )
                            And.left (And.right (And.right h𝓐) (π₁ y) (fst_coor_set A B y hy) (π₁ x) (fst_coor_set A B x hx)) u₉
                        )
                        (
                          fun (hπ₂ : (π₂ y) ≠ (π₂ x)) =>
                            let u₉ := Iff.mpr (And.left (part_ord_pair_prop 𝓑 (And.left h𝓑) (π₂ y) (hy𝓑₂) (π₂ x) (hx𝓑₂))) (
                              And.intro (And.right u₃) (hπ₂)
                            )
                            And.left (And.right (And.right h𝓑) (π₂ y) (snd_coor_set A B y hy) (π₂ x) (snd_coor_set A B x hx)) u₉
                        )
                    )
          )
        )


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


theorem iso_equin : ∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (setPO(𝓐) ~ setPO(𝓑)) :=
  fun (𝓐 𝓑) =>
    fun (h𝓐𝓑 : (𝓐 ≃O 𝓑)) =>
      Exists.elim h𝓐𝓑 (
        fun (f) =>
          fun (hf) =>
            Exists.intro f (And.left hf)
      )


theorem iso_eq : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → ∀ x y ∈ setPO(𝓐); (x = y) ↔ ((f⦅x⦆) = (f⦅y⦆)) :=
  fun (𝓐 𝓑 f) =>
    fun (hf) =>
      fun (x) =>
        fun (hx) =>
          fun (y) =>
            fun (hy) =>
              Iff.intro
              (
                fun (hxy : (x = y)) =>
                  eq_subst (fun (t) => (f⦅t⦆) = (f⦅y⦆)) y x (Eq.symm hxy) (Eq.refl (f⦅y⦆))
              )
              (
                fun (hfxy : (f⦅x⦆) = (f⦅y⦆)) =>
                  let u := And.left (And.left hf)
                  let v := And.left (And.right (And.left hf))
                  let s := And.intro u v

                  Iff.mp (func_inj_prop setPO(𝓐) setPO(𝓑) f (u)) s x hx y hy hfxy
              )


theorem iso_in₀ : ∀ 𝓐 𝓑 f x, (f PO_ISO 𝓐 To 𝓑) → (x ∈ setPO(𝓐)) → ((f⦅x⦆)) ∈ setPO(𝓑) :=
  fun (𝓐 𝓑 f x) =>
    fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        val_in_B f (setPO(𝓐)) (setPO(𝓑)) (And.left (And.left hf)) x hx


theorem iso_in₁ : ∀ 𝓐 𝓑 f x, (f PO_ISO 𝓐 To 𝓑) → (x ∈ setPO(𝓐)) → ((x ∈ setPO(𝓐)) ↔ ((f⦅x⦆)) ∈ setPO(𝓑)) :=
  fun (𝓐 𝓑 f x) =>
    fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        let u := val_in_B f (setPO(𝓐)) (setPO(𝓑)) (And.left (And.left hf)) x hx
        Iff.intro
        (fun (_) => u)
        (fun (_) => hx)


theorem iso_in₂ : ∀ 𝓐 𝓑 T f x, (x ∈ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → ((x ∈ T) ↔ (f⦅x⦆) ∈ f.[T]) :=
  fun (𝓐 𝓑 T f x) =>
    fun (hx : (x ∈ setPO(𝓐))) =>
      fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
        Iff.intro
        (
            fun (hxT : x ∈ T) =>
              Iff.mpr (image_prop f T (f⦅x⦆)) (
                Exists.intro x (
                  And.intro hxT (
                    Iff.mpr (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) (And.left (And.left hf)) x (f⦅x⦆) hx) (
                      Eq.refl ((f⦅x⦆))
                    )

                  )
                )
              )
        )
        (
          fun (hfxT : (f⦅x⦆) ∈ f.[T]) =>
            let u := Iff.mp (image_prop f T (f⦅x⦆)) hfxT
            Exists.elim u (
              fun (y) =>
                fun (hy) =>
                  let u₀ := And.left (And.left (And.left (And.left hf))) (y, (f⦅x⦆)) (And.right hy)
                  let u₁ := And.left (Iff.mp (cartesian_product_pair_prop (setPO(𝓐)) setPO(𝓑) y (f⦅x⦆)) u₀)
                  eq_subst (fun (t) => t ∈ T) y x (Eq.symm (
                    Iff.mpr (iso_eq 𝓐 𝓑 f hf x hx y (u₁)) (
                      Iff.mp (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) (And.left (And.left hf)) y (f⦅x⦆) u₁) (And.right hy)

                    )

                  )) (And.left hy)
            )
        )





theorem iso_R₂ : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → ∀ x y ∈ setPO(𝓐); (x . ≼(𝓐) . y) ↔ ((f⦅x⦆) . (≼(𝓑)) . (f⦅y⦆)) :=
  fun (_) =>
    fun (_) =>
      fun (_) =>
        fun (hf) =>
          And.right hf





theorem iso_refl : ∀ 𝓐, (𝓐 ≃O 𝓐) :=
  fun (𝓐) =>
    Exists.intro (id_ setPO(𝓐)) (
      And.intro (id_is_bij (setPO(𝓐))) (
        fun (x) =>
          fun (hx : x ∈ setPO(𝓐)) =>
            fun (y) =>
              fun (hy : y ∈ setPO(𝓐)) =>
                let f := id_ setPO(𝓐)
                let u := id_val_prop (setPO(𝓐)) x hx
                let v := id_val_prop (setPO(𝓐)) y hy

                eq_subst (fun (t) => ((x, y) ∈ (≼(𝓐))) ↔ ((t, (f⦅y⦆)) ∈ ≼(𝓐))) x (f⦅x⦆) (Eq.symm u) (
                    eq_subst (fun (t) => ((x, y) ∈ (≼(𝓐))) ↔ ((x, t) ∈ ≼(𝓐))) y (f⦅y⦆) (Eq.symm v) (
                      Iff.intro
                      (
                        fun (hxy) => hxy
                      )
                      (
                        fun (hxy) => hxy
                      )
                    )
                  )
          )
      )




theorem iso_symm : ∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (𝓑 ≃O 𝓐) :=
  fun (𝓐 𝓑) =>
    fun (h𝓐𝓑 : (𝓐 ≃O 𝓑)) =>
      Exists.elim h𝓐𝓑 (
        fun (f) =>
          fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
            let u := bijection_inv_mp f setPO(𝓐) setPO(𝓑) (And.left hf)
            Exists.intro (f⁻¹) (
              And.intro (u) (
                fun (x) =>
                  fun (hx : x ∈ setPO(𝓑)) =>
                    fun (y) =>
                      fun (hy : y ∈ setPO(𝓑)) =>
                        let s := And.left hf
                        let t := And.left s
                        let r := And.left t
                        let k := And.left r
                        let u₁ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                        let u₂ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u) t) x hx
                        let u₃ := eq_subst (fun (t) => t⦅x⦆ = (f⦅f⁻¹⦅x⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₁) u₂
                        let u₄ := id_val_prop (setPO(𝓑)) x hx
                        let u₅ := Eq.trans (Eq.symm u₄) (u₃)

                        let u₆ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u) t) y hy
                        let u₇ := eq_subst (fun (t) => t⦅y⦆ = (f⦅f⁻¹⦅y⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₁) u₆
                        let u₈ := id_val_prop (setPO(𝓑)) y hy
                        let u₉ := Eq.trans (Eq.symm u₇) (u₈)

                        let xset := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u) x hx
                        let yset := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u) y hy

                        let res₁ := And.right hf (f⁻¹⦅x⦆) xset (f⁻¹⦅y⦆) yset
                        let res₂ := Iff.intro (Iff.mpr res₁) (Iff.mp res₁)

                        let res₃ := eq_subst (fun (t) => ((t, (f⦅f⁻¹⦅y⦆⦆)) ∈ ≼(𝓑)) ↔ (((f⁻¹⦅x⦆), (f⁻¹⦅y⦆)) ∈ ≼(𝓐))) (f⦅f⁻¹⦅x⦆⦆) x (Eq.symm u₅) (res₂)


                        eq_subst (fun (t) => (((x, t) ∈ ≼(𝓑)) ↔ (((f⁻¹⦅x⦆), (f⁻¹⦅y⦆)) ∈ ≼(𝓐)))) (f⦅f⁻¹⦅y⦆⦆) y (u₉) (res₃)
              )
            )
      )



theorem iso_trans :  ∀ 𝓐 𝓑 𝓒, (𝓐 ≃O 𝓑) → (𝓑 ≃O 𝓒) → (𝓐 ≃O 𝓒) :=
  fun (𝓐 𝓑 𝓒) =>
    let A := setPO(𝓐)
    let B := setPO(𝓑)
    let C := setPO(𝓒)
    let LA := ≼(𝓐)
    let LB := ≼(𝓑)
    let LC := ≼(𝓒)
    fun (h𝓐𝓑 : (𝓐 ≃O 𝓑)) =>
      fun (h𝓑𝓒 : (𝓑 ≃O 𝓒)) =>

        Exists.elim h𝓐𝓑 (
        fun (f) =>
          fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
              Exists.elim h𝓑𝓒 (
                fun (g) =>
                  fun (hg : (g PO_ISO 𝓑 To 𝓒)) =>

                  Exists.intro (g ∘ f) (
                    And.intro (bijection_composition f g A B C (And.left hf) (And.left hg)) (
                      fun (x) =>
                        fun (hx : x ∈ setPO(𝓐)) =>
                          fun (y) =>
                            fun (hy : y ∈ setPO(𝓐)) =>

                              let u₁ := And.right hf x hx y hy

                              iff_transitivity (x . LA . y) ((f⦅x⦆) . LB . (f⦅y⦆)) (((g ∘ f)⦅x⦆) . LC . ((g ∘ f)⦅y⦆)) u₁ (


                                let u₁ := And.right hg (f⦅x⦆) (val_in_B f A B (And.left (And.left hf)) x hx) (f⦅y⦆) (val_in_B f A B (And.left (And.left hf)) y hy)

                                let u₂ := And.right (function_composition_A f g A B C (And.left (And.left hf)) (And.left (And.left hg))) x hx
                                let u₃ := And.right (function_composition_A f g A B C (And.left (And.left hf)) (And.left (And.left hg))) y hy

                                eq_subst (fun (t) => (((f⦅x⦆), (f⦅y⦆)) ∈ LB) ↔ (t, ((g ∘ f)⦅y⦆)) ∈ LC) (g⦅f⦅x⦆⦆) ((g ∘ f)⦅x⦆) (Eq.symm u₂) (
                                  eq_subst (fun (r) => (((f⦅x⦆), (f⦅y⦆)) ∈ LB) ↔ ((((g⦅f⦅x⦆⦆), r) ∈ LC))) (g⦅f⦅y⦆⦆) ((g ∘ f)⦅y⦆) (Eq.symm u₃) (
                                    u₁
                                  )
                                )
                              )
                    )
                  )
              )
        )



theorem iso_R₁ : ∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (PartOrd 𝓐) → (PartOrd 𝓑) → (∀ x y ∈ setPO(𝓐); (x . ≺(𝓐) . y) ↔ ((f⦅x⦆) . (≺(𝓑)) . (f⦅y⦆))) :=
  fun (𝓐 𝓑 f) =>
    fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
      fun (h𝓐 : (PartOrd 𝓐)) =>
        fun (h𝓑 : (PartOrd 𝓑)) =>
          fun (x) =>
            fun (hx : x ∈ setPO(𝓐)) =>
              fun (y) =>
                fun (hy : y ∈ setPO(𝓐)) =>

                  Iff.intro
                  (
                    fun (hxy) =>
                      let u₀ := Iff.mp (And.left (part_ord_pair_prop 𝓐 h𝓐 x hx y hy)) hxy
                      let u₀₁ := Iff.mp (iso_R₂ 𝓐 𝓑 f hf x hx y hy) (And.left u₀)

                      Iff.mpr (And.left (part_ord_pair_prop 𝓑 h𝓑 (f⦅x⦆) (iso_in₀ 𝓐 𝓑 f x hf hx) (f⦅y⦆) (iso_in₀ 𝓐 𝓑 f y hf hy))) (
                        And.intro (u₀₁) (
                          fun (hfxy : (f⦅x⦆) = (f⦅y⦆)) =>
                            let u₂ := Iff.mpr (iso_eq 𝓐 𝓑 f hf x hx y hy) hfxy
                            (And.right u₀) u₂
                        )
                      )

                  )
                  (
                    fun (hfxy) =>
                      let u₀ := Iff.mp (And.left (part_ord_pair_prop 𝓑 h𝓑 (f⦅x⦆) (iso_in₀ 𝓐 𝓑 f x hf hx) (f⦅y⦆) (iso_in₀ 𝓐 𝓑 f y hf hy))) hfxy
                      let u₀₁ := Iff.mpr (iso_R₂ 𝓐 𝓑 f hf x hx y hy) (And.left u₀)
                      Iff.mpr (And.left (part_ord_pair_prop 𝓐 h𝓐 x hx y hy)) (
                        And.intro (u₀₁) (
                          fun (hxy : (x = y)) =>
                            let u₂ := Iff.mp (iso_eq 𝓐 𝓑 f hf x hx y hy) hxy
                            (And.right u₀) u₂
                        )
                      )
                  )


theorem poiso_not_equiv (φ₁ φ₂ : Set → Prop) : ∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((¬(φ₁ x)) ↔ (¬φ₂ (f⦅x⦆))) :=
  fun (_ _) =>
    fun (heqv) =>
      Iff.intro
      (
        fun (hnφ₁x) =>
          fun (hφ₂fx) =>
            hnφ₁x (Iff.mpr heqv hφ₂fx)
      )
      (
        fun (hnφ₂x) =>
          fun (hφ₁fx) =>
            hnφ₂x (Iff.mp heqv hφ₁fx)
      )


theorem poiso_and_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ∧ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ∧ (φ₄ (f⦅x⦆)))) :=
  fun (_ _) =>
    fun (heqv₁₂) =>
      fun (heqv₃₄) =>
        Iff.intro
        (
          fun (hφ₁φ₃x) =>
            And.intro (Iff.mp heqv₁₂ (And.left hφ₁φ₃x)) (Iff.mp heqv₃₄ (And.right hφ₁φ₃x))
        )
        (
          fun (hφ₂φ₄x) =>
            And.intro (Iff.mpr heqv₁₂ (And.left hφ₂φ₄x)) (Iff.mpr heqv₃₄ (And.right hφ₂φ₄x))
        )


theorem poiso_or_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ∨ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ∨ (φ₄ (f⦅x⦆)))) :=
  fun (_ _) =>
    fun (heqv₁₂) =>
      fun (heqv₃₄) =>
        Iff.intro
        (
          fun (hφ₁φ₃x) =>
            Or.elim hφ₁φ₃x
            (
              fun (hφ₁x) =>
                Or.inl ( (Iff.mp heqv₁₂) (hφ₁x))
            )
            (
              fun (hφ₃x) =>
                Or.inr ((Iff.mp heqv₃₄) (hφ₃x))
            )
        )
        (
          fun (hφ₂φ₄x) =>
            Or.elim hφ₂φ₄x
            (
              fun (hφ₂x) =>
                Or.inl ((Iff.mpr heqv₁₂) (hφ₂x))
            )
            (
              fun (hφ₄x) =>
                Or.inr ((Iff.mpr heqv₃₄) (hφ₄x))
            )
        )



theorem poiso_if_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) → ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) → (φ₄ (f⦅x⦆)))) :=
  fun (_ _) =>
    fun (heqv₁₂) =>
      fun (heqv₃₄) =>
        Iff.intro
        (
          fun (hφ₁φ₃x) =>
            fun (hφ₂fx) =>
              Iff.mp heqv₃₄ (
                hφ₁φ₃x (
                  Iff.mpr heqv₁₂ (
                    hφ₂fx
                  )
                )
              )
        )
        (
          fun (hφ₂φ₄x) =>
            fun (hφ₁x) =>
              Iff.mpr heqv₃₄ (
                hφ₂φ₄x (
                  Iff.mp heqv₁₂ (
                    hφ₁x
                  )
                )
              )
        )



theorem poiso_iff_equiv (φ₁ φ₂ φ₃ φ₄ : Set → Prop) :
∀ f x, ((φ₁ x) ↔ (φ₂ (f⦅x⦆))) → ((φ₃ x) ↔ (φ₄ (f⦅x⦆))) → (((φ₁ x) ↔ ((φ₃ x))) ↔ ((φ₂ (f⦅x⦆)) ↔ (φ₄ (f⦅x⦆)))) :=
  fun (_ _) =>
    fun (heqv₁₂) =>
      fun (heqv₃₄) =>
        Iff.intro
        (
          fun (hφ₁φ₃x) =>
            Iff.intro
            (
              fun (hφ₂fx) =>
                Iff.mp heqv₃₄ (
                  (Iff.mp hφ₁φ₃x) (
                    Iff.mpr heqv₁₂ (
                      hφ₂fx
                    )
                  )
                )
            )
            (
              fun (hφ₄fx) =>
                Iff.mp heqv₁₂ (
                  Iff.mpr hφ₁φ₃x (
                    Iff.mpr (heqv₃₄) (
                      hφ₄fx
                    )
                  )
                )
            )
        )
        (
          fun (hφ₂φ₄x) =>
            Iff.intro
            (
              fun (hφ₁x) =>
                Iff.mpr heqv₃₄ (
                  Iff.mp hφ₂φ₄x (
                    Iff.mp heqv₁₂ (
                      hφ₁x
                    )
                  )
                )
            )
            (
              fun (hφ₃x) =>
                Iff.mpr heqv₁₂ (
                  Iff.mpr hφ₂φ₄x (
                    Iff.mp heqv₃₄ (
                      hφ₃x
                    )
                  )
                )
            )
        )


theorem poiso_all_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ X; ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∀ x ∈ X; (φ₁ x)) ↔ (∀ x ∈ f.[X]; (φ₂ x))) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX) =>
      fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
        let u₁ := bijection_inv_mp f setPO(𝓐) setPO(𝓑) (And.left hf)

        let s := And.left hf
        let t := And.left s
        let r := And.left t
        let k := And.left r



        fun (hφ₁φ₂x : (∀ x ∈ X; ((φ₁ x) ↔ (φ₂ (f⦅x⦆))))) =>
          Iff.intro
          (
            fun (hφ₁x) =>
              fun (x) =>
                fun (hx : x ∈ f.[X]) =>

                  let v₁ := specification_set_subset (fun (t) => ∃ y ∈ X; (y . f . t)) (rng f) x hx
                  let v₂ := rng_partial_function f (setPO(𝓐)) (setPO(𝓑)) r x v₁
                  let v₀ := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) x v₂


                  let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                  let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) x (v₂)
                  let u₄ := eq_subst (fun (t) => t⦅x⦆ = (f⦅f⁻¹⦅x⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                  let u₅ := id_val_prop (setPO(𝓑)) x (v₂)
                  let u₅ := Eq.trans (Eq.symm u₅) (u₄)

                  let v₃ := Iff.mp (image_prop f X (x)) hx
                  Exists.elim v₃ (
                    fun (i) =>
                      fun (hi) =>
                        let v₄ := And.right hi
                        let v₅ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) t (f⁻¹⦅x⦆) x v₀) u₅
                        let v₆ := And.left (And.right s) i (f⁻¹⦅x⦆) x v₄ v₅
                        let v₇ := eq_subst (fun (m) => m ∈ X) (i) (f⁻¹⦅x⦆) (v₆) (And.left hi)

                        let u := Iff.mp (hφ₁φ₂x (f⁻¹⦅x⦆) (v₇)) (
                          hφ₁x (f⁻¹⦅x⦆) (v₇)
                        )


                        eq_subst (fun (m) => φ₂ m) (f⦅f⁻¹⦅x⦆⦆) x (Eq.symm u₅) (u)

                  )



          )
          (
            fun (hφ₂x) =>
              fun (x) =>
                fun (hx : x ∈ X) =>
                  Iff.mpr (hφ₁φ₂x x hx) (
                    hφ₂x (f⦅x⦆) (
                      Iff.mp (iso_in₂ 𝓐 𝓑 X f x (hX x hx) (hf)) (hx)
                    )
                  )
          )


theorem poiso_exi_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ X; ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∃ x ∈ X; (φ₁ x)) ↔ (∃ x ∈ f.[X]; (φ₂ x))) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
        let u₁ := bijection_inv_mp f setPO(𝓐) setPO(𝓑) (And.left hf)

        let s := And.left hf
        let t := And.left s
        let r := And.left t
        let k := And.left r

        fun (hφ₁φ₂x : (∀ x ∈ X; ((φ₁ x) ↔ (φ₂ (f⦅x⦆))))) =>
          Iff.intro
          (
            fun(hφ₁x) =>
              Exists.elim hφ₁x (
                fun (x) =>
                  fun (hx) =>
                    Exists.intro ((f⦅x⦆)) (
                      And.intro (Iff.mp (iso_in₂ 𝓐 𝓑 X f x (hX x (And.left hx)) hf) (And.left hx)) (
                        Iff.mp (hφ₁φ₂x x (And.left hx)) (And.right hx)
                      )
                    )
              )
          )
          (
            fun (hφ₂x) =>
              Exists.elim hφ₂x (
                fun (x) =>
                  fun (hx) =>
                    Exists.intro (f⁻¹⦅x⦆) (
                      let v₁ := specification_set_subset (fun (t) => ∃ y ∈ X; (y . f . t)) (rng f) x (And.left hx)
                      let v₂ := rng_partial_function f (setPO(𝓐)) (setPO(𝓑)) r x v₁
                      let v₀ := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) x v₂


                      let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                      let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) x (v₂)
                      let u₄ := eq_subst (fun (t) => t⦅x⦆ = (f⦅f⁻¹⦅x⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                      let u₅ := id_val_prop (setPO(𝓑)) x (v₂)
                      let u₅ := Eq.trans (Eq.symm u₅) (u₄)

                      let v₃ := Iff.mp (image_prop f X (x)) (And.left hx)

                      Exists.elim v₃ (
                        fun (i) =>
                          fun (hi) =>
                            let v₄ := And.right hi
                            let v₅ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) t (f⁻¹⦅x⦆) x v₀) u₅
                            let v₆ := And.left (And.right s) i (f⁻¹⦅x⦆) x v₄ v₅
                            let v₇ := eq_subst (fun (m) => m ∈ X) (i) (f⁻¹⦅x⦆) (v₆) (And.left hi)

                            let u := Iff.mpr (hφ₁φ₂x (f⁻¹⦅x⦆) (v₇)) (
                              eq_subst (fun (m) => φ₂ m) x (f⦅f⁻¹⦅x⦆⦆) (u₅) (And.right hx)
                            )

                            And.intro (v₇) (u)
                      )
                    )
              )
          )




theorem poiso_allin_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ setPO(𝓐); ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∀ x ∈ setPO(𝓐); (φ₁ x)) ↔ (∀ x ∈ setPO(𝓑); (φ₂ x))) :=
  fun (𝓐 𝓑 f) =>
    fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
      let u₁ := bijection_inv_mp f setPO(𝓐) setPO(𝓑) (And.left hf)

      let s := And.left hf
      let t := And.left s
      let r := And.left t
      let k := And.left r



      fun (hφ₁φ₂x : (∀ x ∈ setPO(𝓐); ((φ₁ x) ↔ (φ₂ (f⦅x⦆))))) =>
        Iff.intro
        (
          fun (hφ₁x) =>
            fun (x) =>
              fun (hx : x ∈ setPO(𝓑)) =>

                let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) x hx
                let u₄ := eq_subst (fun (t) => t⦅x⦆ = (f⦅f⁻¹⦅x⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                let u₅ := id_val_prop (setPO(𝓑)) x hx
                let u₅ := Eq.trans (Eq.symm u₅) (u₄)
                let v := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) x hx
                let u := Iff.mp (hφ₁φ₂x (f⁻¹⦅x⦆) (v)) (
                  hφ₁x (f⁻¹⦅x⦆) (v)
                )

                eq_subst (fun (t) => φ₂ t) (f⦅f⁻¹⦅x⦆⦆) x (Eq.symm u₅) (u)
        )
        (
          fun (hφ₂x) =>
            fun (x) =>
              fun (hx : x ∈ setPO(𝓐)) =>
                Iff.mpr (hφ₁φ₂x x hx) (
                  hφ₂x (f⦅x⦆) (
                    val_in_B f (setPO(𝓐)) (setPO(𝓑)) (t) x hx
                  )
                )
        )



theorem posio_exiin_equiv (φ₁ φ₂ : Set → Prop) :
∀ 𝓐 𝓑 f, (f PO_ISO 𝓐 To 𝓑) → (∀ x ∈ setPO(𝓐); ((φ₁ x) ↔ (φ₂ (f⦅x⦆)))) → ((∃ x ∈ setPO(𝓐); (φ₁ x)) ↔ (∃ x ∈ setPO(𝓑); (φ₂ x))) :=
  fun (𝓐 𝓑 f) =>
    fun (hf : (f PO_ISO 𝓐 To 𝓑)) =>
      let u₁ := bijection_inv_mp f setPO(𝓐) setPO(𝓑) (And.left hf)
      fun (hφ₁φ₂x : (∀ x ∈ setPO(𝓐); ((φ₁ x) ↔ (φ₂ (f⦅x⦆))))) =>

        let s := And.left hf
        let t := And.left s
        let r := And.left t
        let k := And.left r

        Iff.intro
        (
          fun (hφ₂x) =>
            Exists.elim hφ₂x (
              fun (x) =>
                fun (hx) =>
                  Exists.intro (f⦅x⦆) (
                    And.intro (val_in_B f (setPO(𝓐)) (setPO(𝓑)) (t) x (And.left hx)) (

                      Iff.mp (hφ₁φ₂x x (And.left hx)) (And.right hx)
                    )
                  )
            )
        )
        (
          fun (hφ₁x) =>
            Exists.elim hφ₁x (
              fun (x) =>
                fun (hx) =>
                  let v := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) x (And.left hx)


                  Exists.intro (f⁻¹⦅x⦆) (
                    And.intro (v) (

                      Iff.mpr (hφ₁φ₂x (f⁻¹⦅x⦆) v) (

                        let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                        let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) x (And.left hx)
                        let u₄ := eq_subst (fun (t) => t⦅x⦆ = (f⦅f⁻¹⦅x⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                        let u₅ := id_val_prop (setPO(𝓑)) x (And.left hx)
                        let u₅ := Eq.trans (Eq.symm u₅) (u₄)


                        eq_subst (fun (t) => φ₂ t) x (f⦅f⁻¹⦅x⦆⦆) (u₅) (And.right hx)
                      )


                    )
                  )


            )
        )



theorem poiso_minal : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_minimal 𝓐 X x) ↔ (is_minimal 𝓑 (f.[X]) (f⦅x⦆))) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX :  (X ⊆ setPO(𝓐))) =>
      fun (hx : x ∈ setPO(𝓐)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ₁ := fun (x) => x ∈ X
          let φ₂ := fun (x) => x ∈ f.[X]
          let φ₃ := fun (x) => ∀ y ∈ X; ¬ (y . (≺(𝓐)) . x)
          let φ₄ := fun (x) => ∀ y ∈ f.[X]; ¬(y . (≺(𝓑)) . x)
          poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (

            iso_in₂ 𝓐 𝓑 X f x hx (And.right (And.right hf))

          ) (

            let φ₅ := fun (y) => (¬ (y . (≺(𝓐)) . x))
            let φ₆ := fun (y) =>  (¬ (y . (≺(𝓑)) . (f⦅x⦆)))

            let φ₇ := fun (y) => (y . (≺(𝓐)) . x)
            let φ₈ := fun (y) =>  (y . (≺(𝓑)) . (f⦅x⦆))


            poiso_all_equiv φ₅ φ₆ 𝓐 𝓑 f X hX (And.right (And.right hf)) (
              fun (y) =>
                fun (hy : y ∈ X) =>
                  poiso_not_equiv φ₇ φ₈ f y (
                    iso_R₁ 𝓐 𝓑 f (And.right (And.right hf)) (And.left hf) (And.left (And.right hf)) y (hX y hy) x hx
                  )
            )
          )


theorem poiso_maxal : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_maximal 𝓐 X x) ↔ (is_maximal 𝓑 (f.[X]) (f⦅x⦆))) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX :  (X ⊆ setPO(𝓐))) =>
      fun (hx : x ∈ setPO(𝓐)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ₁ := fun (x) => x ∈ X
          let φ₂ := fun (x) => x ∈ f.[X]
          let φ₃ := fun (x) => ∀ y ∈ X; ¬ (x . (≺(𝓐)) . y)
          let φ₄ := fun (x) => ∀ y ∈ f.[X]; ¬(x . (≺(𝓑)) . y)
          poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (

            iso_in₂ 𝓐 𝓑 X f x hx (And.right (And.right hf))

          ) (

            let φ₅ := fun (y) => (¬ (x . (≺(𝓐)) . y))
            let φ₆ := fun (y) =>  (¬ ((f⦅x⦆) . (≺(𝓑)) . y))

            let φ₇ := fun (y) => (x . (≺(𝓐)) . y)
            let φ₈ := fun (y) =>  ((f⦅x⦆) . (≺(𝓑)) . y)


            poiso_all_equiv φ₅ φ₆ 𝓐 𝓑 f X hX (And.right (And.right hf)) (
              fun (y) =>
                fun (hy : y ∈ X) =>
                  poiso_not_equiv φ₇ φ₈ f y (
                    iso_R₁ 𝓐 𝓑 f (And.right (And.right hf)) (And.left hf) (And.left (And.right hf)) x hx y (hX y hy)
                  )
            )
          )



theorem poiso_minum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_minimum 𝓐 X x) ↔ (is_minimum 𝓑 (f.[X]) (f⦅x⦆))) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX :  (X ⊆ setPO(𝓐))) =>
      fun (hx : x ∈ setPO(𝓐)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ₁ := fun (x) => x ∈ X
          let φ₂ := fun (x) => x ∈ f.[X]
          let φ₃ := fun (x) => ∀ y ∈ X; (x . (≼(𝓐)) . y)
          let φ₄ := fun (x) => ∀ y ∈ f.[X]; (x . (≼(𝓑)) . y)
          poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (

            iso_in₂ 𝓐 𝓑 X f x hx (And.right (And.right hf))

          ) (

            let φ₅ := fun (y) => (x . (≼(𝓐)) . y)
            let φ₆ := fun (y) =>  ((f⦅x⦆) . (≼(𝓑)) . (y))



            poiso_all_equiv φ₅ φ₆ 𝓐 𝓑 f X hX (And.right (And.right hf)) (
              fun (y) =>
                fun (hy : y ∈ X) =>
                  iso_R₂ 𝓐 𝓑 f (And.right (And.right hf)) x hx y (
                    hX y (hy)
                  )
            )
          )


theorem poiso_maxum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_maximum 𝓐 X x) ↔ (is_maximum 𝓑 (f.[X]) (f⦅x⦆))) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX :  (X ⊆ setPO(𝓐))) =>
      fun (hx : x ∈ setPO(𝓐)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ₁ := fun (x) => x ∈ X
          let φ₂ := fun (x) => x ∈ f.[X]
          let φ₃ := fun (x) => ∀ y ∈ X; (y . (≼(𝓐)) . x)
          let φ₄ := fun (x) => ∀ y ∈ f.[X]; (y . (≼(𝓑)) . x)
          poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (

            iso_in₂ 𝓐 𝓑 X f x hx (And.right (And.right hf))

          ) (

            let φ₅ := fun (y) => (y . (≼(𝓐)) . x)
            let φ₆ := fun (y) =>  (y . (≼(𝓑)) . (f⦅x⦆))



            poiso_all_equiv φ₅ φ₆ 𝓐 𝓑 f X hX (And.right (And.right hf)) (
              fun (y) =>
                fun (hy : y ∈ X) =>
                  iso_R₂ 𝓐 𝓑 f (And.right (And.right hf)) y (
                    hX y (hy)
                  ) x hx
            )
          )


theorem poiso_lowbou : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_lower_bound 𝓐 X x) ↔ (is_lower_bound 𝓑 (f.[X]) (f⦅x⦆)) ) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX :  (X ⊆ setPO(𝓐))) =>
      fun (hx : x ∈ setPO(𝓐)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ₁ := fun (x) => x ∈ setPO(𝓐)
            let φ₂ := fun (x) => x ∈ setPO(𝓑)
            let φ₃ := fun (x) => ∀ y ∈ X; (x . (≼(𝓐)) . y)
            let φ₄ := fun (x) => ∀ y ∈ f.[X]; (x . (≼(𝓑)) . y)
            poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (

              iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx

            ) (

              let φ₅ := fun (y) => (x . (≼(𝓐)) . y)
              let φ₆ := fun (y) =>  ((f⦅x⦆) . (≼(𝓑)) . (y))



              poiso_all_equiv φ₅ φ₆ 𝓐 𝓑 f X hX (And.right (And.right hf)) (
                fun (y) =>
                  fun (hy : y ∈ X) =>
                    iso_R₂ 𝓐 𝓑 f (And.right (And.right hf)) x hx y (
                      hX y (hy)
                    )
              )
            )



theorem poiso_uppbou : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_upper_bound 𝓐 X x) ↔ (is_upper_bound 𝓑 (f.[X]) (f⦅x⦆)) ) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX :  (X ⊆ setPO(𝓐))) =>
      fun (hx : x ∈ setPO(𝓐)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ₁ := fun (x) => x ∈ setPO(𝓐)
            let φ₂ := fun (x) => x ∈ setPO(𝓑)
            let φ₃ := fun (x) => ∀ y ∈ X; (y . (≼(𝓐)) . x)
            let φ₄ := fun (x) => ∀ y ∈ f.[X]; (y . (≼(𝓑)) . x)
            poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (

              iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx

            ) (

              let φ₅ := fun (y) => (y . (≼(𝓐)) . x)
              let φ₆ := fun (y) =>  (y . (≼(𝓑)) . ((f⦅x⦆)))



              poiso_all_equiv φ₅ φ₆ 𝓐 𝓑 f X hX (And.right (And.right hf)) (
                fun (y) =>
                  fun (hy : y ∈ X) =>
                    iso_R₂ 𝓐 𝓑 f (And.right (And.right hf)) y (
                      hX y (hy)
                    ) x hx
              )
            )


theorem minexi_constr : ∀ 𝓐 X, (X ⊆ setPO(𝓐)) → ((𝓐 MinExi X) ↔ (∃ x ∈ setPO(𝓐); is_minimum 𝓐 X x)) :=
  fun (_) =>
    fun (_) =>
      fun (hX) =>
        Iff.intro
        (
          fun (hxE) =>
            Exists.elim hxE (
              fun (x) =>
                fun (hx) =>
                  Exists.intro x (And.intro (hX x (And.left hx)) (hx))
            )
        )
        (
          fun (hxA) =>
            Exists.elim hxA (
              fun (x) =>
                fun (hx) =>
                  Exists.intro x (And.right hx)
            )
        )


theorem maxexi_constr : ∀ 𝓐 X, (X ⊆ setPO(𝓐)) → ((𝓐 MaxExi X) ↔ (∃ x ∈ setPO(𝓐); is_maximum 𝓐 X x)) :=
   fun (_) =>
    fun (_) =>
      fun (hX) =>
        Iff.intro
        (
          fun (hxE) =>
            Exists.elim hxE (
              fun (x) =>
                fun (hx) =>
                  Exists.intro x (And.intro (hX x (And.left hx)) (hx))
            )
        )
        (
          fun (hxA) =>
            Exists.elim hxA (
              fun (x) =>
                fun (hx) =>
                  Exists.intro x (And.right hx)
            )
        )


theorem poiso_minexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 MinExi X) ↔ (𝓑 MinExi f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let hpoiso := And.right (And.right hf)
          let hbij := And.left hpoiso
          let hfunc := And.left hbij
          let hpfunc := And.left hfunc
          let φ₁ := fun (x) => is_minimum 𝓐 X x
          let φ₂ := fun (x) => is_minimum 𝓑 (f.[X]) (x)
          let u₀ := specification_set_subset (fun (t) => ∃ s ∈ X; (s . f . t)) (rng f)
          let u₁ := subset_trans (f.[X]) (rng f) (setPO(𝓑)) u₀ (rng_partial_function f setPO(𝓐) setPO(𝓑) (hpfunc))
          let u := posio_exiin_equiv φ₁ φ₂ 𝓐 𝓑 f (hpoiso) (
            fun (y) =>
              fun (hy : y ∈ setPO(𝓐)) =>
                poiso_minum 𝓐 𝓑 f X y hX hy (hf)
          )
          Iff.intro
          (
            fun (hexi₁) =>
              Iff.mpr (minexi_constr 𝓑 (f.[X]) u₁) (
                Iff.mp (u) (
                  Iff.mp (minexi_constr 𝓐 X hX) (
                    hexi₁
                  )
                )
              )
          )
          (
            fun (hexi₁) =>
              Iff.mpr (minexi_constr 𝓐 (X) hX) (
                Iff.mpr (u) (
                  Iff.mp (minexi_constr 𝓑 (f.[X]) u₁) (
                    hexi₁
                  )
                )
              )
          )




theorem poiso_maxexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 MaxExi X) ↔ (𝓑 MaxExi f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let hpoiso := And.right (And.right hf)
          let hbij := And.left hpoiso
          let hfunc := And.left hbij
          let hpfunc := And.left hfunc
          let φ₁ := fun (x) => is_maximum 𝓐 X x
          let φ₂ := fun (x) => is_maximum 𝓑 (f.[X]) (x)
          let u₀ := specification_set_subset (fun (t) => ∃ s ∈ X; (s . f . t)) (rng f)
          let u₁ := subset_trans (f.[X]) (rng f) (setPO(𝓑)) u₀ (rng_partial_function f setPO(𝓐) setPO(𝓑) (hpfunc))
          let u := posio_exiin_equiv φ₁ φ₂ 𝓐 𝓑 f (hpoiso) (
            fun (y) =>
              fun (hy : y ∈ setPO(𝓐)) =>
                poiso_maxum 𝓐 𝓑 f X y hX hy (hf)
          )
          Iff.intro
          (
            fun (hexi₁) =>
              Iff.mpr (maxexi_constr 𝓑 (f.[X]) u₁) (
                Iff.mp (u) (
                  Iff.mp (maxexi_constr 𝓐 X hX) (
                    hexi₁
                  )
                )
              )
          )
          (
            fun (hexi₁) =>
              Iff.mpr (maxexi_constr 𝓐 (X) hX) (
                Iff.mpr (u) (
                  Iff.mp (maxexi_constr 𝓑 (f.[X]) u₁) (
                    hexi₁
                  )
                )
              )
          )



theorem poiso_subs_eq (φ : Set → Set → Set → Prop) (ψ : Set → Set → Set) :
∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 X x, (x ∈ ψ 𝓧 X ↔ φ 𝓧 X x)) →
(∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (ψ 𝓧 X) ⊆ setPO(𝓧)) →
(∀ X, (∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆)))) → (f.[ψ 𝓐 X] = ψ 𝓑 (f.[X]))) :=
  fun (𝓐 𝓑 f) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      let hff := And.right (And.right hf)
      let u₁ := bijection_inv_mp f setPO(𝓐) setPO(𝓑) (And.left hff)
      let s := And.left hff
      let t := And.left s
      let r := And.left t
      let k := And.left r
      fun (hψφ : ((∀ 𝓧 X x, (x ∈ ψ 𝓧 X ↔ φ 𝓧 X x)))) =>
        fun (hsub : ((∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (ψ 𝓧 X) ⊆ setPO(𝓧)) )) =>
          fun (X) =>
            fun (hψeq : (∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆))))) =>
                  extensionality (f.[ψ 𝓐 X]) (ψ 𝓑 (f.[X])) (
                    fun (x) =>
                      Iff.intro
                      (
                        fun (hx : x ∈ (f.[ψ 𝓐 X])) =>

                          let M := ψ 𝓐 X

                          let hxB := specification_set_subset (fun (t) => ∃ s ∈ M; (s . f . t)) (rng f)
                          let hxB₁ := subset_trans (f.[M]) (rng f) (setPO(𝓑)) (hxB) (rng_partial_function f setPO(𝓐) setPO(𝓑) (r)) x hx


                          let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                          let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) x (hxB₁)
                          let u₄ := eq_subst (fun (t) => t⦅x⦆ = (f⦅f⁻¹⦅x⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                          let u₅ := id_val_prop (setPO(𝓑)) x (hxB₁)
                          let u₆ := Eq.trans (Eq.symm u₅) (u₄)

                          Iff.mpr (hψφ 𝓑 (f.[X]) x) (
                            let u₇ := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) x (hxB₁)
                            let u := Iff.mp (hψeq (f⁻¹⦅x⦆) (u₇)) (
                              Iff.mp (hψφ 𝓐 X (f⁻¹⦅x⦆)) (
                                let u₈ := Iff.mp (image_prop f M (x)) hx
                                Exists.elim u₈ (
                                  fun (i) =>
                                    fun (hi) =>

                                      let v₄ := And.right hi
                                      let v₅ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) t (f⁻¹⦅x⦆) x u₇) u₆
                                      let v₆ := And.left (And.right s) i (f⁻¹⦅x⦆) x v₄ v₅
                                      eq_subst (fun (m) => m ∈ M) (i) (f⁻¹⦅x⦆) (v₆) (And.left hi)
                                )


                              )
                            )

                            eq_subst (fun (m) => φ 𝓑 (f.[X]) m) (f⦅f⁻¹⦅x⦆⦆) x (Eq.symm u₆) u
                          )
                      )
                      (
                        fun (hx : x ∈ ψ 𝓑 (f.[X])) =>
                          let M := ψ 𝓐 X
                          Iff.mpr (image_prop f M x) (
                            Exists.intro (f⁻¹⦅x⦆) (

                              let hxB₀ := specification_set_subset (fun (t) => ∃ s ∈ X; (s . f . t)) (rng f)
                              let hxB₁ := subset_trans (f.[X]) (rng f) (setPO(𝓑)) (hxB₀) (rng_partial_function f setPO(𝓐) setPO(𝓑) (r))

                              let hxB₂ := hsub 𝓑 (f.[X]) (hxB₁) x hx


                              let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                              let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) x (hxB₂)
                              let u₄ := eq_subst (fun (t) => t⦅x⦆ = (f⦅f⁻¹⦅x⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                              let u₅ := id_val_prop (setPO(𝓑)) x (hxB₂)
                              let u₆ := Eq.trans (Eq.symm u₅) (u₄)
                              let u₇ := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) x (hxB₂)
                              let u₈ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) setPO(𝓑) t (f⁻¹⦅x⦆) x u₇) u₆

                              And.intro (

                                Iff.mpr (hψφ 𝓐 X (f⁻¹⦅x⦆)) (
                                  Iff.mpr (hψeq (f⁻¹⦅x⦆) u₇) (
                                    eq_subst (fun (m) => φ 𝓑 (f.[X]) m) x (f⦅f⁻¹⦅x⦆⦆) (u₆) (
                                      Iff.mp (hψφ 𝓑 (f.[X]) x) (
                                        hx
                                      )
                                    )
                                  )
                                )

                              ) (u₈)

                            )
                          )
                      )
                  )


theorem poiso_minset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[min_set 𝓐 X] = min_set 𝓑 (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
        let φ := fun (𝓐) => fun (X) => fun (x) => is_minimal 𝓐 X x
        let ψ := fun (𝓐) => fun (X) => min_set 𝓐 X
        let u := fun (𝓧) => fun (X) => fun (hX : X ⊆ setPO(𝓧)) => subset_trans (ψ 𝓧 X) (X) (setPO(𝓧)) (specification_set_subset (fun (t) => φ 𝓧 X t) (X)) (hX)
        let v := fun (x) => fun (hx : x ∈ setPO(𝓐)) => poiso_minal 𝓐 𝓑 f X x hX hx hf

        poiso_subs_eq φ ψ 𝓐 𝓑 f hf (min_set_is_min_set) (u) X v


theorem poiso_maxset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[max_set 𝓐 X] = max_set 𝓑 (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
        let φ := fun (𝓐) => fun (X) => fun (x) => is_maximal 𝓐 X x
        let ψ := fun (𝓐) => fun (X) => max_set 𝓐 X
        let u := fun (𝓧) => fun (X) => fun (hX : X ⊆ setPO(𝓧)) => subset_trans (ψ 𝓧 X) (X) (setPO(𝓧)) (specification_set_subset (fun (t) => φ 𝓧 X t) (X)) (hX)
        let v := fun (x) => fun (hx : x ∈ setPO(𝓐)) => poiso_maxal 𝓐 𝓑 f X x hX hx hf

        poiso_subs_eq φ ψ 𝓐 𝓑 f hf (max_set_is_max_set) (u) X v

theorem poiso_lowset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[𝓐 ▾ X] = 𝓑 ▾ (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
        let φ := fun (𝓐) => fun (X) => fun (x) => is_lower_bound 𝓐 X x
        let ψ := fun (𝓐) => fun (X) => 𝓐 ▾ X
        let u := fun (𝓧) => fun (X) => fun (_ : X ⊆ setPO(𝓧)) => specification_set_subset (fun (t) => φ 𝓧 X t) (setPO(𝓧))
        let v := fun (x) => fun (hx : x ∈ setPO(𝓐)) => poiso_lowbou 𝓐 𝓑 f X x hX hx hf

        poiso_subs_eq φ ψ 𝓐 𝓑 f hf (low_bou_set_is_low_bou) (u) X (v)


theorem poiso_uppset : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f.[𝓐 ▴ X] = 𝓑 ▴ (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
        let φ := fun (𝓐) => fun (X) => fun (x) => is_upper_bound 𝓐 X x
        let ψ := fun (𝓐) => fun (X) => 𝓐 ▴ X
        let u := fun (𝓧) => fun (X) => fun (_ : X ⊆ setPO(𝓧)) => specification_set_subset (fun (t) => φ 𝓧 X t) (setPO(𝓧))
        let v := fun (x) => fun (hx : x ∈ setPO(𝓐)) => poiso_uppbou 𝓐 𝓑 f X x hX hx hf

        poiso_subs_eq φ ψ 𝓐 𝓑 f hf (upp_bou_set_is_upp_bou) (u) X (v)



theorem poiso_sup : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_supremum 𝓐 X x) ↔ (is_supremum 𝓑 (f.[X]) (f⦅x⦆))) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let u₀ := specification_set_subset (fun (t) => is_upper_bound 𝓐 X t) (setPO(𝓐))
          let u := poiso_minum 𝓐 𝓑 f (𝓐 ▴ X) x (u₀) hx hf
          let u₁ := poiso_uppset 𝓐 𝓑 f X hX hf
          eq_subst (fun (t) => (is_minimum (𝓐) (𝓐 ▴ X) x) ↔ (is_minimum 𝓑 (t) (f⦅x⦆))) (f.[𝓐 ▴ X]) (𝓑 ▴ (f.[X])) (u₁) (u)


theorem poiso_inf : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_infimum 𝓐 X x) ↔ (is_infimum 𝓑 (f.[X]) (f⦅x⦆))) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let u₀ := specification_set_subset (fun (t) => is_lower_bound 𝓐 X t) (setPO(𝓐))
          let u := poiso_maxum 𝓐 𝓑 f (𝓐 ▾ X) x (u₀) hx hf
          let u₁ := poiso_lowset 𝓐 𝓑 f X hX hf
          eq_subst (fun (t) => (is_maximum (𝓐) (𝓐 ▾ X) x) ↔ (is_maximum 𝓑 (t) (f⦅x⦆))) (f.[𝓐 ▾ X]) (𝓑 ▾ (f.[X])) (u₁) (u)


theorem supexi_constr : ∀ 𝓐 X, ((𝓐 SuprExi X) ↔ (∃ x ∈ setPO(𝓐); is_supremum 𝓐 X x)) :=
  fun (𝓐) =>
    fun (X) =>
      Iff.intro
      (
        fun (hxE) =>
          Exists.elim hxE (
            fun (x) =>
              fun (hx) =>
                let u₁ := And.left hx
                let u₂ := And.left (Iff.mp (upp_bou_set_is_upp_bou 𝓐 X x) u₁)
                Exists.intro x (And.intro (u₂) (hx))
          )
      )
      (
        fun (hxA) =>
          Exists.elim hxA (
            fun (x) =>
              fun (hx) =>
                Exists.intro x (And.right hx)
          )
      )


theorem infexi_constr : ∀ 𝓐 X, ((𝓐 InfmExi X) ↔ (∃ x ∈ setPO(𝓐); is_infimum 𝓐 X x)) :=
   fun (𝓐) =>
    fun (X) =>
      Iff.intro
      (
        fun (hxE) =>
          Exists.elim hxE (
            fun (x) =>
              fun (hx) =>
                let u₁ := And.left hx
                let u₂ := And.left (Iff.mp (low_bou_set_is_low_bou 𝓐 X x) u₁)
                Exists.intro x (And.intro (u₂) (hx))
          )
      )
      (
        fun (hxA) =>
          Exists.elim hxA (
            fun (x) =>
              fun (hx) =>
                Exists.intro x (And.right hx)
          )
      )


theorem poiso_supexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 SuprExi X) ↔ (𝓑 SuprExi (f.[X]))) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
        let hpoiso := And.right (And.right hf)
        let φ₁ := fun (x) => is_supremum 𝓐 X x
        let φ₂ := fun (x) => is_supremum 𝓑 (f.[X]) (x)
        let u := posio_exiin_equiv φ₁ φ₂ 𝓐 𝓑 f (hpoiso) (
          fun (y) =>
            fun (hy : y ∈ setPO(𝓐)) =>
              poiso_sup 𝓐 𝓑 f X y hX hy (hf)
        )
        Iff.intro
          (
            fun (hexi₁) =>
              Iff.mpr (supexi_constr 𝓑 (f.[X])) (
                Iff.mp (u) (
                  Iff.mp (supexi_constr 𝓐 X) (
                    hexi₁
                  )
                )
              )
          )
          (
            fun (hexi₁) =>
              Iff.mpr (supexi_constr 𝓐 (X)) (
                Iff.mpr (u) (
                  Iff.mp (supexi_constr 𝓑 (f.[X])) (
                    hexi₁
                  )
                )
              )
          )


theorem poiso_infexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 InfmExi X) ↔ (𝓑 InfmExi (f.[X]))) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
        let hpoiso := And.right (And.right hf)
        let φ₁ := fun (x) => is_infimum 𝓐 X x
        let φ₂ := fun (x) => is_infimum 𝓑 (f.[X]) (x)
        let u := posio_exiin_equiv φ₁ φ₂ 𝓐 𝓑 f (hpoiso) (
          fun (y) =>
            fun (hy : y ∈ setPO(𝓐)) =>
              poiso_inf 𝓐 𝓑 f X y hX hy (hf)
        )
        Iff.intro
          (
            fun (hexi₁) =>
              Iff.mpr (infexi_constr 𝓑 (f.[X])) (
                Iff.mp (u) (
                  Iff.mp (infexi_constr 𝓐 X) (
                    hexi₁
                  )
                )
              )
          )
          (
            fun (hexi₁) =>
              Iff.mpr (infexi_constr 𝓐 (X)) (
                Iff.mpr (u) (
                  Iff.mp (infexi_constr 𝓑 (f.[X])) (
                    hexi₁
                  )
                )
              )
          )



theorem poiso_interv_eq (c d : Set) (φ : Set → Set → Set → Set → Prop) (ψ : Set → Set → Set → Set)
 : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 x, ∀ a b, (x ∈ ψ 𝓧 a b ↔ φ 𝓧 a b x)) →
 (∀ 𝓧 a b, (ψ 𝓧 a b) ⊆ setPO(𝓧)) → ((∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 c d x) ↔ (φ 𝓑 (f⦅c⦆) (f⦅d⦆) (f⦅x⦆)))) → (
  f.[ψ 𝓐 c d] = ψ 𝓑 (f⦅c⦆) (f⦅d⦆)
 )) :=
  fun (𝓐 𝓑 f) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      let hff := And.right (And.right hf)
      let u₁ := bijection_inv_mp f setPO(𝓐) setPO(𝓑) (And.left hff)
      let s := And.left hff
      let t := And.left s
      let r := And.left t
      let k := And.left r
      fun (hab : (∀ 𝓧 x, ∀ a b, (x ∈ ψ 𝓧 a b ↔ φ 𝓧 a b x)) ) =>
        fun (h𝓧 :  (∀ 𝓧 a b, (ψ 𝓧 a b) ⊆ setPO(𝓧))) =>
          fun (hφ : (∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 c d x) ↔ (φ 𝓑 (f⦅c⦆) (f⦅d⦆) (f⦅x⦆))))) =>
                extensionality (f.[ψ 𝓐 c d]) (ψ 𝓑 (f⦅c⦆) (f⦅d⦆)) (
                  fun (y) =>
                    Iff.intro
                    (
                      fun (hy : y ∈ (f.[ψ 𝓐 c d])) =>
                        Iff.mpr (hab 𝓑 y (f⦅c⦆) (f⦅d⦆)) (

                          let M := ψ 𝓐 c d

                          let hyB := specification_set_subset (fun (t) => ∃ s ∈ M; (s . f . t)) (rng f)
                          let hyB₁ := subset_trans (f.[M]) (rng f) (setPO(𝓑)) (hyB) (rng_partial_function f setPO(𝓐) setPO(𝓑) (r)) y (hy)
                          let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                          let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) y (hyB₁)
                          let u₄ := eq_subst (fun (t) => t⦅y⦆ = (f⦅f⁻¹⦅y⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                          let u₅ := id_val_prop (setPO(𝓑)) y (hyB₁)
                          let u₆ := Eq.trans (Eq.symm u₅) (u₄)
                          let u₇ := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) y (hyB₁)

                          let u := Iff.mp (hφ (f⁻¹⦅y⦆) (u₇)) (

                            Iff.mp (hab 𝓐 (f⁻¹⦅y⦆) c d) (

                              let u₀ := Iff.mp (image_prop f M y) hy

                              Exists.elim u₀ (
                                fun (i) =>
                                  fun (hi) =>

                                    eq_subst (fun (m) => m ∈ M) (i) (f⁻¹⦅y⦆) (

                                      let u₈ := And.right hi
                                      let u₉ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) setPO(𝓑) t (f⁻¹⦅y⦆) y u₇) (u₆)
                                      And.left (And.right s) i (f⁻¹⦅y⦆) y u₈ u₉




                                    ) (And.left hi)
                              )
                            )


                          )

                          eq_subst (fun (m) => φ 𝓑 (f⦅c⦆) (f⦅d⦆) m) (f⦅f⁻¹⦅y⦆⦆) (y) (Eq.symm u₆) (u)
                        )
                    )
                    (
                      fun (hy : y ∈ (ψ 𝓑 (f⦅c⦆) (f⦅d⦆))) =>
                        let M := ψ 𝓐 c d
                        let hyB₁ := h𝓧 𝓑 (f⦅c⦆) (f⦅d⦆) y hy
                        let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                        let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) y (hyB₁)
                        let u₄ := eq_subst (fun (t) => t⦅y⦆ = (f⦅f⁻¹⦅y⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                        let u₅ := id_val_prop (setPO(𝓑)) y (hyB₁)
                        let u₆ := Eq.trans (Eq.symm u₅) (u₄)
                        let u₇ := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) y (hyB₁)
                        let u₉ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) setPO(𝓑) t (f⁻¹⦅y⦆) y u₇) (u₆)
                        Iff.mpr (image_prop f M y) (
                          Exists.intro (f⁻¹⦅y⦆) (
                            And.intro (
                              Iff.mpr (hab 𝓐 (f⁻¹⦅y⦆) c d) (
                                Iff.mpr (hφ (f⁻¹⦅y⦆) u₇) (
                                  eq_subst (fun (m) => φ 𝓑 (f⦅c⦆) (f⦅d⦆) m) (y) (f⦅f⁻¹⦅y⦆⦆) u₆ (
                                    Iff.mp (hab 𝓑 y (f⦅c⦆) (f⦅d⦆)) (
                                      hy
                                    )
                                  )
                                )
                              )

                            ) (u₉)
                          )
                        )
                    )
                )




theorem poiso_interv_eq₂ (c : Set) (φ : Set → Set → Set → Prop) (ψ : Set → Set → Set)
 : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (∀ 𝓧 x, ∀ a, (x ∈ ψ 𝓧 a ↔ φ 𝓧 a x)) →
 (∀ 𝓧 a, (ψ 𝓧 a) ⊆ setPO(𝓧)) → ((∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 c x) ↔ (φ 𝓑 (f⦅c⦆) (f⦅x⦆)))) → (
  f.[ψ 𝓐 c] = ψ 𝓑 (f⦅c⦆)
 )) :=
  fun (𝓐 𝓑 f) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      let hff := And.right (And.right hf)
      let u₁ := bijection_inv_mp f setPO(𝓐) setPO(𝓑) (And.left hff)
      let s := And.left hff
      let t := And.left s
      let r := And.left t
      let k := And.left r
      fun (hab : (∀ 𝓧 x, ∀ a, (x ∈ ψ 𝓧 a ↔ φ 𝓧 a x)) ) =>
        fun (h𝓧 :  (∀ 𝓧 a, (ψ 𝓧 a) ⊆ setPO(𝓧))) =>
          fun (hφ : (∀ x, (x ∈ setPO(𝓐)) → ((φ 𝓐 c x) ↔ (φ 𝓑 (f⦅c⦆) (f⦅x⦆))))) =>
                extensionality (f.[ψ 𝓐 c]) (ψ 𝓑 (f⦅c⦆)) (
                  fun (y) =>
                    Iff.intro
                    (
                      fun (hy : y ∈ (f.[ψ 𝓐 c])) =>
                        Iff.mpr (hab 𝓑 y (f⦅c⦆)) (

                          let M := ψ 𝓐 c

                          let hyB := specification_set_subset (fun (t) => ∃ s ∈ M; (s . f . t)) (rng f)
                          let hyB₁ := subset_trans (f.[M]) (rng f) (setPO(𝓑)) (hyB) (rng_partial_function f setPO(𝓐) setPO(𝓑) (r)) y (hy)
                          let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                          let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) y (hyB₁)
                          let u₄ := eq_subst (fun (t) => t⦅y⦆ = (f⦅f⁻¹⦅y⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                          let u₅ := id_val_prop (setPO(𝓑)) y (hyB₁)
                          let u₆ := Eq.trans (Eq.symm u₅) (u₄)
                          let u₇ := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) y (hyB₁)

                          let u := Iff.mp (hφ (f⁻¹⦅y⦆) (u₇)) (

                            Iff.mp (hab 𝓐 (f⁻¹⦅y⦆) c) (

                              let u₀ := Iff.mp (image_prop f M y) hy

                              Exists.elim u₀ (
                                fun (i) =>
                                  fun (hi) =>

                                    eq_subst (fun (m) => m ∈ M) (i) (f⁻¹⦅y⦆) (

                                      let u₈ := And.right hi
                                      let u₉ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) setPO(𝓑) t (f⁻¹⦅y⦆) y u₇) (u₆)
                                      And.left (And.right s) i (f⁻¹⦅y⦆) y u₈ u₉




                                    ) (And.left hi)
                              )
                            )


                          )

                          eq_subst (fun (m) => φ 𝓑 (f⦅c⦆) m) (f⦅f⁻¹⦅y⦆⦆) (y) (Eq.symm u₆) (u)
                        )
                    )
                    (
                      fun (hy : y ∈ (ψ 𝓑 (f⦅c⦆))) =>
                        let M := ψ 𝓐 c
                        let hyB₁ := h𝓧 𝓑 (f⦅c⦆) y hy
                        let u₂ := And.right (Iff.mp (id_bijection_criterion f (setPO(𝓐)) (setPO(𝓑)) k) s)
                        let u₃ := And.right (function_composition_A (f⁻¹) f (setPO(𝓑)) (setPO(𝓐)) (setPO(𝓑)) (And.left u₁) t) y (hyB₁)
                        let u₄ := eq_subst (fun (t) => t⦅y⦆ = (f⦅f⁻¹⦅y⦆⦆)) (f ∘ f⁻¹) (id_ setPO(𝓑)) (u₂) u₃
                        let u₅ := id_val_prop (setPO(𝓑)) y (hyB₁)
                        let u₆ := Eq.trans (Eq.symm u₅) (u₄)
                        let u₇ := val_in_B (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) (And.left u₁) y (hyB₁)
                        let u₉ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) setPO(𝓑) t (f⁻¹⦅y⦆) y u₇) (u₆)
                        Iff.mpr (image_prop f M y) (
                          Exists.intro (f⁻¹⦅y⦆) (
                            And.intro (
                              Iff.mpr (hab 𝓐 (f⁻¹⦅y⦆) c) (
                                Iff.mpr (hφ (f⁻¹⦅y⦆) u₇) (
                                  eq_subst (fun (m) => φ 𝓑 (f⦅c⦆) m) (y) (f⦅f⁻¹⦅y⦆⦆) u₆ (
                                    Iff.mp (hab 𝓑 y (f⦅c⦆)) (
                                      hy
                                    )
                                  )
                                )
                              )

                            ) (u₉)
                          )
                        )
                    )
                )


theorem poiso_lro : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐)) → (f.[⦗ a ; b ⦘ of 𝓐] = ⦗ f⦅a⦆ ; f⦅b⦆ ⦘ of 𝓑) :=
  fun (𝓐 𝓑 f a b) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      fun (ha) =>
        fun (hb) =>
          let φ := fun (𝓐) => fun (a) => fun (b) => fun (x) => (x ∈ setPO(𝓐)) ∧ ((a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b))
          let ψ := fun (𝓐) => fun (a) => fun (b) => ⦗ a ; b ⦘ of 𝓐

          poiso_interv_eq a b φ ψ 𝓐 𝓑 f hf (
            fun (𝓧 x a b) =>
              spec_is_spec (fun (m) => (a . (≺(𝓧)) . m) ∧ (m . (≺(𝓧)) . b)) (setPO(𝓧)) x
          ) (lro_sub_all) (
            fun (x) =>
              fun (hx : (x ∈ setPO(𝓐))) =>
                let φ₁ := fun (x) => (x ∈ setPO(𝓐))
                let φ₂ := fun (x) => (x ∈ setPO(𝓑))
                let φ₃ := fun (x) => (a . (≺(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)
                let φ₄ := fun (x) => ((f⦅a⦆) . (≺(𝓑)) . x) ∧ (x . (≺(𝓑)) . (f⦅b⦆ ))
                poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx) (
                  let φ₁ := fun (x) => (a . (≺(𝓐)) . x)
                  let φ₂ := fun (x) => ((f⦅a⦆)  . (≺(𝓑)) . x)
                  let φ₃ := fun (x) => (x . (≺(𝓐)) . b)
                  let φ₄ := fun (x) => (x  . (≺(𝓑)) . (f⦅b⦆))
                  poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (
                    iso_R₁ 𝓐 𝓑 f (And.right (And.right hf)) (And.left hf) (And.left (And.right hf)) a ha x hx
                  ) (
                    iso_R₁ 𝓐 𝓑 f (And.right (And.right hf)) (And.left hf) (And.left (And.right hf)) x hx b hb
                  )
                )
          )



theorem poiso_lcro : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐)) → (f.[⟦ a ; b ⦘ of 𝓐] = ⟦ f⦅a⦆ ; f⦅b⦆ ⦘ of 𝓑) :=
  fun (𝓐 𝓑 f a b) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      fun (ha) =>
        fun (hb) =>
          let φ := fun (𝓐) => fun (a) => fun (b) => fun (x) => (x ∈ setPO(𝓐)) ∧ ((a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b))
          let ψ := fun (𝓐) => fun (a) => fun (b) => ⟦ a ; b ⦘ of 𝓐

          poiso_interv_eq a b φ ψ 𝓐 𝓑 f hf (
            fun (𝓧 x a b) =>
              spec_is_spec (fun (m) => (a . (≼(𝓧)) . m) ∧ (m . (≺(𝓧)) . b)) (setPO(𝓧)) x
          ) (lcro_sub_all) (
            fun (x) =>
              fun (hx : (x ∈ setPO(𝓐))) =>
                let φ₁ := fun (x) => (x ∈ setPO(𝓐))
                let φ₂ := fun (x) => (x ∈ setPO(𝓑))
                let φ₃ := fun (x) => (a . (≼(𝓐)) . x) ∧ (x . (≺(𝓐)) . b)
                let φ₄ := fun (x) => ((f⦅a⦆) . (≼(𝓑)) . x) ∧ (x . (≺(𝓑)) . (f⦅b⦆ ))
                poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx) (
                  let φ₁ := fun (x) => (a . (≼(𝓐)) . x)
                  let φ₂ := fun (x) => ((f⦅a⦆)  . (≼(𝓑)) . x)
                  let φ₃ := fun (x) => (x . (≺(𝓐)) . b)
                  let φ₄ := fun (x) => (x  . (≺(𝓑)) . (f⦅b⦆))
                  poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (
                    iso_R₂ 𝓐 𝓑 f (And.right (And.right hf)) a ha x hx
                  ) (
                    iso_R₁ 𝓐 𝓑 f (And.right (And.right hf)) (And.left hf) (And.left (And.right hf)) x hx b hb
                  )
                )
          )

theorem poiso_locr : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐)) → (f.[⦗ a ; b ⟧ of 𝓐] = ⦗ f⦅a⦆ ; f⦅b⦆ ⟧ of 𝓑) :=
  fun (𝓐 𝓑 f a b) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      fun (ha) =>
        fun (hb) =>
          let φ := fun (𝓐) => fun (a) => fun (b) => fun (x) => (x ∈ setPO(𝓐)) ∧ ((a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b))
          let ψ := fun (𝓐) => fun (a) => fun (b) => ⦗ a ; b ⟧ of 𝓐

          poiso_interv_eq a b φ ψ 𝓐 𝓑 f hf (
            fun (𝓧 x a b) =>
              spec_is_spec (fun (m) => (a . (≺(𝓧)) . m) ∧ (m . (≼(𝓧)) . b)) (setPO(𝓧)) x
          ) (lorc_sub_all) (
            fun (x) =>
              fun (hx : (x ∈ setPO(𝓐))) =>
                let φ₁ := fun (x) => (x ∈ setPO(𝓐))
                let φ₂ := fun (x) => (x ∈ setPO(𝓑))
                let φ₃ := fun (x) => (a . (≺(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)
                let φ₄ := fun (x) => ((f⦅a⦆) . (≺(𝓑)) . x) ∧ (x . (≼(𝓑)) . (f⦅b⦆ ))
                poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx) (
                  let φ₁ := fun (x) => (a . (≺(𝓐)) . x)
                  let φ₂ := fun (x) => ((f⦅a⦆)  . (≺(𝓑)) . x)
                  let φ₃ := fun (x) => (x . (≼(𝓐)) . b)
                  let φ₄ := fun (x) => (x  . (≼(𝓑)) . (f⦅b⦆))
                  poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (
                    iso_R₁ 𝓐 𝓑 f (And.right (And.right hf)) (And.left hf) (And.left (And.right hf)) a ha x hx
                  ) (
                    iso_R₂ 𝓐 𝓑 f (And.right (And.right hf))  x hx b hb
                  )
                )
          )

theorem poiso_lrc : ∀ 𝓐 𝓑 f a b, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (b ∈ setPO(𝓐)) → (f.[⟦ a ; b ⟧ of 𝓐] = ⟦ f⦅a⦆ ; f⦅b⦆ ⟧ of 𝓑) :=
  fun (𝓐 𝓑 f a b) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      fun (ha) =>
        fun (hb) =>
          let φ := fun (𝓐) => fun (a) => fun (b) => fun (x) => (x ∈ setPO(𝓐)) ∧ ((a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b))
          let ψ := fun (𝓐) => fun (a) => fun (b) =>  ⟦ a ; b ⟧ of 𝓐

          poiso_interv_eq a b φ ψ 𝓐 𝓑 f hf (
            fun (𝓧 x a b) =>
              spec_is_spec (fun (m) => (a . (≼(𝓧)) . m) ∧ (m . (≼(𝓧)) . b)) (setPO(𝓧)) x
          ) (lrc_sub_all) (
            fun (x) =>
              fun (hx : (x ∈ setPO(𝓐))) =>
                let φ₁ := fun (x) => (x ∈ setPO(𝓐))
                let φ₂ := fun (x) => (x ∈ setPO(𝓑))
                let φ₃ := fun (x) => (a . (≼(𝓐)) . x) ∧ (x . (≼(𝓐)) . b)
                let φ₄ := fun (x) => ((f⦅a⦆) . (≼(𝓑)) . x) ∧ (x . (≼(𝓑)) . (f⦅b⦆ ))
                poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx) (
                  let φ₁ := fun (x) => (a . (≼(𝓐)) . x)
                  let φ₂ := fun (x) => ((f⦅a⦆)  . (≼(𝓑)) . x)
                  let φ₃ := fun (x) => (x . (≼(𝓐)) . b)
                  let φ₄ := fun (x) => (x  . (≼(𝓑)) . (f⦅b⦆))
                  poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (
                    iso_R₂ 𝓐 𝓑 f (And.right (And.right hf))  a ha x hx
                  ) (
                    iso_R₂ 𝓐 𝓑 f (And.right (And.right hf))  x hx b hb
                  )
                )
          )

theorem poiso_lc : ∀ 𝓐 𝓑 f a, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (f.[⟦ a ; +∞ ⦘ of 𝓐] = ⟦ f⦅a⦆ ; +∞ ⦘ of 𝓑) :=
  fun (𝓐 𝓑 f a) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      fun (ha) =>
        let φ := fun (𝓐) => fun (a) => fun (x) => (x ∈ setPO(𝓐)) ∧ ((a . (≼(𝓐)) . x))
          let ψ := fun (𝓐) => fun (a) => ⟦ a ; +∞ ⦘ of 𝓐

          poiso_interv_eq₂ a φ ψ 𝓐 𝓑 f hf (
            fun (𝓧 x a) =>
              spec_is_spec (fun (m) => (a . (≼(𝓧)) . m)) (setPO(𝓧)) x
          ) (lc_sub_all) (
            fun (x) =>
              fun (hx : (x ∈ setPO(𝓐))) =>
                let φ₁ := fun (x) => (x ∈ setPO(𝓐))
                let φ₂ := fun (x) => (x ∈ setPO(𝓑))
                let φ₃ := fun (x) => (a . (≼(𝓐)) . x)
                let φ₄ := fun (x) => ((f⦅a⦆) . (≼(𝓑)) . x)
                poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx) (
                    iso_R₂ 𝓐 𝓑 f (And.right (And.right hf))  a ha x hx
                )

          )





theorem poiso_rc : ∀ 𝓐 𝓑 f b, (f PO_ISO_PO 𝓐 To 𝓑) → (b ∈ setPO(𝓐)) → (f.[ ⦗ -∞ ; b ⟧ of 𝓐] = ⦗  -∞  ; f⦅b⦆ ⟧ of 𝓑) :=
  fun (𝓐 𝓑 f b) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      fun (hb) =>
        let φ := fun (𝓐) => fun (b) => fun (x) => (x ∈ setPO(𝓐)) ∧ ((x . (≼(𝓐)) . b))
          let ψ := fun (𝓐) => fun (b) => ⦗ -∞ ; b ⟧ of 𝓐

          poiso_interv_eq₂ b φ ψ 𝓐 𝓑 f hf (
            fun (𝓧 x b) =>
              spec_is_spec (fun (m) => (m . (≼(𝓧)) . b)) (setPO(𝓧)) x
          ) (rc_sub_all) (
            fun (x) =>
              fun (hx : (x ∈ setPO(𝓐))) =>
                let φ₁ := fun (x) => (x ∈ setPO(𝓐))
                let φ₂ := fun (x) => (x ∈ setPO(𝓑))
                let φ₃ := fun (x) => (x . (≼(𝓐)) . b)
                let φ₄ := fun (x) => (x . (≼(𝓑)) . (f⦅b⦆))
                poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx) (
                    iso_R₂ 𝓐 𝓑 f (And.right (And.right hf)) x hx b hb
                )

          )

theorem poiso_lo : ∀ 𝓐 𝓑 f a, (f PO_ISO_PO 𝓐 To 𝓑) → (a ∈ setPO(𝓐)) → (f.[ ⦗  a ; +∞ ⦘ of 𝓐] = ⦗ f⦅a⦆ ; +∞ ⦘ of 𝓑) :=
  fun (𝓐 𝓑 f a) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      fun (ha) =>
        let φ := fun (𝓐) => fun (a) => fun (x) => (x ∈ setPO(𝓐)) ∧ ((a . (≺(𝓐)) . x))
          let ψ := fun (𝓐) => fun (a) => ⦗ a ; +∞ ⦘ of 𝓐

          poiso_interv_eq₂ a φ ψ 𝓐 𝓑 f hf (
            fun (𝓧 x a) =>
              spec_is_spec (fun (m) => (a . (≺(𝓧)) . m)) (setPO(𝓧)) x
          ) (lo_sub_all) (
            fun (x) =>
              fun (hx : (x ∈ setPO(𝓐))) =>
                let φ₁ := fun (x) => (x ∈ setPO(𝓐))
                let φ₂ := fun (x) => (x ∈ setPO(𝓑))
                let φ₃ := fun (x) => (a . (≺(𝓐)) . x)
                let φ₄ := fun (x) => ((f⦅a⦆) . (≺(𝓑)) . x)
                poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx) (
                    iso_R₁ 𝓐 𝓑 f (And.right (And.right hf)) (And.left hf) (And.left (And.right hf)) a ha x hx
                )

          )

theorem poiso_ro : ∀ 𝓐 𝓑 f b, (f PO_ISO_PO 𝓐 To 𝓑) → (b ∈ setPO(𝓐)) → (f.[⦗ -∞ ; b ⦘ of 𝓐] = ⦗ -∞ ; f⦅b⦆ ⦘ of 𝓑) :=
  fun (𝓐 𝓑 f b) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      fun (hb) =>
        let φ := fun (𝓐) => fun (b) => fun (x) => (x ∈ setPO(𝓐)) ∧ ((x . (≺(𝓐)) . b))
          let ψ := fun (𝓐) => fun (b) => ⦗ -∞ ; b ⦘ of 𝓐

          poiso_interv_eq₂ b φ ψ 𝓐 𝓑 f hf (
            fun (𝓧 x b) =>
              spec_is_spec (fun (m) => (m . (≺(𝓧)) . b)) (setPO(𝓧)) x
          ) (ro_sub_all) (
            fun (x) =>
              fun (hx : (x ∈ setPO(𝓐))) =>
                let φ₁ := fun (x) => (x ∈ setPO(𝓐))
                let φ₂ := fun (x) => (x ∈ setPO(𝓑))
                let φ₃ := fun (x) => (x . (≺(𝓐)) . b)
                let φ₄ := fun (x) => (x . (≺(𝓑)) . (f⦅b⦆))
                poiso_and_equiv φ₁ φ₂ φ₃ φ₄ f x (iso_in₁ 𝓐 𝓑 f x (And.right (And.right hf)) hx) (
                    iso_R₁ 𝓐 𝓑 f (And.right (And.right hf)) (And.left hf) (And.left (And.right hf)) x hx b hb
                )

          )

theorem poiso_full : ∀ 𝓐 𝓑 f, (f PO_ISO_PO 𝓐 To 𝓑) → (f.[⦗ -∞ ; +∞  ⦘ of 𝓐] = ⦗ -∞ ; +∞  ⦘ of 𝓑) :=
  fun (𝓐 𝓑 f) =>
    fun (hf) =>
      let hff := And.right (And.right hf)
      let hbij := And.left hff
      let hfunc := And.left hbij
      let hpfunc := And.left hfunc
      let hbinrel := And.left hpfunc
      let hbrel := And.left (prop_then_binary_relation (setPO(𝓐)) (setPO(𝓑)) f hbinrel)
      eq_subst (fun (t) => f.[t] = ⦗ -∞ ; +∞  ⦘ of 𝓑) (⦗ -∞ ; +∞  ⦘ of 𝓐) (setPO(𝓐)) (f_eq_all 𝓐) (
        eq_subst (fun (t) => f.[setPO(𝓐)] = t) (⦗ -∞ ; +∞  ⦘ of 𝓑) (setPO(𝓑)) (f_eq_all 𝓑) (
          let u₂ := Iff.mp (func_surj_crit setPO(𝓐) setPO(𝓑) f hfunc) (And.intro hfunc (And.right (And.right hbij)))
          let u₃ := rng_is_rel_image f hbrel
          let u₄ := Eq.trans (Eq.symm u₃) u₂
          let u₅ := dom_function f setPO(𝓐) setPO(𝓑) hfunc
          eq_subst (fun (m) => f.[m] = setPO(𝓑)) (dom f) (setPO(𝓐)) (Eq.symm u₅) (u₄)

        )
      )



theorem poiso_elconstr  (φ : Set → Set → Set → Prop ) (ψ : Set → Set → Set) (cond : Set → Set → Prop)  :
∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) →
(cond 𝓐 X) →
(cond 𝓑 (f.[X])) →
(f PO_ISO_PO 𝓐 To 𝓑) →
(∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (PartOrd 𝓧) → (cond 𝓧 X) → ψ 𝓧 X ∈ setPO(𝓧)) →
(∀ 𝓧 X t, (PartOrd 𝓧) → (cond 𝓧 X) →  ((φ 𝓧 X (t) ↔ (t = ψ 𝓧 X)))) →
(∀ X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆)))) →
(f⦅ψ 𝓐 X⦆ = ψ 𝓑 (f.[X])) :=

fun (𝓐 𝓑 f X) =>
  fun (hX : (X ⊆ setPO(𝓐))) =>
    fun (hcondX) =>
      fun (hcondfX) =>
        fun (hf) =>
          fun (hin : ∀ 𝓧 X, (X ⊆ setPO(𝓧)) → (PartOrd 𝓧) → (cond 𝓧 X) → ψ 𝓧 X ∈ setPO(𝓧)) =>
            fun (hφψ : (∀ 𝓧 X t, (PartOrd 𝓧) → (cond 𝓧 X) →  ((φ 𝓧 X (t) ↔ (t = ψ 𝓧 X))))) =>
              fun (h𝓐𝓑 : (∀ X x, (X ⊆ setPO(𝓐)) →
              (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X x) ↔ (φ 𝓑 (f.[X]) (f⦅x⦆))))) =>
                let el := ψ 𝓐 X
                let elA := hin 𝓐 X hX (And.left hf) hcondX
                let u₁ := Iff.mpr (hφψ 𝓐 X el (And.left hf) hcondX) (Eq.refl el)
                let u₂ := Iff.mp (h𝓐𝓑 X el hX elA hf) u₁
                Iff.mp (hφψ 𝓑 (f.[X]) (f⦅el⦆) (And.left (And.right hf)) (hcondfX)) u₂


theorem poiso_minumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 MinExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Min X⦆ = 𝓑 Min (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hXexi : (𝓐 MinExi X)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ := fun (𝓐) => fun (X) => fun(x) => is_minimum 𝓐 X x
          let ψ := fun (𝓐) => fun (X) => 𝓐 Min X
          let cond := fun (𝓐) => fun (X) => 𝓐 MinExi X
          let u := fun (𝓧) =>
                      fun (Y) =>
                        fun (hY : Y ⊆ setPO(𝓧)) =>
                          fun (h𝓧 : PartOrd 𝓧) =>
                            fun (hYexi : 𝓧 MinExi Y) =>
                              let v₁ := And.left (min_po_prop 𝓧 Y h𝓧 hYexi)
                              let v := hY (ψ 𝓧 Y) v₁
                              v
          let hfXexi := Iff.mp (poiso_minexi 𝓐 𝓑 f X hX hf) hXexi
          poiso_elconstr φ ψ cond 𝓐 𝓑 f X hX hXexi hfXexi hf (u) (min_po_crit) (poiso_minum 𝓐 𝓑 f)



theorem poiso_maxumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 MaxExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Max X⦆ = 𝓑 Max (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hXexi : (𝓐 MaxExi X)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ := fun (𝓐) => fun (X) => fun(x) => is_maximum 𝓐 X x
          let ψ := fun (𝓐) => fun (X) => 𝓐 Max X
          let cond := fun (𝓐) => fun (X) => 𝓐 MaxExi X
          let u := fun (𝓧) =>
                      fun (Y) =>
                        fun (hY : Y ⊆ setPO(𝓧)) =>
                          fun (h𝓧 : PartOrd 𝓧) =>
                            fun (hYexi : 𝓧 MaxExi Y) =>
                              let v₁ := And.left (max_po_prop 𝓧 Y h𝓧 hYexi)
                              let v := hY (ψ 𝓧 Y) v₁
                              v
          let hfXexi := Iff.mp (poiso_maxexi 𝓐 𝓑 f X hX hf) hXexi
          poiso_elconstr φ ψ cond 𝓐 𝓑 f X hX hXexi hfXexi hf (u) (max_po_crit) (poiso_maxum 𝓐 𝓑 f)


theorem poiso_supel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 SuprExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Supr X⦆ = 𝓑 Supr (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hXexi : (𝓐 SuprExi X)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ := fun (𝓐) => fun (X) => fun(x) => is_supremum 𝓐 X x
          let ψ := fun (𝓐) => fun (X) => 𝓐 Supr X
          let cond := fun (𝓐) => fun (X) => 𝓐 SuprExi X
          let u := fun (𝓧) =>
                      fun (Y) =>
                        fun (_ : Y ⊆ setPO(𝓧)) =>
                          fun (h𝓧 : PartOrd 𝓧) =>
                            fun (hYexi : 𝓧 SuprExi Y) =>
                              let v₁ := And.left (supr_po_prop 𝓧 Y h𝓧 hYexi)
                              And.left (Iff.mp (upp_bou_set_is_upp_bou 𝓧 Y (ψ 𝓧 Y)) v₁)

          let hfXexi := Iff.mp (poiso_supexi 𝓐 𝓑 f X hX hf) hXexi
          poiso_elconstr φ ψ cond 𝓐 𝓑 f X hX hXexi hfXexi hf (u) (supr_po_crit) (poiso_sup 𝓐 𝓑 f)


theorem poiso_infel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 InfmExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Infm X⦆ = 𝓑 Infm (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hXexi : (𝓐 InfmExi X)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ := fun (𝓐) => fun (X) => fun(x) => is_infimum 𝓐 X x
          let ψ := fun (𝓐) => fun (X) => 𝓐 Infm X
          let cond := fun (𝓐) => fun (X) => 𝓐 InfmExi X
          let u := fun (𝓧) =>
                      fun (Y) =>
                        fun (_ : Y ⊆ setPO(𝓧)) =>
                          fun (h𝓧 : PartOrd 𝓧) =>
                            fun (hYexi : 𝓧 InfmExi Y) =>
                              let v₁ := And.left (inf_po_prop 𝓧 Y h𝓧 hYexi)
                              And.left (Iff.mp (low_bou_set_is_low_bou 𝓧 Y (ψ 𝓧 Y)) v₁)

          let hfXexi := Iff.mp (poiso_infexi 𝓐 𝓑 f X hX hf) hXexi
          poiso_elconstr φ ψ cond 𝓐 𝓑 f X hX hXexi hfXexi hf (u) (infm_po_crit) (poiso_inf 𝓐 𝓑 f)


theorem poiso_if_then_iff (φ : Set → Prop) :
(∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → (φ 𝓐) → (φ 𝓑)) → (∀ 𝓐 𝓑, (𝓐 ≃O 𝓑) → ((φ 𝓐) ↔ (φ 𝓑))) :=
  fun (hprop) =>
    fun (𝓐 𝓑) =>
      fun (h𝓐𝓑) =>
        let symmiso := iso_symm 𝓐 𝓑 h𝓐𝓑
        Iff.intro
        (
          fun (hφ𝓐) =>
            hprop 𝓐 𝓑 h𝓐𝓑 hφ𝓐
        )
        (
          fun (hφ𝓑) =>
            hprop 𝓑 𝓐 (symmiso) hφ𝓑
        )


-- TO DO: prove the following theorems


theorem poiso_latt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((Latt 𝓐) ↔ (Latt 𝓑)) :=
  fun (𝓐 𝓑) =>
    fun (h𝓐𝓑 : 𝓐 P≃O 𝓑) =>
      let po𝓐 := And.left h𝓐𝓑
      let po𝓑 := And.left (And.right h𝓐𝓑)
      let iso := And.right (And.right h𝓐𝓑)

      Exists.elim iso (
        fun (f) =>
          fun (hf) =>
            let hfunc := And.left (And.left hf)
            let φ₃ := (∀ x y ∈ (setPO(𝓐)); (𝓐 SuprExi ({x, y})) ∧ (𝓐 InfmExi ({x, y})))
            let φ₄ := (∀ x y ∈ (setPO(𝓑)); (𝓑 SuprExi ({x, y})) ∧ (𝓑 InfmExi ({x, y})))
            let φ₅ := fun (x) => (∀ y ∈ (setPO(𝓐)); (𝓐 SuprExi ({x, y})) ∧ (𝓐 InfmExi ({x, y})))
            let φ₆ := fun (x) => (∀ y ∈ (setPO(𝓑)); (𝓑 SuprExi ({x, y})) ∧ (𝓑 InfmExi ({x, y})))
            let u : φ₃ ↔ φ₄ := poiso_allin_equiv φ₅ φ₆ 𝓐 𝓑 f hf (
              fun (x) =>
                fun (hx : x ∈ setPO(𝓐)) =>
                  let φ₇ := fun (y) => (𝓐 SuprExi ({x, y})) ∧ (𝓐 InfmExi ({x, y}))
                  let φ₈ := fun (y) => (𝓑 SuprExi ({(f⦅x⦆), y})) ∧ (𝓑 InfmExi ({(f⦅x⦆), y}))

                  poiso_allin_equiv φ₇ φ₈ 𝓐 𝓑 f hf (
                    fun (y) =>
                      fun (hy : y ∈ setPO(𝓐)) =>

                      let φ₉ := fun (y) => (𝓐 SuprExi ({x, y}))
                      let φ₁₀ := fun (y) => (𝓑 SuprExi ({(f⦅x⦆), y}))
                      let φ₁₁ := fun (y) => (𝓐 InfmExi ({x, y}))
                      let φ₁₂ := fun (y) => (𝓑 InfmExi ({(f⦅x⦆), y}))

                      let u₀ := fun (t) =>
                        fun (ht : t ∈ {x, y}) =>
                          Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair x y t) ht)
                          (
                            fun (htx : t = x) =>
                              eq_subst (fun (m) => m ∈ setPO(𝓐)) x t (Eq.symm htx) (hx)
                          )
                          (
                            fun (hty : t = y) =>
                              eq_subst (fun (m) => m ∈ setPO(𝓐)) y t (Eq.symm hty) (hy)
                          )

                      let u₁ := extensionality (f.[{x, y}]) ({(f⦅x⦆), (f⦅y⦆)}) (
                        fun (t) =>
                          Iff.intro
                          (
                            fun (ht : t ∈ (f.[{x, y}])) =>
                              let u := Iff.mp (image_prop f {x, y} t) ht
                              Exists.elim u (
                                fun (s) =>
                                  fun (hs) =>
                                    Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair x y s) (And.left hs))
                                    (
                                      fun (hsx : s = x) =>
                                        let u₁ := And.right hs
                                        let u₂ := eq_subst (fun (m) => (m . f . t)) s x (hsx) u₁
                                        let u₃ := Iff.mp (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) hfunc x t hx) u₂
                                        eq_subst (fun (m) => m ∈ {(f⦅x⦆), (f⦅y⦆)}) (f⦅x⦆) t (Eq.symm u₃) (
                                          left_unordered_pair (f⦅x⦆) (f⦅y⦆)
                                        )
                                    )
                                    (
                                      fun (hsy : s = y) =>
                                        let u₁ := And.right hs
                                        let u₂ := eq_subst (fun (m) => (m . f . t)) s y (hsy) u₁
                                        let u₃ := Iff.mp (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) hfunc y t hy) u₂
                                        eq_subst (fun (m) => m ∈ {(f⦅x⦆), (f⦅y⦆)}) (f⦅y⦆) t (Eq.symm u₃) (
                                          right_unordered_pair (f⦅x⦆) (f⦅y⦆)
                                        )
                                    )
                              )
                          )
                          (
                            fun (ht : t ∈ {(f⦅x⦆), (f⦅y⦆)}) =>

                             Iff.mpr ( image_prop f {x, y} t) (

                              Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair (f⦅x⦆) (f⦅y⦆) t) (ht))
                              (
                                fun (ht : t = (f⦅x⦆)) =>
                                  Exists.intro x (And.intro (left_unordered_pair x y) (
                                    eq_subst (fun (m) => (x, m) ∈ f) (f⦅x⦆) t (Eq.symm ht) (
                                      Iff.mpr (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) hfunc x (f⦅x⦆) hx) (
                                        Eq.refl (f⦅x⦆)
                                      )
                                    )
                                  ))
                              )
                              (
                                fun (ht : t = (f⦅y⦆)) =>
                                  Exists.intro y (And.intro (right_unordered_pair x y) (
                                    eq_subst (fun (m) => (y, m) ∈ f) (f⦅y⦆) t (Eq.symm ht) (
                                      Iff.mpr (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑)) hfunc y (f⦅y⦆) hy) (
                                        Eq.refl (f⦅y⦆)
                                      )
                                    )
                                  ))
                              )




                             )
                          )
                      )

                      poiso_and_equiv φ₉ φ₁₀ φ₁₁ φ₁₂ f y (
                        let u₂ := poiso_supexi 𝓐 𝓑 f {x, y} (u₀) (And.intro (po𝓐) (And.intro po𝓑 hf))

                        eq_subst (fun (t) => (𝓐 SuprExi {x, y}) ↔ (𝓑 SuprExi t)) (f.[{x, y}]) ({(f⦅x⦆), (f⦅y⦆)}) (u₁) (u₂)
                      )
                      (
                        let u₂ := poiso_infexi 𝓐 𝓑 f {x, y} (u₀) (And.intro (po𝓐) (And.intro po𝓑 hf))

                        eq_subst (fun (t) => (𝓐 InfmExi {x, y}) ↔ (𝓑 InfmExi t)) (f.[{x, y}]) ({(f⦅x⦆), (f⦅y⦆)}) (u₁) (u₂)
                      )
                  )
            )

            Iff.intro (
              fun (hφ₁φ₃) =>
                And.intro (po𝓑) (Iff.mp (u) (And.right hφ₁φ₃))
            ) (
              fun (hφ₂φ₄) =>
                And.intro (po𝓐) (Iff.mpr (u) (And.right hφ₂φ₄))
            )
      )


theorem poiso_subset_prop (φ : Set → Set → Prop) :
(∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((φ 𝓐 X) ↔ (φ 𝓑 (f.[X])))) →
(∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((∀ X, (X ⊆ setPO(𝓐)) → (φ 𝓐 X)) ↔ (∀ X, (X ⊆ setPO(𝓑)) → (φ 𝓑 X)))) :=
  fun (hProp) =>
    fun (𝓐 𝓑 hPO) =>
      Exists.elim (And.right (And.right (hPO))) (
        fun (f) =>
          fun (hf) =>
            let hfbij := And.left hf
            let hfunc := And.left hfbij
            let hfinvbij := bijection_inv_mp f (setPO(𝓐)) (setPO(𝓑)) hfbij
            let hfinvfunc := And.left hfinvbij
            let hfinvpfunc := And.left hfinvfunc
            let hiso := And.intro (And.left (hPO)) (And.intro (And.left (And.right hPO)) (hf))
            Iff.intro
            (
              fun (h𝓐X) =>
                fun (X) =>
                  fun (hX : X ⊆ setPO(𝓑)) =>
                    let v₀ := specification_set_subset (fun (b) => ∃ a ∈ X; (a . (f⁻¹) . b)) (rng (f⁻¹))
                    let v₁ := rng_partial_function (f⁻¹) (setPO(𝓑)) (setPO(𝓐)) hfinvpfunc
                    let v₂ := subset_trans (f⁻¹.[X]) (rng (f⁻¹)) (setPO(𝓐)) v₀ v₁
                    let u₀ := h𝓐X (f⁻¹.[X]) (v₂)
                    let u₁ := Iff.mp (hProp 𝓐 𝓑 f (f⁻¹.[X]) (v₂) (hiso)) u₀
                    eq_subst (fun (t) => φ 𝓑 t) (f.[f⁻¹.[X]]) (X) (bijimg_f_finv f (setPO(𝓐)) (setPO(𝓑)) hfbij X hX) (u₁)

            )
            (
              fun (h𝓑X) =>
                fun (X) =>
                  let v₀ := specification_set_subset (fun (b) => ∃ a ∈ X; (a . (f) . b)) (rng (f))
                  let v₁ := rng_partial_function (f) (setPO(𝓐)) (setPO(𝓑)) (And.left hfunc)
                  let v₂ := subset_trans (f.[X]) (rng (f)) (setPO(𝓑)) v₀ v₁
                  fun (hX : X ⊆ setPO(𝓐)) =>
                    Iff.mpr (hProp 𝓐 𝓑 f X hX hiso) (
                      h𝓑X (f.[X]) (v₂)
                    )
            )
      )



theorem poiso_complatt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((CompLatt 𝓐) ↔ (CompLatt 𝓑)) :=
  fun (𝓐 𝓑 hPO) =>
    let φ := fun (𝓐) => fun (X) => 𝓐 SuprExi X
    let u₁ := poiso_subset_prop φ (poiso_supexi) 𝓐 𝓑 hPO
    Iff.intro
    (
      fun (hcomp𝓐) =>
        And.intro (And.left (And.right hPO)) (Iff.mp u₁ (And.right hcomp𝓐))
    )
    (
      fun (hcomp𝓑) =>
        And.intro (And.left hPO) (Iff.mpr u₁ (And.right hcomp𝓑))
    )


theorem poiso_linord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((LinOrd 𝓐) ↔ (LinOrd 𝓑)) :=
  fun (𝓐 𝓑) =>
    fun (h𝓐𝓑 : 𝓐 P≃O 𝓑) =>
      let po𝓐 := And.left h𝓐𝓑
      let po𝓑 := And.left (And.right h𝓐𝓑)
      let iso := And.right (And.right h𝓐𝓑)

      Exists.elim iso (
        fun (f) =>
          fun (hf) =>
            let φ₃ := ∀ x y ∈ (setPO(𝓐)); ((x . (≼(𝓐)) . y) ∨ (y . (≼(𝓐)) . x))
            let φ₄ := ∀ x y ∈ (setPO(𝓑)); ((x . (≼(𝓑)) . y) ∨ (y . (≼(𝓑)) . x))
            let φ₅ := fun (x) => ∀ y ∈ setPO(𝓐); ((x . (≼(𝓐)) . y) ∨ (y . (≼(𝓐)) . x))
            let φ₆ := fun (x) => ∀ y ∈ setPO(𝓑); ((x . (≼(𝓑)) . y) ∨ (y . (≼(𝓑)) . x))

            let u : φ₃ ↔ φ₄ := poiso_allin_equiv φ₅ φ₆ 𝓐 𝓑 f hf (
              fun (x) =>
                fun (hx : x ∈ setPO(𝓐)) =>
                  let φ₇ := fun (y) => (x . (≼(𝓐)) . y) ∨ (y . (≼(𝓐)) . x)
                  let φ₈ := fun (y) => ((f⦅x⦆) . (≼(𝓑)) . y) ∨ (y . (≼(𝓑)) . (f⦅x⦆))

                  poiso_allin_equiv φ₇ φ₈ 𝓐 𝓑 f hf (
                    fun (y) =>
                      fun (hy : y ∈ setPO(𝓐)) =>

                      let φ₉ := fun (y) => (x . (≼(𝓐)) . y)
                      let φ₁₀ := fun (y) => ((f⦅x⦆) . (≼(𝓑)) . y)
                      let φ₁₁ := fun (y) => (y . (≼(𝓐)) . x)
                      let φ₁₂ := fun (y) => (y . (≼(𝓑)) . (f⦅x⦆))

                      poiso_or_equiv φ₉ φ₁₀ φ₁₁ φ₁₂ f y (
                        iso_R₂ 𝓐 𝓑 f hf x hx y hy
                      ) (
                        iso_R₂ 𝓐 𝓑 f hf y hy x hx
                      )

                  )
            )

            Iff.intro (
              fun (hφ₁φ₃) =>
                And.intro (po𝓑) (Iff.mp (u) (And.right hφ₁φ₃))
            ) (
              fun (hφ₂φ₄) =>
                And.intro (po𝓐) (Iff.mpr (u) (And.right hφ₂φ₄))
            )
      )





theorem poiso_welord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((WellOrd 𝓐) ↔ (WellOrd 𝓑)) :=
  fun (𝓐 𝓑 hPO) =>
    let φ := fun (𝓐) => fun (X) => (X ≠ ∅) → 𝓐 MinExi X

    let u₀ := fun (𝓐 𝓑 f X) =>
                fun (hX : X ⊆ setPO(𝓐)) =>
                    fun (hf : f PO_ISO_PO 𝓐 To 𝓑) =>
                      let hiso := And.right (And.right hf)
                      let hbij := And.left hiso
                      let hfunc := And.left hbij
                      Iff.intro
                      (
                        fun (h𝓐 : (X ≠ ∅) → (𝓐 MinExi X)) =>
                          fun (hfX : f.[X] ≠ ∅) =>
                            Iff.mp (poiso_minexi 𝓐 𝓑 f X hX hf) (
                              h𝓐 (Iff.mpr (set_non_empty_iff_non_empty X) (
                                let u₁ := Iff.mp (set_non_empty_iff_non_empty (f.[X])) hfX
                                Exists.elim u₁ (
                                  fun (y) =>
                                    fun (hy) =>
                                      let u₂ := Iff.mp (image_prop f X y) hy
                                      Exists.elim u₂ (
                                        fun (x) =>
                                          fun (hx) =>
                                            Exists.intro x (And.left hx)
                                      )
                                )
                              ))
                            )
                      )
                      (
                        fun (h𝓑 : (f.[X] ≠ ∅) → (𝓑 MinExi (f.[X]))) =>
                          fun (hXemp : (X ≠ ∅)) =>
                            Iff.mpr (poiso_minexi 𝓐 𝓑 f X hX hf) (
                              h𝓑 (
                                Iff.mpr (set_non_empty_iff_non_empty (f.[X])) (
                                  let u₂ := Iff.mp (set_non_empty_iff_non_empty X) hXemp

                                  Exists.elim u₂ (
                                    fun (y) =>
                                      fun (hy) =>
                                        Exists.intro ((f⦅y⦆)) (
                                          Iff.mpr (image_prop f X (f⦅y⦆)) (
                                            Exists.intro y (
                                              And.intro (hy) (
                                                Iff.mpr (function_equal_value_prop f (setPO(𝓐)) (setPO(𝓑))
                                                (hfunc) y (f⦅y⦆) (hX y hy)) (
                                                  Eq.refl (f⦅y⦆)
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

    let u₁ := poiso_subset_prop φ (u₀) 𝓐 𝓑 hPO
    Iff.intro
    (
      fun (hWell𝓐) =>
        And.intro (Iff.mp (poiso_linord 𝓐 𝓑 hPO) (And.left hWell𝓐)) (
          Iff.mp (u₁) (And.right hWell𝓐)
        )
    )
    (
      fun (hWell𝓑) =>
        And.intro (Iff.mpr (poiso_linord 𝓐 𝓑 hPO) (And.left hWell𝓑)) (
          Iff.mpr (u₁) (And.right hWell𝓑)
        )
    )


theorem poiso_inv : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((inv_PO 𝓐) P≃O (inv_PO 𝓑)) :=
  fun (𝓐 𝓑 hPO) =>
    Exists.elim (And.right (And.right (hPO))) (
      fun (f) =>
        fun (hf) =>
          let u₀ := And.left hf
          And.intro (inv_is_PO 𝓐 (And.left hPO)) (And.intro (
            inv_is_PO 𝓑 (And.left (And.right hPO))
          ) (
            let u₁ := setPO_is_setPO setPO(𝓐) ≻(𝓐) ≽(𝓐)
            let u₂ := setPO_is_setPO setPO(𝓑) ≻(𝓑) ≽(𝓑)
            Exists.intro f (
              And.intro (
                eq_subst (fun (t) => (f Bij (setPO(inv_PO 𝓐)) To t)) (setPO(𝓑)) (setPO(inv_PO 𝓑)) (Eq.symm u₂) (
                  eq_subst (fun (s) => (f Bij s To setPO(𝓑))) (setPO(𝓐)) (setPO(inv_PO 𝓐)) (Eq.symm u₁) (
                    u₀
                  )
                )
              ) (
                fun (x hx y hy) =>
                    let hx₁ := eq_subst (fun (t) => x ∈ t) (setPO(inv_PO 𝓐)) (setPO(𝓐)) (u₁) hx
                    let hy₁ := eq_subst (fun (t) => y ∈ t) (setPO(inv_PO 𝓐)) (setPO(𝓐)) (u₁) hy
                    let u₃ := And.right hf y hy₁ x hx₁
                    let u₄ := po_lesseq_moreeq 𝓐 (And.left hPO) y x
                    let u₅ := po_lesseq_moreeq 𝓑 (And.left (And.right hPO)) (f⦅y⦆) (f⦅x⦆)
                    let v₀ := lesseqPO_is_lesseqPO setPO(𝓐) ≻(𝓐) ≽(𝓐)
                    let v₀₀ := lesseqPO_is_lesseqPO setPO(𝓑) ≻(𝓑) ≽(𝓑)
                    Iff.intro
                    (
                      fun (hxy) =>

                        let v₁ := eq_subst (fun (t) => (x, y) ∈ t) (≼(inv_PO 𝓐)) (≽(𝓐)) (v₀) (hxy)
                        let v₂ := Iff.mpr u₄ v₁
                        let v₃ := Iff.mp u₃ v₂
                        let v₄ := Iff.mp u₅ v₃
                        eq_subst (fun (t) => ((f⦅x⦆), (f⦅y⦆)) ∈ t) (≽(𝓑)) (≼(inv_PO 𝓑)) (Eq.symm v₀₀) (v₄)
                    )
                    (
                      fun (hfxy) =>
                        let v₁ := eq_subst (fun (t) => ((f⦅x⦆), (f⦅y⦆)) ∈ t) (≼(inv_PO 𝓑)) (≽(𝓑)) (v₀₀) (hfxy)
                        let v₂ := Iff.mpr u₅ v₁
                        let v₃ := Iff.mpr u₃ v₂
                        let v₄ := Iff.mp u₄ v₃
                        eq_subst (fun (t) => ((x), (y)) ∈ t) (≽(𝓐)) (≼(inv_PO 𝓐)) (Eq.symm v₀) (v₄)
                    )
              )
            )
          ))
    )


theorem poiso_subs : ∀ 𝓐 𝓑 f X, (X ≠ ∅) → (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 SubsPO X) P≃O (𝓑 SubsPO (f.[X]))) :=
  fun (𝓐 𝓑 f X hempX hX) =>
    fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
      let hiso := And.right (And.right hf)
      let hbij := And.left hiso
      let hfunc := And.left hbij
      let A := setPO(𝓐)
      let B := setPO(𝓑)
      let u₁ := Iff.mp (set_non_empty_iff_non_empty X) hempX
      Exists.elim u₁ (
        fun (x) =>
          fun (hx) =>
            let u₂ := Iff.mpr (image_prop f X (f⦅x⦆)) (
              Exists.intro x (And.intro (hx) (function_value_pick_property f A B x (hX x hx) (And.left hbij)))
            )

            let u₃ := Iff.mpr (set_non_empty_iff_non_empty (f.[X])) (
              Exists.intro (f⦅x⦆) (u₂)
            )

            let v₀ := specification_set_subset (fun (b) => ∃ a ∈ X; (a . (f) . b)) (rng (f))
            let v₁ := rng_partial_function (f) (setPO(𝓐)) (setPO(𝓑)) (And.left hfunc)
            let v₂ := subset_trans (f.[X]) (rng (f)) (setPO(𝓑)) v₀ v₁
            let v₃ := setPO_is_setPO X (≺(𝓐) spec X) (≼(𝓐) spec X)
            let v₄ := setPO_is_setPO (f.[X]) (≺(𝓑) spec (f.[X])) (≼(𝓑) spec (f.[X]))
            let v₄₁ := lesseqPO_is_lesseqPO X (≺(𝓐) spec X) (≼(𝓐) spec X)
            let v₄₂ := lesseqPO_is_lesseqPO (f.[X]) (≺(𝓑) spec (f.[X])) (≼(𝓑) spec (f.[X]))

            And.intro (sub_is_PO 𝓐 X hempX (And.left hf) hX) (
              And.intro (sub_is_PO 𝓑 (f.[X]) u₃ (And.left (And.right hf)) (v₂)) (
                Exists.intro (f ⨡ X) (
                  And.intro (

                    eq_subst (fun (t) => (f ⨡ X) Bij t To setPO(𝓑 SubsPO (f.[X]))) (X) (setPO(𝓐 SubsPO X)) (Eq.symm v₃) (
                      eq_subst (fun (t₂) => (f ⨡ X) Bij X To t₂) (f.[X]) (setPO(𝓑 SubsPO (f.[X]))) (Eq.symm v₄) (
                        equinum_image_f A B X f hX (And.intro (hfunc) (And.left (And.right hbij)))
                      )
                    )

                  ) (
                    fun (x) =>
                      fun (hx) =>
                        fun (y) =>
                          fun (hy) =>
                            let hx₁ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 SubsPO X)) X (v₃) (hx)
                            let hy₁ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 SubsPO X)) (X) (v₃) (hy)
                            let hx₂ := hX x hx₁
                            let hy₂ := hX y hy₁

                            Iff.intro
                            (
                              fun (hxy) =>
                                let v₅ := eq_subst (fun (t) => (x, y) ∈ t) (≼(𝓐 SubsPO X)) (≼(𝓐) spec X) (v₄₁) (hxy)
                                let v₆ := interset2sets_subset_prop (≼(𝓐)) (X × X)
                                let v₇ := And.left v₆ (x, y) v₅
                                let v₈ := Iff.mp (And.right hiso x hx₂ y hy₂) v₇
                                let v₉ := fun_restriction_val A B X f hX hfunc x hx₁
                                let v₁₀ := fun_restriction_val A B X f hX hfunc y hy₁
                                let v₁₁ := eq_subst (fun (t) => (t, ((f ⨡ X)⦅y⦆)) ∈ (≼(𝓑))) (f⦅x⦆) ((f ⨡ X)⦅x⦆) (v₉) (
                                  eq_subst (fun (t) => ((f⦅x⦆), t) ∈ (≼(𝓑)) ) (f⦅y⦆) ((f ⨡ X)⦅y⦆) (v₁₀) (v₈)
                                )
                                let m := (f ⨡ X)⦅x⦆
                                let n := (f ⨡ X)⦅y⦆

                                let himg₁ := Iff.mpr (image_prop f X (f⦅x⦆)) (
                                  Exists.intro x (And.intro (hx₁) (function_value_pick_property f A B x hx₂ hfunc))
                                )

                                let himg₂ := Iff.mpr (image_prop f X (f⦅y⦆)) (
                                  Exists.intro y (And.intro (hy₁) (function_value_pick_property f A B y hy₂ hfunc))
                                )


                                eq_subst (fun (t) => (m, n) ∈ t) (≼(𝓑) spec (f.[X])) (≼(𝓑 SubsPO (f.[X]))) (Eq.symm v₄₂) (
                                  Iff.mpr (intersect_2sets_prop (≼(𝓑)) (f.[X] × f.[X]) (m, n)) (
                                    And.intro (v₁₁) (
                                      Iff.mpr (cartesian_product_pair_prop (f.[X]) (f.[X]) m n) (
                                        And.intro (
                                          eq_subst (fun (t) => (t) ∈ (f.[X])) (f⦅x⦆) m (v₉) (
                                            himg₁
                                          )
                                        ) (eq_subst (fun (t) => (t) ∈ (f.[X])) (f⦅y⦆) n (v₁₀) (
                                            himg₂
                                          ))
                                      )
                                    )
                                  )
                                )
                            )
                            (
                              fun (hfxy) =>
                                let m := (f ⨡ X)⦅x⦆
                                let n := (f ⨡ X)⦅y⦆
                                let s₁ := eq_subst (fun (t) => (m, n) ∈ t) (≼(𝓑 SubsPO (f.[X]))) (≼(𝓑) spec (f.[X])) (v₄₂) (hfxy)
                                let s₂ := Iff.mp (intersect_2sets_prop (≼(𝓑)) (f.[X] × f.[X]) (m, n)) s₁
                                let s₃ := And.left s₂
                                let s₅ := fun_restriction_val A B X f hX hfunc x hx₁
                                let s₆ := fun_restriction_val A B X f hX hfunc y hy₁
                                let s₇ := eq_subst (fun (t) => (t, (f⦅y⦆)) ∈ ≼(𝓑)) ((f ⨡ X)⦅x⦆) (f⦅x⦆) (Eq.symm s₅) (
                                  eq_subst (fun (t) => (((f ⨡ X)⦅x⦆), t) ∈ ≼(𝓑)) ((f ⨡ X)⦅y⦆) (f⦅y⦆) (Eq.symm s₆) (
                                    s₃
                                  )
                                )
                                let s₈ := Iff.mpr (And.right hiso x hx₂ y hy₂) s₇
                                let s₉ := Iff.mpr (intersect_2sets_prop (≼(𝓐)) (X × X) (x, y)) (
                                  And.intro (s₈) (
                                    Iff.mpr (cartesian_product_pair_prop X X x y) (
                                      And.intro (hx₁) (hy₁)
                                    )
                                  )
                                )
                                eq_subst (fun (t) => (x, y) ∈ t) (≼(𝓐) spec X) (≼(𝓐 SubsPO X)) (Eq.symm (v₄₁)) (s₉)
                            )
                  )
                )
              )
            )
      )




theorem poiso_inter : ∀ 𝓐 𝓑 𝓒 𝓓 f, (setPO(𝓐) = setPO(𝓒)) →
(setPO(𝓑) = setPO(𝓓)) → (f PO_ISO_PO 𝓐 To 𝓑) → (f PO_ISO_PO 𝓒 To 𝓓) → (f PO_ISO_PO (𝓐 InterPO 𝓒) To (𝓑 InterPO 𝓓)) :=
  fun (𝓐 𝓑 𝓒 𝓓 f heq₁ heq₂ h𝓐𝓑 h𝓒𝓓) =>
          let u₁ := setPO_is_setPO (setPO(𝓐)) (≺(𝓐) ∩ ≺(𝓒)) (≼(𝓐) ∩ ≼(𝓒))
          let u₂ := setPO_is_setPO (setPO(𝓑)) (≺(𝓑) ∩ ≺(𝓓)) (≼(𝓑) ∩ ≼(𝓓))
          let u₃ := lesseqPO_is_lesseqPO (setPO(𝓐)) (≺(𝓐) ∩ ≺(𝓒)) (≼(𝓐) ∩ ≼(𝓒))
          let u₄ := lesseqPO_is_lesseqPO (setPO(𝓑)) (≺(𝓑) ∩ ≺(𝓓)) (≼(𝓑) ∩ ≼(𝓓))
          let u₀ := And.right (And.right (h𝓐𝓑))
          let u₀₁:= And.right (And.right h𝓒𝓓)
          And.intro (inter_is_PO_PO 𝓐 𝓒 (And.left h𝓐𝓑) (And.left h𝓒𝓓) heq₁) (
            And.intro (inter_is_PO_PO 𝓑 𝓓 (And.left (And.right h𝓐𝓑)) (And.left (And.right h𝓒𝓓)) heq₂) (
              And.intro (

                eq_subst (fun (t) => f Bij t To setPO(𝓑 InterPO 𝓓)) (setPO(𝓐)) (setPO(𝓐 InterPO 𝓒)) (Eq.symm u₁) (
                  eq_subst (fun (s) => f Bij (setPO(𝓐)) To s) (setPO(𝓑)) (setPO(𝓑 InterPO 𝓓)) (Eq.symm u₂) (
                    And.left u₀
                  )
                )

              ) (
                fun (x hx y hy) =>
                  let hx₁ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 InterPO 𝓒)) (setPO(𝓐)) (u₁) (hx)
                  let hx₂ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐)) (setPO(𝓒)) (heq₁) (hx₁)
                  let hy₁ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 InterPO 𝓒)) (setPO(𝓐)) (u₁) (hy)
                  let hy₂ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐)) (setPO(𝓒)) (heq₁) (hy₁)
                  Iff.intro
                  (
                    fun (hxy) =>
                      let u₅ := eq_subst (fun (t) => (x, y) ∈ t) (≼(𝓐 InterPO 𝓒)) (≼(𝓐) ∩ (≼(𝓒))) (u₃) hxy
                      let u₆ := Iff.mp (intersect_2sets_prop (≼(𝓐)) (≼(𝓒)) (x, y)) u₅
                      let u₇ := Iff.mp (And.right u₀ x hx₁ y hy₁) (And.left u₆)
                      let u₈ := Iff.mp (And.right u₀₁ x hx₂ y hy₂) (And.right u₆)

                      eq_subst (fun (t) => ((f⦅x⦆), (f⦅y⦆)) ∈ t) (≼(𝓑) ∩ ≼(𝓓)) (≼(𝓑 InterPO 𝓓)) (Eq.symm u₄) (
                        Iff.mpr (intersect_2sets_prop (≼(𝓑)) (≼(𝓓)) ((f⦅x⦆), (f⦅y⦆)) ) (
                          And.intro (u₇) (u₈)
                        )
                      )
                  )
                  (
                    fun (hfxy) =>
                      let u₅ := eq_subst (fun (t) => ((f⦅x⦆), (f⦅y⦆)) ∈ t) (≼(𝓑 InterPO 𝓓)) (≼(𝓑) ∩ ≼(𝓓)) (u₄) hfxy
                      let u₆ := Iff.mp (intersect_2sets_prop (≼(𝓑)) (≼(𝓓)) ((f⦅x⦆), (f⦅y⦆))) u₅
                      let u₇ := Iff.mpr (And.right u₀ x hx₁ y hy₁) (And.left u₆)
                      let u₈ := Iff.mpr (And.right u₀₁ x hx₂ y hy₂) (And.right u₆)

                      eq_subst (fun (t) => (x, y) ∈ t) (≼(𝓐) ∩ (≼(𝓒))) (≼(𝓐 InterPO 𝓒)) (Eq.symm u₃) (
                        Iff.mpr (intersect_2sets_prop (≼(𝓐)) (≼(𝓒)) (x, y)) (
                          And.intro (u₇) (u₈)
                        )
                      )
                  )
              )
            )
          )




theorem poiso_cart : ∀ 𝓐 𝓑 𝓒 𝓓, (𝓐 P≃O 𝓑) → (𝓒 P≃O 𝓓) → ((𝓐 CartPO 𝓒) P≃O (𝓑 CartPO 𝓓)) :=
  fun (𝓐 𝓑 𝓒 𝓓 h𝓐𝓑 h𝓒𝓓) =>
    let hpo𝓐𝓑 := And.right (And.right h𝓐𝓑)
    let h𝓐 := And.left h𝓐𝓑
    let h𝓑 := And.left (And.right h𝓐𝓑)
    let hpo𝓒𝓓 := And.right (And.right h𝓒𝓓)
    let h𝓒 := And.left h𝓒𝓓
    let h𝓓 := And.left (And.right h𝓒𝓓)
    let A := setPO(𝓐)
    let B := setPO(𝓑)
    let C := setPO(𝓒)
    let D := setPO(𝓓)
    let u₁ := setPO_is_setPO (A × C) (le_cart 𝓐 𝓒) (leq_cart 𝓐 𝓒)
    let u₂ := setPO_is_setPO (B × D) (le_cart 𝓑 𝓓) (leq_cart 𝓑 𝓓)
    let u₁₁ := lesseqPO_is_lesseqPO (A × C) (le_cart 𝓐 𝓒) (leq_cart 𝓐 𝓒)
    let u₂₁ := lesseqPO_is_lesseqPO (B × D) (le_cart 𝓑 𝓓) (leq_cart 𝓑 𝓓)

    Exists.elim hpo𝓐𝓑 (
      fun (f) =>
        fun (hf) =>
          Exists.elim hpo𝓒𝓓 (
            fun (g) =>
              fun (hg) =>
                And.intro (cart_PO_PO 𝓐 𝓒 h𝓐 h𝓒) (And.intro (
                  cart_PO_PO 𝓑 𝓓 h𝓑 h𝓓
                ) (
                  let hf₁ := And.left hf
                  let hf₂ := And.left hf₁
                  let hf₃ := And.intro hf₂ (And.left (And.right hf₁))
                  let hg₁ := And.left hg
                  let hg₂ := And.left hg₁
                  let hg₃ := And.intro hg₂ (And.left (And.right hg₁))
                  let hf₄ := And.right hf
                  let hg₄ := And.right hg
                  let hfinv := bijection_inv_mp f A B hf₁
                  let hginv := bijection_inv_mp g C D hg₁
                  let X := A × C
                  let Y := B × D
                  let P := fun (pr) => (f⦅π₁ pr⦆, g⦅π₂ pr⦆)
                  let h := lam_fun (A × C) (B × D) P
                  let func_prop_all := lam_then_fun_prop (P) X Y (
                      fun (elem) => fun (h₂ : elem ∈ X) =>
                        let h₅ := fst_coor_set A C elem h₂
                        let h₇ := val_in_B f A B hf₂ (π₁ elem) (h₅)
                        let h₀ := snd_coor_set A C elem h₂
                        let h₀₀ := val_in_B g C D hg₂ (π₂ elem) (h₀)
                        Iff.mpr (cartesian_product_pair_prop B D (f⦅π₁ elem⦆) (g⦅π₂ elem⦆)) (
                          And.intro (h₇) (h₀₀)
                        )
                  )
                  let func_prop := And.left func_prop_all
                  let value_prop := And.right func_prop_all
                  let inj_prop := Iff.mpr (func_inj_prop X Y h func_prop) (
                    fun (x hx y hy) =>
                      fun (hxhy) =>
                        let u₃ := value_prop x hx
                        let u₄ := value_prop y hy
                        let u₅ := Eq.trans (Eq.symm u₃) (hxhy)
                        let u₆ := Eq.trans (u₅) (u₄)
                        let u₇ := Iff.mp (ordered_pair_set_prop (f⦅π₁ x⦆) (g⦅π₂ x⦆) (f⦅π₁ y⦆) (g⦅π₂ y⦆)) u₆
                        let u₇₀ := fst_coor_set A C x hx
                        let u₇₁ := fst_coor_set A C y hy
                        let u₇₂ := snd_coor_set A C x hx
                        let u₇₃ := snd_coor_set A C y hy
                        let u₈ := Iff.mp (func_inj_prop A B f hf₂) (hf₃) (π₁ x) u₇₀ (π₁ y) u₇₁ (And.left u₇)
                        let u₉ := Iff.mp (func_inj_prop C D g hg₂) (hg₃) (π₂ x) u₇₂ (π₂ y) (u₇₃) (And.right u₇)
                        equal_fst_snd A C x y hx hy u₈ u₉
                  )
                  let injv_prop := And.right inj_prop
                  let surj_prop := Iff.mpr (func_surj_prop X Y h func_prop) (
                    fun (s hs) =>
                      let lelem := ((f⁻¹)⦅π₁ s⦆)
                      let relem := ((g⁻¹)⦅π₂ s⦆)
                      let elem := ((((f⁻¹)⦅π₁ s⦆)), ((g⁻¹)⦅π₂ s⦆))

                      Exists.intro elem (
                        let u₃ := fst_coor_set B D s hs
                        let u₄ := val_in_B (f⁻¹) B A (And.left hfinv) (π₁ s) u₃
                        let u₅ := snd_coor_set B D s hs
                        let u₆ := val_in_B (g⁻¹) D C (And.left hginv) (π₂ s) u₅
                        let u₇ := Iff.mpr (cartesian_product_pair_prop A C ((f⁻¹)⦅π₁ s⦆) ((g⁻¹)⦅π₂ s⦆)) (
                          And.intro (u₄) (u₆)
                        )
                        And.intro (u₇) (

                          let u₈ := value_prop elem u₇
                          Eq.trans (
                            let u₉ := coordinates_fst_coor lelem relem
                            let u₁₀ := eq_subst (fun (t) => (f⦅π₁ elem⦆) = (f⦅t⦆)) (π₁ elem) (lelem) (u₉) (Eq.refl (f⦅π₁ elem⦆))
                            let u₁₁ := bij_f_finv f A B hf₁ (π₁ s) u₃
                            let u₁₂ := Eq.trans u₁₀ u₁₁
                            let u₁₃ := coordinates_snd_coor lelem relem
                            let u₁₄ := eq_subst (fun (t) => (g⦅π₂ elem⦆) = (g⦅t⦆)) (π₂ elem) (relem) (u₁₃) (Eq.refl (g⦅π₂ elem⦆))
                            let u₁₅ := bij_f_finv g C D hg₁ (π₂ s) u₅
                            let u₁₆ := Eq.trans u₁₄ u₁₅
                            let u₁₇ := Iff.mpr (ordered_pair_set_prop (f⦅π₁ elem⦆) (g⦅π₂ elem⦆) (π₁ s) (π₂ s)) (
                              And.intro (u₁₂) (u₁₆)
                            )
                            let u₁₈ := fst_snd_then_unique B D s hs
                            Eq.trans (u₁₈) (Eq.symm u₁₇)

                          ) (Eq.symm u₈)
                        )
                      )

                  )
                  let surjv_prop := And.right surj_prop
                  Exists.intro h (
                    And.intro (
                      eq_subst (fun (t) => h Bij t To (setPO(𝓑 CartPO 𝓓))) (A × C) (setPO(𝓐 CartPO 𝓒)) (Eq.symm u₁) (
                        eq_subst (fun (t) => h Bij (A × C) To t) (B × D) (setPO(𝓑 CartPO 𝓓)) (Eq.symm u₂) (
                          And.intro (func_prop) (And.intro (injv_prop) (surjv_prop))
                        )
                      )
                    ) (


                      fun (x hx y hy) =>

                        let hx₁ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 CartPO 𝓒)) (A × C) (u₁) hx
                        let hx₁₁ := fst_coor_set A C x hx₁
                        let hx₁₂ := snd_coor_set A C x hx₁
                        let hy₁ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 CartPO 𝓒)) (A × C) (u₁) hy
                        let hy₁₁ := fst_coor_set A C y hy₁
                        let hy₁₂ := snd_coor_set A C y hy₁
                        let hhx := val_in_B h X Y func_prop x hx₁
                        let hhy := val_in_B h X Y func_prop y hy₁
                        let v₃ : (π₁ (P x)) = (f⦅π₁ x⦆) := coordinates_fst_coor (f⦅π₁ x⦆) (g⦅π₂ x⦆)
                        let v₄ := value_prop x hx₁
                        let v₅ := eq_subst (fun (t) => (π₁ t) = (f⦅π₁ x⦆)) (P x) (h⦅x⦆) (Eq.symm v₄) v₃

                        let v₆ : (π₁ (P y)) = (f⦅π₁ y⦆) := coordinates_fst_coor (f⦅π₁ y⦆) (g⦅π₂ y⦆)
                        let v₇ := value_prop y hy₁
                        let v₈ := eq_subst (fun (t) => (π₁ t) = (f⦅π₁ y⦆)) (P y) (h⦅y⦆) (Eq.symm v₇) v₆

                        let v₃₁ : (π₂ (P x)) = (g⦅π₂ x⦆) := coordinates_snd_coor (f⦅π₁ x⦆) (g⦅π₂ x⦆)
                        let v₄₁ := value_prop x hx₁
                        let v₅₁ := eq_subst (fun (t) => (π₂ t) = (g⦅π₂ x⦆)) (P x) (h⦅x⦆) (Eq.symm v₄₁) v₃₁

                        let v₆₁ : (π₂ (P y)) = (g⦅π₂ y⦆) := coordinates_snd_coor (f⦅π₁ y⦆) (g⦅π₂ y⦆)
                        let v₇₁ := value_prop y hy₁
                        let v₈₁ := eq_subst (fun (t) => (π₂ t) = (g⦅π₂ y⦆)) (P y) (h⦅y⦆) (Eq.symm v₇₁) v₆₁

                        Iff.intro
                        (
                          fun (hxy) =>
                            let v₀₀ := eq_subst (fun (t) => (x, y) ∈ t) (≼(𝓐 CartPO 𝓒)) (leq_cart 𝓐 𝓒) (u₁₁) (hxy)
                            let v₀ := Iff.mp (leq_cart_prop 𝓐 𝓒 x hx₁ y hy₁) v₀₀
                            let v₁ := Iff.mp (hf₄ (π₁ x) (hx₁₁) (π₁ y) (hy₁₁)) (And.left v₀)
                            let v₂ := Iff.mp (hg₄ (π₂ x) (hx₁₂) (π₂ y) (hy₁₂)) (And.right v₀)

                            let v₉ := eq_subst (fun (t) => (t, (π₁ (h⦅y⦆))) ∈ (≼(𝓑))) (f⦅π₁ x⦆) (π₁ (h⦅x⦆)) (Eq.symm v₅) (
                              eq_subst (fun (t) => ((f⦅π₁ x⦆), t) ∈ (≼(𝓑))) (f⦅π₁ y⦆) (π₁ (h⦅y⦆)) (Eq.symm v₈) (v₁)
                            )
                            let v₉₁ := eq_subst (fun (t) => (t, (π₂ (h⦅y⦆))) ∈ (≼(𝓓))) (g⦅π₂ x⦆) (π₂ (h⦅x⦆)) (Eq.symm v₅₁) (
                              eq_subst (fun (t) => ((g⦅π₂ x⦆), t) ∈ (≼(𝓓))) (g⦅π₂ y⦆) (π₂ (h⦅y⦆)) (Eq.symm v₈₁) (v₂)
                            )
                            let v := Iff.mpr (leq_cart_prop 𝓑 𝓓 (h⦅x⦆) hhx (h⦅y⦆) hhy) (
                              And.intro (v₉) (v₉₁)
                            )

                            eq_subst (fun (t) => ((h⦅x⦆), (h⦅y⦆)) ∈ t) (leq_cart 𝓑 𝓓) (≼(𝓑 CartPO 𝓓)) (Eq.symm u₂₁) (v)
                        )
                        (
                          fun (hfxy) =>
                            let v₀₀ := eq_subst (fun (t) => ((h⦅x⦆), (h⦅y⦆)) ∈ t) (≼(𝓑 CartPO 𝓓)) (leq_cart 𝓑 𝓓) (u₂₁) (hfxy)
                            let v₀ := Iff.mp (leq_cart_prop 𝓑 𝓓 (h⦅x⦆) hhx (h⦅y⦆) hhy) v₀₀

                            let v₉ := eq_subst (fun (t) => (t, (f⦅π₁ y⦆)) ∈ (≼(𝓑))) (π₁ (h⦅x⦆)) (f⦅π₁ x⦆) (v₅) (
                              eq_subst (fun (t) => ((π₁ (h⦅x⦆)), t) ∈ (≼(𝓑))) (π₁ (h⦅y⦆)) (f⦅π₁ y⦆) v₈ (
                                And.left v₀
                              )
                            )

                            let v₉₁ := eq_subst (fun (t) => (t, (g⦅π₂ y⦆)) ∈ (≼(𝓓))) (π₂ (h⦅x⦆)) (g⦅π₂ x⦆) (v₅₁) (
                              eq_subst (fun (t) => ((π₂ (h⦅x⦆)), t) ∈ (≼(𝓓))) (π₂ (h⦅y⦆)) (g⦅π₂ y⦆) v₈₁ (
                                And.right v₀
                              )
                            )

                            let v₂ := Iff.mpr (hg₄ (π₂ x) (hx₁₂) (π₂ y) (hy₁₂)) v₉₁
                            let v₁ := Iff.mpr (hf₄ (π₁ x) (hx₁₁) (π₁ y) (hy₁₁)) v₉
                            let v₃ := Iff.mpr (leq_cart_prop 𝓐 𝓒 x hx₁ y hy₁) (And.intro (v₁) (v₂))

                            eq_subst (fun (t) => (x, y) ∈ t) (leq_cart 𝓐 𝓒) (≼(𝓐 CartPO 𝓒)) (Eq.symm u₁₁) (v₃)
                        )

                    )
                  )
                ))
          )
    )

noncomputable def induced_R₂ (𝓐 f: Set) := {s ∈ (rng f) × (rng f) | ∃ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∧ s = (f⦅x⦆, f⦅y⦆)}

theorem bij_rng : ∀ f A B, (f Inj A To B) → (f Bij A To (rng f)) :=
  fun (f A B) =>
    fun (hinf) =>
      let hfrngf := function_rng_def f A B (And.left hinf)
      And.intro (hfrngf) (
        And.intro (And.right hinf) (
          fun (y) =>
            fun (hy) =>
              Iff.mp (rng_prop f y) hy
        )
      )


theorem induced_crit₀ : ∀ 𝓐 f, (f Bij (setPO(𝓐)) To (rng f)) → ∀ x y ∈ (setPO(𝓐)); (x . (≼(𝓐)) . y) ↔ ((f⦅x⦆) . (induced_R₂ 𝓐 f) . (f⦅y⦆)) :=
  fun (𝓐 f hf) =>
    fun (x hx y hy) =>
      let P := fun (s) => ∃ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∧ s = (f⦅x⦆, f⦅y⦆)
      let rn := rng f
      let B := (rn) × (rn)
      let fxset := val_in_B f (setPO(𝓐)) rn (And.left hf) x hx
      let fyset := val_in_B f (setPO(𝓐)) rn (And.left hf) y hy
      Iff.intro
      (
        fun (hxy) =>
          Iff.mpr (spec_is_spec P B ((f⦅x⦆), (f⦅y⦆))) (
            And.intro (

              Iff.mpr (cartesian_product_pair_prop rn rn (f⦅x⦆) (f⦅y⦆)) (
                And.intro (fxset) (fyset)
              )

            ) (Exists.intro x (And.intro (hx) (Exists.intro y (And.intro (hy) (
              And.intro (hxy) (Eq.refl ((f⦅x⦆), (f⦅y⦆)))
            )))))
          )
      )
      (
        fun (hfxy) =>
          let u₁ := And.right (Iff.mp (spec_is_spec P B ((f⦅x⦆), (f⦅y⦆))) hfxy)
          Exists.elim u₁ (
            fun (a) =>
              fun (ha) =>
                Exists.elim (And.right ha) (
                  fun (b) =>
                    fun (hb) =>
                      let u₂ := And.right hb
                      let u₃ := And.right u₂
                      let u₄ := Iff.mp (ordered_pair_set_prop (f⦅x⦆) (f⦅y⦆) (f⦅a⦆) (f⦅b⦆)) u₃
                      let u₅ := And.intro (And.left hf) (And.left (And.right hf))
                      let u₆ := Iff.mp (func_inj_prop (setPO(𝓐)) (rng f) f (And.left u₅)) u₅ x hx a (And.left ha) (And.left u₄)
                      let u₇ := Iff.mp (func_inj_prop (setPO(𝓐)) (rng f) f (And.left u₅)) u₅ y hy b (And.left hb) (And.right u₄)
                      let u₈ := eq_subst (fun (t) => (t, b) ∈ (≼(𝓐))) a x (Eq.symm u₆) (And.left u₂)
                      eq_subst (fun (t) => (x, t) ∈ (≼(𝓐))) b y (Eq.symm u₇) (u₈)
                )
          )


      )



theorem induced_crit: ∀ 𝓐 f, (f Bij (setPO(𝓐)) To (rng f)) →  ∀ x y ∈ rng f; (x . (induced_R₂ 𝓐 f) . y) ↔ (((f⁻¹⦅x⦆) . (≼(𝓐)) . (f⁻¹⦅y⦆))) :=
fun (𝓐 f hf) =>
  fun (x hx y hy) =>
    let P := fun (s) => ∃ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∧ s = (f⦅x⦆, f⦅y⦆)
    let rn := rng f
    let B := (rn) × (rn)
    let finvbij := bijection_inv_mp f (setPO(𝓐)) (rng f) hf
    let finvfunc := And.left finvbij
    Iff.intro
    (
      fun (hxy) =>
        let u₁ := Iff.mp (spec_is_spec P B (x, y)) hxy
        Exists.elim (And.right u₁) (
          fun (a) =>
            fun (ha) =>
              Exists.elim (And.right ha) (
                fun (b) =>
                  fun (hb) =>
                    let u₂ := And.right hb
                    let u₃ := And.right u₂
                    let u₄ := Iff.mp (ordered_pair_set_prop x y (f⦅a⦆) (f⦅b⦆)) u₃
                    let u₅ := And.left u₄
                    let u₆ := eq_subst (fun (t) => (f⁻¹⦅x⦆) = (f⁻¹⦅t⦆)) x (f⦅a⦆) (u₅) (Eq.refl (f⁻¹⦅x⦆))
                    let u₇ := bij_finv_f f (setPO(𝓐)) rn hf a (And.left ha)
                    let u₈ := Eq.trans u₆ u₇
                    let u₉ := And.right u₄
                    let u₁₀ := eq_subst (fun (t) => (f⁻¹⦅y⦆) = (f⁻¹⦅t⦆)) y (f⦅b⦆) (u₉) (Eq.refl (f⁻¹⦅y⦆))
                    let u₁₁ := bij_finv_f f (setPO(𝓐)) rn hf b (And.left hb)
                    let u₁₂ := Eq.trans u₁₀ u₁₁

                    let u₁₃ := And.left u₂
                    let u₁₄ := eq_subst (fun (t) => (t, b) ∈ (≼(𝓐))) (a) (f⁻¹⦅x⦆) (Eq.symm u₈) (u₁₃)
                    eq_subst (fun (t) => ((f⁻¹⦅x⦆), t) ∈ (≼(𝓐))) (b) (f⁻¹⦅y⦆) (Eq.symm u₁₂) (u₁₄)
              )
        )

    )
    (
      fun (hfxy) =>
        let u₁ := Iff.mpr (cartesian_product_pair_prop rn rn x y) (And.intro (hx) (hy))
        let u₂ := val_in_B (f⁻¹) (rn) (setPO(𝓐)) finvfunc x hx
        let u₃ := val_in_B (f⁻¹) (rn) (setPO(𝓐)) finvfunc y hy

        Iff.mpr (spec_is_spec P B (x, y)) (

          And.intro (u₁) (
            Exists.intro (f⁻¹⦅x⦆) (
              And.intro (u₂) (Exists.intro (f⁻¹⦅y⦆) (

                And.intro (u₃) (
                  And.intro (hfxy) (
                    Iff.mpr (ordered_pair_set_prop x y (f⦅f⁻¹⦅x⦆⦆) (f⦅f⁻¹⦅y⦆⦆)) (
                      And.intro (Eq.symm (bij_f_finv f (setPO(𝓐)) (rng f) (hf) x (hx))) (
                        Eq.symm (bij_f_finv f (setPO(𝓐)) (rng f) (hf) y (hy))
                      )
                    )
                  )

                )
              ))
            )
          )
        )
    )



noncomputable def induced_order (𝓐 f: Set) := ⁅rng f; str (rng f) (induced_R₂ 𝓐 f); (induced_R₂ 𝓐 f)⁆

theorem po_induced : ∀ 𝓐 f X, (f Inj (setPO(𝓐)) To X) → (PartOrd 𝓐) → (PartOrd (induced_order 𝓐 f)) :=
  fun (𝓐 f X) =>
    fun (hf) =>
      fun (h𝓐) =>
        let B := rng f
        let R₂ := (induced_R₂ 𝓐 f)
        let R₁ := str B R₂

        let 𝓑 := ⁅B; R₁; R₂⁆
        let P := fun (s) => ∃ x y ∈ setPO(𝓐); (x . (≼(𝓐)) . y) ∧ s = (f⦅x⦆, f⦅y⦆)

        let 𝓐nemp := po_emp 𝓐 h𝓐
        let 𝓐exi := Iff.mp (set_non_empty_iff_non_empty (setPO(𝓐))) 𝓐nemp
        let rngExi : ∃ y, y ∈ (rng f) := Exists.elim 𝓐exi (
          fun (x) =>
            fun (hx) =>
              Exists.intro (f⦅x⦆) (
                let u₁ := Iff.mpr (function_equal_value_prop f (setPO(𝓐)) X (And.left hf) x (f⦅x⦆) hx) (Eq.refl (f⦅x⦆))

                Iff.mpr (rng_prop f (f⦅x⦆)) (Exists.intro x (u₁))
              )
        )
        let rngnemp := Iff.mpr (set_non_empty_iff_non_empty (rng f)) rngExi
        let R₂bin := specification_set_subset P (B × B)
        let fbij := bij_rng f (setPO(𝓐)) X hf
        let finvbij := bijection_inv_mp f (setPO(𝓐)) (rng f) fbij
        let finvfunc := And.left finvbij
        let finvset := val_in_B (f⁻¹) (rng f) (setPO(𝓐)) finvfunc

        Exists.intro B (
          Exists.intro R₁ (
            Exists.intro R₂ (
              And.intro (Eq.refl 𝓑) (
                Iff.mpr (part_ord_nspo_crit B R₁ R₂) (
                  And.intro (rngnemp) (
                    And.intro (

                      And.intro (R₂bin) (


                        And.intro (

                          fun (x) =>
                            fun (hx) =>
                              Iff.mpr (induced_crit 𝓐 f fbij x hx x hx) (
                                refl_R₂ 𝓐 h𝓐 (f⁻¹⦅x⦆) (finvset x (hx))
                              )

                        ) (And.intro (

                          fun (x) =>
                            fun (y) =>
                              fun (hxy) =>
                                let R₂B := R₂bin (x, y) (And.left hxy)
                                let cart := Iff.mp (cartesian_product_pair_prop B B x y) R₂B
                                let u₀ := (Iff.mp (induced_crit 𝓐 f fbij x (And.left cart) y (And.right cart)) (And.left hxy))
                                let u₁ := (Iff.mp (induced_crit 𝓐 f fbij y (And.right cart) x (And.left cart)) (And.right hxy))
                                let u₂ := antisymm_R₂ 𝓐 h𝓐 (f⁻¹⦅x⦆) (f⁻¹⦅y⦆) (u₀) (u₁)
                                let u₃ := And.intro (finvfunc) (And.left (And.right finvbij))
                                Iff.mp (func_inj_prop (rng f) (setPO(𝓐)) (f⁻¹) finvfunc) u₃ x (
                                  And.left cart) y (And.right cart) u₂


                        ) (
                          fun (x) =>
                            fun (y) =>
                              fun (z) =>
                                fun (hxyz) =>
                                  let R₂B₁ := R₂bin (x, y) (And.left hxyz)
                                  let cart₁ := Iff.mp (cartesian_product_pair_prop B B x y) R₂B₁
                                  let R₂B₂ := R₂bin (y, z) (And.right hxyz)
                                  let cart₂ := Iff.mp (cartesian_product_pair_prop B B y z) R₂B₂
                                  Iff.mpr (induced_crit 𝓐 f fbij x (And.left cart₁) z (And.right cart₂)) (
                                    trans_R₂ 𝓐 h𝓐 (f⁻¹⦅x⦆) (f⁻¹⦅y⦆) (f⁻¹⦅z⦆) (
                                      Iff.mp (induced_crit 𝓐 f fbij x (And.left cart₁) y (And.right cart₁)) (
                                        And.left hxyz
                                      )
                                    ) (Iff.mp (induced_crit 𝓐 f fbij y (And.left cart₂) z (And.right cart₂)) (
                                        And.right hxyz
                                      ))
                                  )
                        ))
                      )

                    ) (Eq.refl R₁)
                  )
                )
              )
            )
          )
        )


theorem poiso_induced : ∀ 𝓐 f X, (PartOrd 𝓐) → (f Inj (setPO(𝓐)) To X) → (f PO_ISO_PO 𝓐 To (induced_order 𝓐 f)) :=
  fun (𝓐 f X h𝓐 hf) =>
    And.intro (h𝓐) (
      And.intro (po_induced 𝓐 f X hf h𝓐) (
        let B := rng f
        let R₂ := induced_R₂ 𝓐 f
        let R₁ := str B R₂
        let u₁ := setPO_is_setPO B R₁ R₂
        let u₂ := lesseqPO_is_lesseqPO B R₁ R₂
        let fbij := bij_rng f (setPO(𝓐)) (X) (hf)
        And.intro (
          eq_subst (fun (t) => f Bij (setPO(𝓐)) To t) (B) (setPO(induced_order 𝓐 f)) (Eq.symm u₁) (
            fbij
          )
        ) (
          let u₃ := induced_crit₀ 𝓐 f fbij

          eq_subst (fun (t) => ∀ x y ∈ (setPO(𝓐)); (x . (≼(𝓐)) . y) ↔ ((f⦅x⦆) . (t) . (f⦅y⦆))) (induced_R₂ 𝓐 f) (≼(induced_order 𝓐 f)) (
            Eq.symm u₂) (u₃)
        )
      )
    )
