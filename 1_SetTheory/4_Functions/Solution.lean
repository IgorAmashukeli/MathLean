import «Header»

noncomputable def is_functional (R : Set) : Prop := ∀ x y z, (x . R . y) → (x . R . z) → y = z
noncomputable def is_total (R X : Set) : Prop := ∀ x ∈ X; ∃ y, (x . R . y)
noncomputable def is_injective (R : Set) : Prop := ∀ x y z, (x . R . z) → (y . R . z) → x = y
noncomputable def is_surjective (R Y : Set) : Prop := ∀ y ∈ Y; ∃ x, (x . R . y)

noncomputable def rel_is_functional (R : Set) : Prop := binary_relation R ∧ is_functional R
noncomputable def rel_is_total (R X : Set) : Prop := binary_relation R ∧ is_total R X
noncomputable def rel_is_injective (R : Set) : Prop := binary_relation R ∧ is_injective R
noncomputable def rel_is_surjective (R Y : Set) : Prop := binary_relation R ∧ is_surjective R Y


theorem func_inv_inj : ∀ R, binary_relation R → (is_functional R ↔ is_injective (R⁻¹)) :=
  fun (R) => fun (h : binary_relation R) =>
    let _ := inv_is_rel R h
    Iff.intro
    (
      fun (h₁ : is_functional R) =>
        fun (x y z) =>  fun (s : (x . (R⁻¹) . z)) => fun (t : (y . (R⁻¹) . z)) =>
          h₁ z x y (Iff.mpr (inv_pair_prop R h z x) (s)) (Iff.mpr (inv_pair_prop R h z y) (t))
    )
    (
      fun (h₁ : is_injective (R⁻¹)) =>
        fun (x y z) => fun (s : (x . R . y)) => fun (t : (x . R . z)) =>
          h₁ y z x (Iff.mp (inv_pair_prop R h x y) (s)) (Iff.mp (inv_pair_prop R h x z) (t))
    )


theorem inj_inv_func : ∀ R, binary_relation R → (is_injective R ↔ is_functional (R⁻¹)) :=
  fun (R) => fun (h : binary_relation R) =>
    Iff.intro
    (
      fun (h₁ : is_injective R) =>
        Iff.mpr (func_inv_inj (R⁻¹) (inv_is_rel R (h))) (eq_subst (fun (u) => is_injective u) (R) ((R⁻¹)⁻¹) (Eq.symm (inv_prop R h)) (h₁) )
    )
    (
      fun (h₂ : is_functional (R⁻¹)) =>
        let first := Iff.mp (func_inv_inj (R⁻¹) (inv_is_rel R h)) (h₂)
        eq_subst (fun (u) => is_injective u) ((R⁻¹)⁻¹) (R) (inv_prop R h) (first)
    )




theorem tot_inv_surj : ∀ R X, binary_relation R → ((is_total R X) ↔ (is_surjective (R⁻¹) X)) :=
  fun (R) => fun (X) => fun (h : binary_relation R) =>
    Iff.intro
    (
      fun (h₁ : is_total R X) =>
        fun (x) =>
          fun (s : x ∈ X) =>
            Exists.elim (h₁ x s) (
              fun (w) =>
                fun (hw : (x . R . w)) =>
                  Exists.intro w (Iff.mp (inv_pair_prop R h x w) (hw))
            )

    )
    (
      fun (h₂ : is_surjective (R⁻¹) X) =>
        fun (x) =>
          fun (s : x ∈ X) =>
            Exists.elim (h₂ x s) (
              fun (w) =>
                fun (hw : (w, x) ∈ (R⁻¹)) =>
                  Exists.intro w (Iff.mpr (inv_pair_prop R h x w) (hw))
            )
    )




theorem surj_inv_tot : ∀ R X, binary_relation R → ((is_surjective R X) ↔ (is_total (R⁻¹) X)) :=
  fun (R) => fun (X) => fun (h : binary_relation R) =>
    Iff.intro
    (
      fun (h₁ : is_surjective R X) =>
        fun (x) =>
          fun (s : x ∈ X) =>
            Exists.elim (h₁ x s) (
              fun (w) =>
                fun (hw : (w . R . x)) =>
                  Exists.intro w (Iff.mp (inv_pair_prop R h w x) (hw))
            )
    )
    (
      fun (h₁ : is_total (R⁻¹) X) =>
        fun (x) =>
          fun (s : x ∈ X) =>
           Exists.elim (h₁ x s) (
              fun (w) =>
                fun (hw : (x . (R⁻¹) . w)) =>
                  Exists.intro w (Iff.mpr (inv_pair_prop R h w x) (hw))
           )
    )


theorem func_subs : ∀ P Q, (is_functional Q) → (P ⊆ Q) → (is_functional P) :=
  fun (P Q) =>
    fun (hfunc : (is_functional Q)) =>
      fun (hsubs : (P ⊆ Q)) =>
        fun (x y z) =>
          fun (hxy : (x . P . y)) =>
            fun (hxz : (x . P . z)) =>
              hfunc x y z (hsubs (x, y) hxy) (hsubs (x, z) hxz)


theorem inj_subs : ∀ P Q, (is_injective Q) → (P ⊆ Q) → (is_injective P) :=
  fun (P Q) =>
    fun (hinj : (is_injective Q)) =>
      fun (hsubs : (P ⊆ Q)) =>
        fun (x y z) =>
          fun (hxy : (x . P . z)) =>
            fun (hyz : (y . P . z)) =>
              hinj x y z (hsubs (x, z) hxy) (hsubs (y, z) hyz)


theorem tot_subs : ∀ P Q, (is_total P A) → (P ⊆ Q) → (is_total Q (A ∪ dom Q)) :=
  fun (P Q) =>
    fun (hist : (is_total P A)) =>
      fun (hpq : (P ⊆ Q)) =>
        fun (x) =>
          fun (hx : (x ∈ (A ∪ dom Q))) =>
            let u := Iff.mp (union2_sets_prop A (dom Q) x) hx
            Or.elim u
            (
              fun (hxA : x ∈ A) =>
                let v := hist x hxA
                Exists.elim v (
                  fun (y) =>
                    fun (hy : (x . P . y)) =>
                      Exists.intro y (
                        hpq (x, y) hy
                      )
                )
            )
            (
              fun (hxQ : x ∈ dom Q) =>
                Iff.mp (dom_prop Q x) hxQ
            )


theorem surj_subs : ∀ P Q, (is_surjective P A) → (P ⊆ Q) → (is_surjective Q (A ∪ rng Q)) :=
  fun (P Q) =>
    fun (hist : (is_surjective P A)) =>
      fun (hpq : (P ⊆ Q)) =>
        fun (x) =>
          fun (hx : (x ∈ (A ∪ rng Q))) =>
            let u := Iff.mp (union2_sets_prop A (rng Q) x) hx
            Or.elim u
            (
              fun (hxA : (x ∈ A)) =>
                let v := hist x hxA
                Exists.elim v (
                  fun (y) =>
                    fun (hy : (y . P . x)) =>
                      Exists.intro y (
                        hpq (y, x) hy
                      )
                )
            )
            (
              fun (hxQ : x ∈ rng Q) =>
                Iff.mp (rng_prop Q x) hxQ
            )





theorem func_un :
∀ A B C D P Q,
(P BinRelBtw A AND B) → (Q BinRelBtw C AND D) → (A ∩ C = ∅) → (is_functional P) → (is_functional Q) → (is_functional (P ∪ Q)) :=
fun (A B C D P Q) =>
  fun (hAB : (P BinRelBtw A AND B)) =>
    fun (hCD : (Q BinRelBtw C AND D)) =>
      fun (hAC : (A ∩ C = ∅)) =>
        fun (hfuncP : (is_functional P)) =>
          fun (hfuncQ : (is_functional Q)) =>
            fun (x y z) =>
              fun (hxy : (x . (P ∪ Q) . y)) =>
                fun (hxz : (x . (P ∪ Q) . z)) =>
                  let u := Iff.mp (union2_sets_prop P Q (x, y)) hxy
                  let v := Iff.mp (union2_sets_prop P Q (x, z)) hxz
                  Or.elim u
                  (
                    fun (xpy : (x . P . y)) =>
                      Or.elim v
                      (
                        fun (xpz : (x . P . z)) =>
                          hfuncP x y z xpy xpz
                      )
                      (
                        fun (xqz : (x . Q . z)) =>
                          False.elim (
                            let s := And.left (Iff.mp (cartesian_product_pair_prop A B x y) (hAB (x, y) xpy))
                            let t := And.left (Iff.mp (cartesian_product_pair_prop C D x z) (hCD (x, z) xqz))
                            let m := Iff.mpr (intersect_2sets_prop A C x) (And.intro (s) (t))
                            empty_set_is_empty x (
                              eq_subst (fun (n) => x ∈ n) (A ∩ C) (∅) hAC m
                            )
                          )
                      )
                  )
                  (
                    fun (xqy : (x . Q . y)) =>
                      Or.elim v
                      (
                        fun (xpz : (x . P . z)) =>
                          False.elim (
                            let s := And.left (Iff.mp (cartesian_product_pair_prop A B x z) (hAB (x, z) xpz))
                            let t := And.left (Iff.mp (cartesian_product_pair_prop C D x y) (hCD (x, y) xqy))
                            let m := Iff.mpr (intersect_2sets_prop A C x) (And.intro (s) (t))
                            empty_set_is_empty x (
                              eq_subst (fun (n) => x ∈ n) (A ∩ C) (∅) hAC m
                            )
                          )
                      )
                      (
                        fun (xqz : (x . Q . z)) =>
                          hfuncQ x y z xqy xqz
                      )
                  )


theorem inj_un :
∀ A B C D P Q,
(P BinRelBtw A AND B) → (Q BinRelBtw C AND D) → (B ∩ D = ∅) → (is_injective P) → (is_injective Q) → (is_injective (P ∪ Q)) :=
  fun (A B C D P Q) =>
    fun (hAB : (P BinRelBtw A AND B)) =>
      fun (hCD : (Q BinRelBtw C AND D)) =>
        fun (hBD : (B ∩ D = ∅)) =>
          fun (hP : (is_injective P)) =>
            fun (hQ : (is_injective Q)) =>
              let a₁ := And.left (prop_then_binary_relation A B P hAB)
              let a₂ := And.left (prop_then_binary_relation C D Q hCD)
              let u := Iff.mp (inj_inv_func P (a₁)) hP
              let v := Iff.mp (inj_inv_func Q (a₂)) hQ
              let s := inv_between_mp A B P hAB
              let t := inv_between_mp C D Q hCD
              let m := func_un B A D C (P⁻¹) (Q⁻¹) s t hBD u v
              let res₁ := inv_union_prop P Q a₁ a₂
              let res₂ := eq_subst (fun (n) => is_functional n) ((P⁻¹) ∪ (Q⁻¹)) ((P ∪ Q)⁻¹) (Eq.symm (res₁)) (m)
              Iff.mpr (inj_inv_func (P ∪ Q) (union2_rel_is_rel P Q a₁ a₂)) (
                res₂
              )


theorem tot_un :
∀ A B P Q, (is_total P A) → (is_total Q B) → (is_total (P ∪ Q) (A ∪ B)) :=
  fun (A B P Q) =>
      fun (hPt : (is_total P A)) =>
        fun (hQt : (is_total Q B)) =>
          fun (x) =>
            fun (hx : (x ∈ (A ∪ B))) =>
              let u := Iff.mp (union2_sets_prop A B x) hx
              Or.elim u
              (
                fun (hxa : x ∈ A) =>
                  Exists.elim (hPt x hxa) (
                    fun (y) =>
                      fun (hy : (x . P . y)) =>
                        Exists.intro y (
                          And.left (union2_sets_subset_prop P Q) (x, y) hy
                        )
                  )
              )
              (
                fun (hxb : x ∈ B) =>
                  Exists.elim (hQt x hxb) (
                    fun (y) =>
                      fun (hy : (x . Q . y)) =>
                        Exists.intro y (
                          And.right (union2_sets_subset_prop P Q) (x, y) hy
                        )
                  )
              )


theorem surj_un :
∀ A B P Q, (is_surjective P A) → (is_surjective Q B) → (is_surjective (P ∪ Q) (A ∪ B)) :=
  fun (A B P Q) =>
    fun (hPt : (is_surjective P A)) =>
        fun (hQt : (is_surjective Q B)) =>
          fun (x) =>
            fun (hx : (x ∈ (A ∪ B))) =>
              let u := Iff.mp (union2_sets_prop A B x) hx
              Or.elim u
              (
                fun (hxa : x ∈ A) =>
                  Exists.elim (hPt x hxa) (
                    fun (y) =>
                      fun (hy : (y . P . x)) =>
                        Exists.intro y (
                          And.left (union2_sets_subset_prop P Q) (y, x) hy
                        )
                  )
              )
              (
                fun (hxb : x ∈ B) =>
                  Exists.elim (hQt x hxb) (
                    fun (y) =>
                      fun (hy : (y . Q . x)) =>
                        Exists.intro y (
                          And.right (union2_sets_subset_prop P Q) (y, x) hy
                        )
                  )
              )


theorem func_intr :
∀ P Q, (is_functional P ∨ is_functional Q) → (is_functional (P ∩ Q)) :=
  fun (P Q) =>
    fun (hfuncPQ : (is_functional P ∨ is_functional Q)) =>
      Or.elim hfuncPQ
      (
        fun (hfuncP : (is_functional P)) =>
          func_subs (P ∩ Q) P (hfuncP) (
            And.left (intersect_2sets_subset_prop P Q)
          )
      )
      (
        fun (hfuncQ : (is_functional Q)) =>
          func_subs (P ∩ Q) Q (hfuncQ) (
            And.right (intersect_2sets_subset_prop P Q)
          )
      )


theorem inj_intr :
∀ P Q, (is_injective P ∨ is_injective Q) → (is_injective (P ∩ Q)) :=
  fun (P Q) =>
    fun (hinjPQ : (is_injective P ∨ is_injective Q)) =>
      Or.elim hinjPQ
      (
        fun (hinjP : (is_injective P)) =>
          inj_subs (P ∩ Q) P (hinjP) (
            And.left (intersect_2sets_subset_prop P Q)
          )
      )
      (
        fun (hinjQ : (is_injective Q)) =>
          inj_subs (P ∩ Q) Q (hinjQ) (
            And.right (intersect_2sets_subset_prop P Q)
          )
      )


theorem tot_intr :
∀ P Q A B, (is_total P A) → (is_total Q B) → (is_functional (P ∪ Q)) → (is_total (P ∩ Q) (A ∩ B)) :=
  fun (P Q A B) =>
    fun (htota : (is_total P A)) =>
      fun (htotb : (is_total Q B)) =>
        fun (hfunc : (is_functional (P ∪ Q))) =>
          fun (x) =>
            fun (hx : x ∈ A ∩ B) =>
              let u := Iff.mp (intersect_2sets_prop A B x) hx
              let v := htota x (And.left u)
              let s := htotb x (And.right u)
              Exists.elim v (
                fun (y) =>
                  fun (hy : (x . P . y)) =>
                    Exists.elim s (
                      fun (z) =>
                        fun (hz : (x . Q . z)) =>
                          let frst := And.left (union2_sets_subset_prop P Q) (x, y) hy
                          let scnd := And.right (union2_sets_subset_prop P Q) (x, z) hz
                          let thrd := hfunc x y z frst scnd
                          Exists.intro y (
                            Iff.mpr (intersect_2sets_prop P Q (x, y)) (
                              And.intro hy (
                                eq_subst (fun (t) => (x . Q . t)) z y (Eq.symm thrd) (hz)
                              )
                            )
                          )
                    )
              )


theorem surj_intr :
∀ P Q A B, (is_surjective P A) → (is_surjective Q B) → (is_injective (P ∪ Q)) → (is_surjective (P ∩ Q) (A ∩ B)) :=
  fun (P Q A B) =>
    fun (hsurja : (is_surjective P A)) =>
      fun (hsurjb : (is_surjective Q B)) =>
        fun (hinj : (is_injective (P ∪ Q))) =>
          fun (x) =>
            fun (hx : x ∈ A ∩ B) =>
              let u := Iff.mp (intersect_2sets_prop A B x) hx
              let v := hsurja x (And.left u)
              let s := hsurjb x (And.right u)
              Exists.elim v (
                fun (y) =>
                  fun (hy : (y . P . x)) =>
                    Exists.elim s (
                      fun (z) =>
                        fun (hz : (z . Q . x)) =>
                          let frst := And.left (union2_sets_subset_prop P Q) (y, x) hy
                          let scnd := And.right (union2_sets_subset_prop P Q) (z, x) hz
                          let thrd := hinj y z x frst scnd
                          Exists.intro y (
                            Iff.mpr (intersect_2sets_prop P Q (y, x)) (
                              And.intro hy (
                                eq_subst (fun (t) => (t . Q . x)) z y (Eq.symm thrd) (hz)
                              )
                            )
                          )
                    )
              )

theorem func_diff :
∀ P Q, (is_functional P) → (is_functional (P \ Q)) :=
  fun (P Q) =>
    fun (hfunc : (is_functional P)) =>
      func_subs (P \ Q) P hfunc (
        difference_subset_prop P Q
      )


theorem inj_diff :
∀ P Q, (is_injective P) → (is_injective (P \ Q)) :=
  fun (P Q) =>
    fun (hinj : (is_injective P)) =>
      inj_subs (P \ Q) P hinj (
        difference_subset_prop P Q
      )

theorem tot_diff :
∀ P Q A, (is_total P A) → (is_total (P \ Q) (A \ (dom (P ∩ Q)) )) :=
  fun (P Q A) =>
      fun (htotA : (is_total P A)) =>
          fun (x) =>
            fun (hx : x ∈ (A \ (dom (P ∩ Q)))) =>
              let u := Iff.mp (difference_prop A (dom (P ∩ Q)) x) hx
              let v := htotA x (And.left u)
              Exists.elim v (
                fun (y) =>
                  fun (hPy : (x . P . y)) =>
                    Exists.intro y (
                      Iff.mpr (difference_prop P Q (x, y)) (
                        And.intro (hPy) (
                          fun (hQy : (x . Q . y)) =>
                            let s := Iff.mpr (intersect_2sets_prop P Q (x, y)) (And.intro hPy hQy)
                            And.right u (
                              Iff.mpr (dom_prop (P ∩ Q) x) (
                                Exists.intro y (s)
                              )
                            )
                        )
                      )
                    )
              )


theorem surj_diff : ∀ P Q A, (is_surjective P A) → (is_surjective (P \ Q) (A \ (rng (P ∩ Q)))) :=
  fun (P Q A) =>
    fun (hsurjA : (is_surjective P A)) =>
      fun (x) =>
          fun (hx : x ∈ (A \ (rng (P ∩ Q)))) =>
            let u := Iff.mp (difference_prop A (rng (P ∩ Q)) x) hx
            let v := hsurjA x (And.left u)
            Exists.elim v (
              fun (y) =>
                fun (hPy : (y . P . x)) =>
                  Exists.intro y (
                    Iff.mpr (difference_prop P Q (y, x)) (
                      And.intro (hPy) (
                        fun (hQy : (y . Q . x)) =>
                          let s := Iff.mpr (intersect_2sets_prop P Q (y, x)) (And.intro hPy hQy)
                          And.right u (
                            Iff.mpr (rng_prop (P ∩ Q) x) (
                              Exists.intro y (s)
                            )
                          )
                      )
                    )
                  )
            )


theorem tot_dom_prop : ∀ R X, ((is_total R X) ↔ (X ⊆ dom R)) :=
  fun (R) => fun (X) =>
    Iff.intro
    (
      fun (h₁ : is_total R X) =>
        fun (x) =>
          fun (s : x ∈ X) =>
            Exists.elim (h₁ x s) (
              fun(w) =>
                fun (hw : (x . R . w)) =>
                  Iff.mpr (dom_prop R x) (Exists.intro w (hw))
            )
    )
    (
      fun (h₁ : X ⊆ dom R) =>
        fun (x) =>
          fun (s : x ∈ X) =>
            let first := h₁ x s
            let second := Iff.mp (dom_prop R x) first
            Exists.elim second
            (
              fun (w) =>
                fun (hw : (x . R . w)) =>
                  Exists.intro w (hw)
            )
    )



theorem surj_rng_prop : ∀ R X, ((is_surjective R X) ↔ (X ⊆ rng R)) :=
  fun (R) => fun (X) =>
    Iff.intro
    (
      fun (h₁ : is_surjective R X) =>
        fun (y) =>
          fun (s : y ∈ X) =>
            Exists.elim (h₁ y s) (
              fun (w) =>
                fun (hw : (w, y) ∈ R) =>
                  Iff.mpr (rng_prop R y) (Exists.intro w (hw))
            )
    )
    (
      fun (h₁ : X ⊆ rng R) =>
        fun (y) =>
          fun (s : y ∈ X) =>
            let first := h₁ y s
            let second := (Iff.mp (rng_prop R y)) (first)
            Exists.elim second
            (
              fun (w) =>
                fun (hw : (w, y) ∈ R) =>
                  Exists.intro w (hw)
            )
    )



theorem preimage_inter_func : ∀ R, (BinRel R) → ((is_functional R) ↔ (∀ X Y, R⁻¹.[X ∩ Y] = (R⁻¹.[X] ∩ R⁻¹.[Y]))) :=
  fun (R) =>
    fun (hR : (BinRel R)) =>
      Iff.intro
      (
        fun (hfunc : (is_functional R)) =>
          fun (X Y) =>
            Iff.mp (subs_subs_eq (R⁻¹.[X ∩ Y]) (R⁻¹.[X] ∩ R⁻¹.[Y])) (
              And.intro (rel_preimage_inter X Y R hR) (
                fun (x) =>
                  fun (hx : (x ∈ R⁻¹.[X] ∩ R⁻¹.[Y])) =>
                    let u := Iff.mp (intersect_2sets_prop (R⁻¹.[X]) (R⁻¹.[Y]) x) hx
                    let v := Iff.mp (preimage_prop R X hR x) (And.left u)
                    let s := Iff.mp (preimage_prop R Y hR x) (And.right u)
                    Exists.elim v (
                      fun (y) =>
                        fun (hy : y ∈ X ∧ (x . R . y)) =>
                          Exists.elim s (
                            fun (s) =>
                              fun (hs : s ∈ Y ∧ (x . R . s)) =>
                                let first := hfunc x y s (And.right hy) (And.right hs)
                                Iff.mpr (preimage_prop R (X ∩ Y) hR x) (
                                  Exists.intro y (
                                    And.intro (
                                      Iff.mpr (intersect_2sets_prop X Y y) (
                                        And.intro (And.left hy) (
                                          eq_subst (fun (t) => t ∈ Y) s y (Eq.symm first) (And.left hs)
                                        )
                                      )
                                    ) (And.right hy)
                                  )
                                )
                          )
                    )
              )
            )
      )
      (
        fun (him : (∀ X Y, R⁻¹.[X ∩ Y] = (R⁻¹.[X] ∩ R⁻¹.[Y]))) =>
          fun (x y z) =>
            fun (hxy : (x . R . y)) =>
              fun (hxz : (x . R . z)) =>
                let u := him {y} {z}
                let v := Iff.mpr (preimage_prop R {y} hR x) (
                  Exists.intro y (And.intro (elem_in_singl y) (hxy))
                )
                let s := Iff.mpr (preimage_prop R {z} hR x) (
                  Exists.intro z (And.intro (elem_in_singl z) (hxz))
                )
                let t := Iff.mpr (intersect_2sets_prop (R⁻¹.[{y}]) (R⁻¹.[{z}]) x) (
                  And.intro (v) (s)
                )
                let res := eq_subst (fun (m) => x ∈ m) ((R⁻¹.[{y}]) ∩ (R⁻¹.[{z}])) (R⁻¹.[{y} ∩ {z}]) (Eq.symm u) (t)
                let res₂ := Iff.mp (preimage_prop R ({y} ∩ {z}) hR x) res
                Exists.elim res₂ (
                  fun (n) =>
                    fun (hn : n ∈ ({y} ∩ {z}) ∧ (x . R . n)) =>
                      let res₃ := And.left hn
                      let res₄ := Iff.mp (intersect_2sets_prop {y} {z} n) res₃
                      let res₅ := in_singl_elem y n (And.left res₄)
                      let res₆ := in_singl_elem z n (And.right res₄)
                      Eq.trans (Eq.symm res₅) (res₆)
                )
      )



theorem image_inter_inject : ∀ R, (BinRel R) → ((is_injective R) ↔ (∀ X Y, R.[X ∩ Y] = (R.[X] ∩ R.[Y]))) :=
  fun (R) =>
    fun (hR : (BinRel R)) =>
      Iff.intro
      (
        fun (injR : (is_injective R)) =>
          let u := Iff.mp (inj_inv_func R hR) injR
          let v := inv_is_rel R hR
          let res := Iff.mp (preimage_inter_func (R⁻¹) v) u
          eq_subst (fun (t) => ∀ X Y, t.[X ∩ Y] = (t.[X] ∩ t.[Y])) ((R⁻¹)⁻¹) R (inv_prop R hR) (res)
      )
      (
        fun (himg : ∀ X Y, R.[X ∩ Y] = (R.[X] ∩ R.[Y])) =>
          let res₁ := eq_subst (fun (t) => ∀ X Y, t.[X ∩ Y] = (t.[X] ∩ t.[Y])) R ((R⁻¹)⁻¹) (Eq.symm (inv_prop R hR)) (himg)
          let res₂ := inv_is_rel R hR
          let res₃ := Iff.mpr (preimage_inter_func (R⁻¹) res₂) res₁
          Iff.mpr (inj_inv_func R hR) (res₃)
      )

open Classical


theorem preimage_diff_func : ∀ R, (BinRel R) → ((is_functional R) ↔ (∀ X Y, R⁻¹.[X \ Y] = (R⁻¹.[X]) \ (R⁻¹.[Y]))) :=
  fun (R) =>
    fun (hR : (BinRel R)) =>
      Iff.intro
      (
        fun (hisf : (is_functional R)) =>
          fun (X Y) =>
            Iff.mp (subs_subs_eq (R⁻¹.[X \ Y]) ((R⁻¹.[X]) \ (R⁻¹.[Y]))) (
              And.intro (
                fun (x) =>
                  fun (hx : x ∈ R⁻¹.[X \ Y]) =>
                    let u := Iff.mp (preimage_prop R (X \ Y) hR x) hx
                    Exists.elim u (
                      fun (y) =>
                        fun (hy : y ∈ (X \ Y) ∧ (x . R . y)) =>
                          Iff.mpr (difference_prop (R⁻¹.[X]) (R⁻¹.[Y]) x) (
                            And.intro (
                              Iff.mpr (preimage_prop R X hR x) (
                                Exists.intro y (And.intro (And.left (Iff.mp (difference_prop X Y y) (
                                  And.left hy
                                ))) (And.right hy))
                              )
                            ) (
                              fun (hxr : x ∈ (R⁻¹.[Y])) =>
                                let v := Iff.mp (preimage_prop R Y hR x) hxr
                                Exists.elim v (
                                  fun (m) =>
                                    fun (hm : m ∈ Y ∧ (x . R . m)) =>
                                      let s := hisf x y m (And.right hy) (And.right hm)
                                      And.right (Iff.mp (difference_prop X Y y) (And.left hy)) (
                                        eq_subst (fun (t) => t ∈ Y) m y (Eq.symm s) (And.left hm)
                                      )
                                )

                            )
                          )
                    )

              ) (rel_preimage_diff X Y R)
            )

      )
      (
        fun (him : (∀ X Y, R⁻¹.[X \ Y] = (R⁻¹.[X] \ R⁻¹.[Y]))) =>
          fun (x y z) =>
            fun (hxy : (x . R . y)) =>
              fun (hxz : (x . R . z)) =>
                let A := R⁻¹.[{y} \ {z}]
                let B := (R⁻¹.[{y}] \ R⁻¹.[{z}])
                let u := him {y} {z}
                Or.elim (em (y = z))
                (fun (hyz : y = z) => hyz)
                (
                  fun (hnyz : y ≠ z) =>
                    let s := Iff.mpr (preimage_prop R ({y} \ {z}) hR x) (
                      Exists.intro y (And.intro (
                        Iff.mpr (difference_prop {y} {z} y) (
                          And.intro (elem_in_singl y) (
                            fun (hsigyz : y ∈ {z}) =>
                              hnyz (
                                in_singl_elem z y hsigyz
                              )
                          )
                        )
                      ) (hxy))
                    )

                    let m := eq_subst (fun (t) => x ∈ t) A B u s

                    let m₂ := And.right (Iff.mp (difference_prop (R⁻¹.[{y}]) (R⁻¹.[{z}]) x) m)

                    let m₃ := Iff.mpr (preimage_prop R {z} hR x)

                    let m₄ := Iff.mp (contraposition (∃ t ∈ {z}; (x . R . t)) (x ∈ R⁻¹.[{z}])) m₃ m₂

                    let m₅ := Iff.mpr (morgan_uni Set (fun (t) => t ∈ {z} ∧ (x . R . t))) m₄ z


                    False.elim (
                      m₅ (And.intro (elem_in_singl z) (hxz))
                    )
                )

      )



theorem image_diff_inj : ∀ R, (BinRel R) → ((is_injective R) ↔ (∀ X Y, R.[X \ Y] = (R.[X]) \ (R.[Y]))) :=
  fun (R) =>
    fun (hr : (BinRel R)) =>
      Iff.intro
      (
        fun (hinj : (is_injective R)) =>
          let u := Iff.mp (inj_inv_func R hr) hinj
          let v := inv_is_rel R hr
          let s := Iff.mp (preimage_diff_func (R⁻¹) v) u
          eq_subst (fun (t) => (∀ X Y, t.[X \ Y] = (t.[X]) \ (t.[Y]))) ((R⁻¹)⁻¹) (R) (inv_prop R hr) (s)
      )
      (
        fun (hrxy : (∀ X Y, R.[X \ Y] = (R.[X]) \ (R.[Y]))) =>
          let u := eq_subst (fun (t) => (∀ X Y, t.[X \ Y] = (t.[X]) \ (t.[Y]))) R ((R⁻¹)⁻¹) (Eq.symm (inv_prop R hr)) hrxy
          let v := inv_is_rel R hr
          let s := Iff.mpr ((preimage_diff_func (R⁻¹) v)) u
          Iff.mpr (inj_inv_func R hr) (s)
      )




theorem composition_functional : ∀ P Q, is_functional P → is_functional Q → is_functional (P ∘ Q) :=
  fun (P) => fun (Q) => fun (h : is_functional P) => fun (g : is_functional Q) =>
    fun (x) => fun (y) => fun (z) => fun (t : (x . (P ∘ Q) . y)) => fun (s : (x . (P ∘ Q) . z)) =>
      let first := Iff.mp (composition_pair_prop P Q x y) t
      Exists.elim (first)
      (
        fun (w) =>
          fun (hw : (x . Q . w) ∧ (w . P . y)) =>
          let second := Iff.mp (composition_pair_prop P Q x z) s
          Exists.elim second
          (
            fun (u) =>
              fun (hu : (x . Q . u) ∧ (u . P . z)) =>
                let third := g x w u (And.left hw) (And.left hu)
                h w y z  (And.right hw) (eq_subst (fun (m) => (m . P . z)) u  w (Eq.symm third) (And.right hu))
          )
      )


theorem composition_injective : ∀ P Q, is_injective P → is_injective Q → is_injective (P ∘ Q) :=
  fun (P) => fun (Q) => fun (h : is_injective P) => fun (g : is_injective Q) =>
    fun (x) => fun (y) => fun (z) => fun (t : (x . (P ∘ Q) . z)) => fun (s : (y . (P ∘ Q) . z)) =>
      let first := Iff.mp (composition_pair_prop P Q x z) t
      Exists.elim (first)
      (
        fun (w) =>
          fun (hw : (x . Q . w) ∧ (w . P . z)) =>
            let second := Iff.mp (composition_pair_prop P Q y z) s
            Exists.elim second
            (
              fun (u) =>
                fun (hu : (y . Q . u) ∧ (u . P . z)) =>
                  let third := h u w z (And.right hu) (And.right hw)
                  g x y w (And.left hw) (eq_subst (fun (m) => (y . Q . m)) u w (third) (And.left hu))
            )
      )



theorem composition_total : ∀ P Q X Y, binary_relation_between Y X Q → is_total P X → is_total Q Y → is_total (P ∘ Q) Y :=
  fun (P) => fun (Q) => fun(X) => fun (Y) => fun (m : binary_relation_between Y X Q) => fun (h : is_total P X) => fun (g : is_total Q Y) =>
    fun (x) => fun (h₁ : x ∈ Y) =>
      let first := g x h₁
      Exists.elim first
      (
        fun (w) =>
          fun (hw : (x . Q . w)) =>
            let h₂ := And.right (Iff.mp (cartesian_product_pair_prop Y X x w) (m (x, w) hw))
            let second := h w (h₂)
            Exists.elim second
            (
              fun (u) =>
                fun (hu : (w . P . u)) =>
                  Exists.intro u (Iff.mpr (composition_pair_prop P Q x u) (Exists.intro w (And.intro (hw) (hu))))
            )
      )



theorem composition_surjective : ∀ P Q X Y, binary_relation_between Y X P → is_surjective P X → is_surjective Q Y → is_surjective (P ∘ Q) X :=
  fun (P) => fun (Q) => fun (X) => fun (Y) => fun (m : binary_relation_between Y X P) => fun (h : is_surjective P X) => fun (g : is_surjective Q Y) =>
    fun (x) => fun (h₁ : x ∈ X) =>
      let first := h x h₁
      Exists.elim first
      (
        fun (w) =>
          fun (hw : (w . P . x)) =>
            let h₂ := And.left (Iff.mp (cartesian_product_pair_prop Y X w x) (m (w, x) hw))
            let second := g w (h₂)
            Exists.elim second
            (
              fun (u) =>
                fun (hu : (u . Q . w)) =>
                  Exists.intro u (Iff.mpr (composition_pair_prop P Q u x) (Exists.intro w (And.intro (hu) (hw))))
            )
      )



noncomputable def partial_function (f A B : Set) : Prop := binary_relation_between A B f ∧ is_functional f
noncomputable def function (f A B : Set) : Prop := partial_function f A B ∧ is_total f A




syntax term "PartFun" term "To" term : term

macro_rules
  | `($f:term PartFun $A:term To $B:term)  => `(partial_function $f $A $B)

syntax term "Fun" term "To" term : term

macro_rules
  | `($f:term Fun $A:term To $B:term) => `(function $f $A $B)



noncomputable def val_defined (f x : Set) : Prop := x ∈ dom f
noncomputable def val_undefined (f x : Set) : Prop := x ∉ dom f


syntax term "↓↓" term : term

macro_rules
  | `($f:term ↓↓ $x:term) => `(val_defined $f $x)

syntax term "↑↑" term : term

macro_rules
  | `($f:term ↑↑ $x:term) => `(val_undefined $f $x)


theorem function_is_partial_function: ∀ f A B, (f Fun A To B) → (f PartFun A To B) :=
  fun (f A B) => fun (h : f Fun A To B) => And.left h


theorem partial_function_change_B : ∀ f A B C, (f PartFun A To B) → (B ⊆ C) → (f PartFun A To C) :=
  fun (f A B C) =>
    fun (hf : (f PartFun A To B)) =>
      fun (hBC : B ⊆ C) =>
        let u := cartesian_product_subset A B A C (subset_refl A) hBC
        And.intro (subset_trans_curry f (A × B) (A × C) (And.left hf) (u)) (And.right hf)



theorem partial_function_change_A : ∀ f A B C, (f PartFun A To B) → (A ⊆ C) → (f PartFun C To B) :=
  fun (f A B C) =>
    fun (hf : (f PartFun A To B)) =>
      fun (hAC : A ⊆ C) =>
        let u := cartesian_product_subset A B C B hAC (subset_refl B)
        And.intro (subset_trans_curry f (A × B) (C × B) (And.left hf) u) (And.right hf)


theorem function_change_B : ∀ f A B C, (f Fun A To B) → (B ⊆ C) → (f Fun A To C) :=
  fun (f A B C) =>
    fun (hf : (f Fun A To B)) =>
      fun (hBC : B ⊆ C) =>
        let u := cartesian_product_subset A B A C (subset_refl A) (hBC)
        And.intro (And.intro (subset_trans_curry f (A × B) (A × C) (And.left (And.left hf))
        (u)) (And.right (And.left hf))) (And.right hf)



theorem dom_partial_function : ∀ f A B, (f PartFun A To B) → dom f ⊆ A :=
  fun (f A B) => fun (h : f PartFun A To B) =>
    fun (x) => fun (g : x ∈ dom f) =>
      let first := And.left h
      And.left (And.right (prop_then_binary_relation A B f (first))) x g


theorem rng_partial_function : ∀ f A B, (f PartFun A To B) → rng f ⊆ B :=
  fun (f A B) => fun (h : f PartFun A To B) =>
    fun (x) => fun (g : x ∈ rng f) =>
      let first := Iff.mp (rng_prop f x) g
      Exists.elim first
      (
        fun (w) =>
          fun (hw: (w . f . x)) =>
            let second := And.left h (w, x) hw
            And.right (Iff.mp (cartesian_product_pair_prop A B w x) second)
      )


theorem dom_function: ∀ f A B, (f Fun A To B) → A = dom f :=
  fun (f A B) => fun (h : f Fun A To B) =>
    extensionality A (dom f) (
      fun (x) =>
      Iff.intro
      (
        fun (g : x ∈ A) =>
          let first := And.right h x g
          Iff.mpr (dom_prop f x) first
      )
      (
        fun (g : x ∈ dom f) =>
          let first := And.left (And.left h)
          And.left (And.right (prop_then_binary_relation A B f (first))) x g
      )
    )

theorem function_no_change_A : ∀ f A B C, (f Fun A To B) → (f Fun C To B) → (A = C) :=
  fun (f A B C) =>
    fun (hf : (f Fun A To B)) =>
        fun (hf₂ : f Fun C To B) =>
          Eq.trans (dom_function f A B hf) (Eq.symm (dom_function f C B hf₂))



noncomputable def value_pick (f x : Set) : Set := ⋃ (f  .[ { x } ])
syntax term "⦅" term "⦆" : term
macro_rules
  | `($f:term ⦅ $x:term ⦆) => `(value_pick $f $x)



theorem partial_function_value_pick_property_defined : ∀ f A B x, (f PartFun A To B) → (f ↓↓ x) → (x . f . (f⦅x⦆)) :=
  fun (f A B x) => fun (g : f PartFun A To B) => fun (h₁ : f ↓↓ x) =>
    let second := And.right g
    let fourth := Iff.mp (dom_prop f x) h₁
    let fifth : ∀ s ∈ f .[ { x } ]; (x . f . s) := fun (s) => fun(h₂ : s ∈ f .[{x}]) =>
      let sixth := And.right (Iff.mp (specification_set_is_specification (fun (u) => (∃ a ∈ {x}; (a . f . u))) (rng f) s) h₂)
      Exists.elim sixth
      (
        fun (t) => fun (ht : t ∈ {x} ∧ (t . f . s)) =>
          eq_subst (fun (u) => (u . f . s)) t x (in_singl_elem x t (And.left ht)) (And.right ht)
      )
    let seventh : ∃ d, ((f .[ { x } ]) = {d}) := Exists.elim fourth (fun (w) => fun (hw : (x . f . w)) =>
      Exists.intro w (extensionality (f .[ { x } ]) ({w}) (fun (a) => (Iff.intro
      (
        fun (eight : a ∈ (f .[ { x } ])) =>
          let ha := fifth a eight
          let h_sec := second x a w ha hw
          eq_subst (fun (u) => u ∈ {w}) (w) (a) (Eq.symm h_sec) (elem_in_singl w)
      )
      (
        fun (eight : a ∈ ({w})) =>
          let frst := in_singl_elem w a eight
          eq_subst (fun (u) => u ∈ (f .[ { x } ])) w a (Eq.symm frst) (
            Iff.mpr (specification_set_is_specification (fun (u) => (∃ a ∈ {x}; (a . f . u))) (rng f) w) (And.intro
            (Iff.mpr (rng_prop f w) (Exists.intro x (hw))) (Exists.intro x (And.intro (elem_in_singl x) (hw))))
          )

      )
      )))
    )
    Exists.elim seventh
    (
      fun (w) => fun (hw : f.[{x}] = {w}) =>
        let rememb := union_sing w
        let rememb2 : f⦅x⦆ = w := eq_subst (fun (u) => ⋃ u = w) {w} (f.[{x}]) (Eq.symm hw) (rememb)
        let rememb3 : w ∈ f.[{x}] := eq_subst (fun (u) => w ∈ u) {w} (f.[{x}]) (Eq.symm hw) (elem_in_singl w)
        let rememb4 : (x . f . w) := fifth w rememb3
        eq_subst (fun (u) => (x . f . u)) w (f⦅x⦆) (Eq.symm rememb2) (rememb4)
    )

theorem function_value_pick_property: ∀ f A B, ∀ x ∈ A; (f Fun A To B) → (x . f . (f⦅x⦆) ) :=
    fun (f A B x) => fun (h : x ∈ A) => fun (g : (f Fun A To B)) =>
      let first := function_is_partial_function f A B g
      let second := dom_function f A B g
      let third := eq_subst (fun (u) => x ∈ u) A (dom f) (second) (h)
      partial_function_value_pick_property_defined f A B x first third



theorem partial_function_equal_value_prop : ∀ f A B, (f PartFun A To B) → ∀ x y, (f ↓↓ x) → ( (x . f . y) ↔ (y = f⦅x⦆)) :=
  fun (f A B) => fun (h₁ : f PartFun A To B) => fun (x y) => fun (h₃ : f ↓↓ x) =>
    Iff.intro
    (
      fun (s : (x . f . y)) =>
        let first := partial_function_value_pick_property_defined f A B x h₁ h₃
        And.right h₁ x y (f⦅x⦆) s first
    )
    (
      fun (s : y = f⦅x⦆) =>
        let first := partial_function_value_pick_property_defined f A B x h₁ h₃
        eq_subst (fun (u) => (x . f . u)) (f⦅x⦆) y (Eq.symm s) (first)
    )




theorem function_equal_value_prop : ∀ f A B, (f Fun A To B) → ∀ x y, x ∈ A → ( (x . f . y) ↔ (y = f⦅x⦆)) :=
  fun (f A B) => fun (h₁ : f Fun A To B) => fun (x y) => fun (h₂ : x ∈ A) =>
    Iff.intro
    (
      fun (s : (x . f . y)) =>
        let first := function_value_pick_property f A B x h₂ h₁
        (And.right (And.left h₁)) x y (f⦅x⦆) s first
    )
    (
      fun (s : y = f⦅x⦆) =>
        let first := function_value_pick_property f A B x h₂ h₁
        eq_subst (fun (u) => (x . f . u)) (f⦅x⦆) y (Eq.symm s) (first)
    )


theorem partial_function_value_pick_property_undefined : ∀ f A B x, (f PartFun A To B) → (f ↑↑ x) → (f⦅x⦆ = ∅) :=
  fun (f A B x) =>
    fun (_ : (f PartFun A To B)) =>
      fun (hund : (f ↑↑ x)) =>
        let r : empty (f.[ { x } ]) :=
          fun (y) => fun (hy : y ∈ (f.[ { x } ])) =>
            let A₁ := rng f
            let P₁ := fun (t) => ∃ a ∈ {x}; (a . f . t)
            let res₁ := And.right (Iff.mp (specification_set_is_specification P₁ A₁ y) (hy))
            Exists.elim res₁
            (
              fun (x₀) =>
                fun (hx₀ : x₀ ∈ {x} ∧ (x₀ . f . y)) =>
                  let res₂ := in_singl_elem x x₀ (And.left hx₀)
                  let eq_subst_res := eq_subst (fun (t) => (t . f . y)) x₀ x (res₂) (And.right hx₀)
                  let dom_prop₁ := Iff.mpr (dom_prop f x) (Exists.intro y (eq_subst_res))
                  hund (dom_prop₁)

            )
        let s := Iff.mp (subs_subs_eq (f.[ { x } ]) ∅) (And.intro (
          fun (m) =>
            fun (hm : m ∈ (f.[ { x } ])) =>
              False.elim (r m (hm))
        ) (empty_set_is_subset_any (f.[ { x } ])))
        eq_subst (fun (t) => ⋃ t = ∅) (∅) (f.[ { x } ]) (Eq.symm (s)) (union_empty)





noncomputable def part_same_val (f g x y : Set) : Prop := ((f ↑↑ x) ∧ g ↑↑ y) ∨ (((f ↓↓ x) ∧ (g ↓↓ y)) ∧ (f⦅x⦆ = g⦅y⦆))


syntax term "（" term "）" "≈" term "﹙" term "﹚" : term

macro_rules
  | `($f:term （ $x:term ） ≈ $g:term ﹙ $y:term ﹚) => `(part_same_val $f $g $x $y)





theorem partial_equal_functions : ∀ f g A B C D, (f PartFun A To B) → (g PartFun C To D) → ((f = g) ↔ (∀ x, (f（x） ≈ g﹙x﹚))) :=
  fun (f g A B C D) => fun (h₁ : f PartFun A To B) => fun (h₂ : g PartFun C To D) =>
    Iff.intro
    (
      fun (prop₁ : f = g) =>
        fun (x) =>
        Or.elim (em (f ↓↓ x))
        (
          fun (s : f ↓↓ x) =>
            let first := eq_subst (fun (u) => u ↓↓ x) f g (prop₁) (s)
            (Or.inr : ((f ↓↓ x) ∧ (g ↓↓ x)) ∧ (f⦅x⦆ = g⦅x⦆)  → f（x） ≈ g﹙x﹚) (
              And.intro (And.intro (s) (first)) (eq_subst (fun (u) => f⦅x⦆ = u⦅x⦆) f g prop₁ (Eq.refl (f⦅x⦆)))
            )

        )
        (
          fun (s : f ↑↑ x) =>
            let first := eq_subst (fun (u) => u ↑↑ x) f g (prop₁) (s)
            (Or.inl : ((f ↑↑ x) ∧ (g ↑↑ x)) → f（x） ≈ g﹙x﹚) (And.intro (s) (first))
        )

    )
    (
      fun (prop₁ : ∀ x, (f（x） ≈ g﹙x﹚)) =>
        relation_equality f g (And.left (prop_then_binary_relation A B f (And.left h₁))) (And.left (prop_then_binary_relation C D g (And.left h₂))) (fun (x) => fun (y) =>
          Iff.intro
          (
            fun (prop₂ : (x . f . y)) =>
              let first: f ↓↓ x := Iff.mpr (dom_prop f x) (Exists.intro y prop₂)
              let second := prop₁ x
              Or.elim second
              (
                fun (t : (f ↑↑ x) ∧ g ↑↑ x) =>
                  (False.elim : False → (x . g . y)) (And.left t (first))
              )
              (
                fun (t : ((f ↓↓ x) ∧ (g ↓↓ x)) ∧ (f⦅x⦆ = g⦅x⦆)) =>
                  let third := And.right t
                  let h₃ := And.left (And.left t)
                  let fourth := Iff.mp (partial_function_equal_value_prop f A B h₁ x y h₃) prop₂
                  let fifth := eq_subst (fun (u) => u = g⦅x⦆) (f⦅x⦆) y (Eq.symm fourth) (third)
                  Iff.mpr (partial_function_equal_value_prop g C D h₂ x y (And.right (And.left t))) fifth
              )
          )
          (
            fun (prop₂ : (x . g . y)) =>
              let first: g ↓↓ x := Iff.mpr (dom_prop g x) (Exists.intro y prop₂)
              let second := prop₁ x
              Or.elim second
              (
                fun (t : (f ↑↑ x) ∧ g ↑↑ x) =>
                  (False.elim : False → (x . f . y)) (And.right t (first))
              )
              (
                fun (t : ((f ↓↓ x) ∧ (g ↓↓ x)) ∧ (f⦅x⦆ = g⦅x⦆)) =>
                  let third := And.right t
                  let h₃ := And.right (And.left t)
                  let fourth := Iff.mp (partial_function_equal_value_prop g C D h₂ x y h₃) prop₂
                  let fifth := eq_subst (fun (u) => u = f⦅x⦆) (g⦅x⦆) y (Eq.symm fourth) (Eq.symm third)
                  Iff.mpr (partial_function_equal_value_prop f A B h₁ x y (And.left (And.left t))) fifth
              )
          )
        )

    )



theorem equal_functions_abcd : ∀ f g A B C D, (f Fun A To B) → (g Fun C To D) → ((f = g) ↔ (dom f = dom g ∧ ∀ x, f⦅x⦆ = g⦅x⦆)) :=
  fun (f g A B C D) => fun (h₁ : f Fun A To B) => fun (h₂ : g Fun C To D) =>
    Iff.intro
    (
      fun (t : f = g) =>
        And.intro
        (
          eq_subst (fun (u) => dom f = dom u) f g (t) (Eq.refl (dom f))
        )
        (
        fun (x) =>
          eq_subst (fun (u) => (f⦅x⦆ = u⦅x⦆)) (f) (g) (t) (Eq.refl (f⦅x⦆))
        )
    )
    (
      fun (t : dom f = dom g ∧ ∀ x, f⦅x⦆ = g⦅x⦆) =>
        Iff.mpr (partial_equal_functions f g A B C D (And.left h₁) (And.left h₂)) (fun (x) =>
            Or.elim (em (f ↓↓ x))
            (
              fun (r : f ↓↓ x) =>
                let first: g ↓↓ x := eq_subst (fun (u) => x ∈ u) (dom f) (dom g) (And.left t) (r)
                (Or.inr : ((f ↓↓ x) ∧ (g ↓↓ x)) ∧ (f⦅x⦆ = g⦅x⦆)  → f（x） ≈ g﹙x﹚) (And.intro (And.intro (r) (first)) (And.right t x))
            )
            (
              fun (r: f ↑↑ x) =>
                let first: g ↑↑ x := eq_subst (fun (u) => x ∉ u) (dom f) (dom g) (And.left t) (r)
                (Or.inl : ((f ↑↑ x) ∧ (g ↑↑ x)) → f（x） ≈ g﹙x﹚) (And.intro (r) (first))
            )
        )

    )


theorem equal_functions_abc: ∀ f g A B C, (f Fun A To B) → (g Fun A To C) → ((f = g) ↔ (∀ x, f⦅x⦆ = g⦅x⦆)) :=
  fun (f g A B C) => fun (h₁ : f Fun A To B) => fun (h₂ : g Fun A To C) =>
    Iff.intro
    (
      fun (t : f = g) =>
        And.right (Iff.mp (equal_functions_abcd f g A B A C (h₁) (h₂)) (t))
    )
    (
      fun (t : ∀ x, f⦅x⦆ = g⦅x⦆) =>
        Iff.mpr (equal_functions_abcd f g A B A C (h₁) (h₂))
        (And.intro (eq_subst (fun (u) => dom f = u) A (dom g) (dom_function g A C h₂) (Eq.symm (dom_function f A B h₁))) (t))
    )


theorem equal_functions_abc_A:  ∀ f g A B C, (f Fun A To B) → (g Fun A To C) → ((f = g) ↔ (∀ x ∈ A; f⦅x⦆ = g⦅x⦆)) :=
    fun (f g A B C) => fun (h₁ : f Fun A To B) => fun (h₂ : g Fun A To C) =>
    Iff.intro
    (
      fun (t : f = g) =>
        fun (x) => fun (_ : x ∈ A) =>
          Iff.mp (equal_functions_abc f g A B C h₁ h₂) t x
    )
    (
      fun (t : ∀ x ∈ A; f⦅x⦆ = g⦅x⦆) =>
        Iff.mpr (equal_functions_abc f g A B C h₁ h₂) (
          fun (x) =>
            Or.elim (em (x ∈ A))
            (
              fun (hx : x ∈ A) =>
                t x hx
            )
            (
              fun (hx : x ∉ A) =>
                let u := partial_function_value_pick_property_undefined f A B x (And.left h₁)
                let v := dom_function f A B h₁
                let s := u (eq_subst (fun (t) => x ∉ t) A (dom f) (v) hx)
                let v₂ := dom_function g A C h₂
                let u₂ := partial_function_value_pick_property_undefined g A C x (And.left h₂)
                let s₂ := u₂ (eq_subst (fun (t) => x ∉ t) A (dom g) v₂ hx)
                Eq.trans (s) (Eq.symm (s₂))

            )
        )
    )


theorem part_fun_val_image_prop : ∀ f A B, (f PartFun A To B) → ∀ x y, (x ∈ dom f) → ((f⦅x⦆ = y) ↔ (f.[{x}] = {y})) :=
  fun (f A B) => fun (h₁ : f PartFun A To B) => fun (x y) => fun (h₂ : x ∈ dom f) =>
  Iff.intro
  (
    fun (h₃ : f⦅x⦆ = y) =>
      extensionality (f.[{x}]) ({y}) (
          fun (s) =>
          Iff.intro
          (
            fun (h₄ : s ∈ f.[{x}]) =>
              let first := Iff.mp (specification_set_is_specification (fun (u) => ∃ a ∈ {x}; (a . f . u)) (rng f) s) h₄
              Exists.elim (And.right (first))
              (
                fun (w) =>
                  fun (hw : w ∈ {x} ∧ (w . f . s)) =>
                    let first := in_singl_elem x w (And.left hw)
                    let second: (x . f . s) := eq_subst (fun (u) => (u . f . s)) w x (first) (And.right hw)
                    let third := And.right h₁ x s y second (Iff.mpr (partial_function_equal_value_prop f A B h₁ x y (h₂)) (Eq.symm (h₃)))
                    eq_subst (fun (u) => u ∈ {y}) y s (Eq.symm third) (elem_in_singl y)

              )
          )
          (
            fun (h₄ : s ∈ {y}) =>
              let first := in_singl_elem y s h₄

              eq_subst (fun (u) => u ∈ f.[{x}]) y s (Eq.symm first)
              (Iff.mpr (specification_set_is_specification (fun (u) => ∃ a ∈ {x}; (a . f . u)) (rng f) y)
                (And.intro (Iff.mpr (rng_prop f y) (Exists.intro x (Iff.mpr (partial_function_equal_value_prop f A B h₁ x y h₂) (Eq.symm h₃))))
                  (Exists.intro x (And.intro (elem_in_singl x) (Iff.mpr (partial_function_equal_value_prop f A B h₁ x y h₂) (Eq.symm h₃)))
                  )

                )
              )
          )
      )
  )
  (
    fun (h₃ : f.[{x}] = {y}) =>
      let first := eq_subst (fun (u) => y ∈ u) ({y}) (f.[{x}]) (Eq.symm h₃) (elem_in_singl y)
      let second := Iff.mp (specification_set_is_specification (fun (u) => ∃ a ∈ {x}; (a . f . u)) (rng f) y) first
      Exists.elim (And.right second)
      (
        fun (w) =>
          fun (hw : w ∈ {x} ∧ (w . f . y)) =>
            let third := in_singl_elem x w (And.left hw)
            let second := eq_subst (fun(u) => (u . f . y)) w x (third) (And.right hw)
            Eq.symm (Iff.mp (partial_function_equal_value_prop f A B h₁ x y h₂) (second))

      )
  )



theorem part_val_in_B : ∀ f A B, (f PartFun A To B) → ∀ x ∈ dom f; f⦅x⦆ ∈ B :=
  fun (f A B) => fun (h₁ : f PartFun A To B) => fun (x) => fun (h₂ : x ∈ dom f) =>
    let h₃ := partial_function_value_pick_property_defined f A B x h₁ h₂
    And.right (Iff.mp (cartesian_product_pair_prop A B x (f⦅x⦆)) (And.left h₁ (x, f⦅x⦆) h₃))


theorem part_val_in_rng : ∀ f A B, (f PartFun A To B) → ∀ x ∈ dom f; f⦅x⦆ ∈ rng f :=
  fun (f A B ) => fun (h₁ : f PartFun A To B) => fun (x) => fun (h₂ : x ∈ dom f) =>
    let h₃ := partial_function_value_pick_property_defined f A B x h₁ h₂
    (Iff.mpr (rng_prop f (f⦅x⦆))) (Exists.intro x (h₃))



theorem val_in_B : ∀ f A B, (f Fun A To B) → ∀ x ∈ A; f⦅x⦆ ∈ B :=
  fun (f A B) => fun (h₁ : f Fun A To B) => fun (x) => fun (h₂ : x ∈ A) =>
    let h₃ := function_value_pick_property f A B x h₂ h₁
    And.right (Iff.mp (cartesian_product_pair_prop A B x (f⦅x⦆)) (And.left (And.left h₁) (x, f⦅x⦆) h₃))


theorem val_in_rng : ∀ f A B, (f Fun A To B) → ∀ x ∈ A; f⦅x⦆ ∈ rng f :=
  fun (f A B) => fun (h₁ : f Fun A To B) => fun (x) => fun (h₂ : x ∈ A) =>
    let h₃ := function_value_pick_property f A B x h₂ h₁
    Iff.mpr (rng_prop f (f⦅x⦆)) (Exists.intro x (h₃))







theorem func_val_image_singl_prop : ∀ f A B, (f Fun A To B) → ∀ x y, (x ∈ A) → ((f⦅x⦆ = y) ↔ (f.[{x}] = {y})) :=
  fun (f A B) => fun (h₁ : f Fun A To B) => fun (x y) => fun (t : x ∈ A) =>
    part_fun_val_image_prop f A B (function_is_partial_function f A B (h₁)) x y (eq_subst (fun (u) => x ∈ u) A (dom f) (dom_function f A B h₁) (t))


theorem part_func_val_preimage_prop : ∀ f A B C, (f PartFun A To B) → ∀ x ∈ dom f; f⦅x⦆ ∈ C ↔ x ∈ f⁻¹.[C] :=
  fun (f A B C) => fun (h₁ : f PartFun A To B) => fun (x) => fun (s : x ∈ dom f) =>
    Iff.intro
    (
      fun (r : f⦅x⦆ ∈ C) =>
        eq_subst (fun (u) => x ∈ u) ({a ∈ dom f | ∃ b ∈ C; (a . f . b)}) (f⁻¹.[C]) (Eq.symm (rel_pre_image_eq C f (And.left (prop_then_binary_relation A B f (And.left h₁))))) (
          Iff.mpr (specification_set_is_specification (fun (u) => ∃ b ∈ C; (u . f . b)) (dom f) x) (And.intro (s) (Exists.intro (f⦅x⦆) (And.intro (r) (partial_function_value_pick_property_defined f A B x (h₁) (s)))))
        )
    )
    (
      fun (r : x ∈ f⁻¹.[C]) =>
        let first := rel_pre_image_eq C f (And.left (prop_then_binary_relation A B f (And.left h₁)))
        let second := eq_subst (fun (u) => x ∈ u) (f⁻¹.[C]) ({a ∈ dom f | ∃ b ∈ C; (a . f . b)}) (first) (r)
        let third := And.right (Iff.mp (specification_set_is_specification (fun (u) =>  ∃ b ∈ C; (u . f . b)) (dom f) x) (second))
        Exists.elim third
        (
          fun (w) =>
            fun (hw : w ∈ C ∧ (x . f . w)) =>
              eq_subst (fun (u) => u ∈ C) w (f⦅x⦆) (And.right h₁ x w (f⦅x⦆) (And.right hw) (partial_function_value_pick_property_defined f A B x (h₁) (s))) (And.left hw)
        )
    )


theorem part_func_img_prop : ∀ f A B, (f PartFun A To B) → ∀ X, f.[X] ⊆ B :=
  fun (f A B) =>
    fun (hf : f PartFun A To B) =>
      fun (X) =>
          let u := rng_partial_function f A B (hf)
          subset_trans_curry (f.[X]) (rng f) (B) (
            let P := fun (b) => ∃ a ∈ X; (a . f . b)
            specification_set_subset P (rng f)
          ) (u)




theorem partial_composition : ∀ f g A B C, (f PartFun A To B) → (g PartFun B To C) → (((g ∘ f) PartFun A To C) ∧ (∀ x ∈ dom f; (g ∘ f)（x） ≈ g﹙f⦅x⦆﹚)) :=
  fun (f g A B C) => fun (h₁ : f PartFun A To B) => fun (h₂ : g PartFun B To C) =>
    let first := And.right h₁
    let second := And.right h₂
    let third := composition_functional g f second first
    let sixth : (g ∘ f) ⊆ (dom f × rng g) := specification_set_subset (fun (u) => ∃ x y, (u = (x, y)) ∧ ∃ z, (x . f . z) ∧ (z . g . y)) (dom f × rng g)
    let seventh := dom_partial_function f A B h₁
    let eighth := rng_partial_function g B C h₂
    let nineth := cartesian_product_subset (dom f) (rng g) (A) C (seventh) (eighth)
    let tenth := subset_trans_curry (g ∘ f) (dom f × rng g) (A × C) (sixth) (nineth)
    let eleventh := And.intro tenth third
    And.intro
    (

      eleventh
    )
    (
      fun (x) =>
        fun (r : x ∈ dom f) =>
          let h₀
          := calc
              dom (g ∘ f) = (g ∘ f)⁻¹.[C] := dom_preimage A C (g ∘ f) (tenth)
              _ =  f⁻¹.[g⁻¹.[C]] := rel_preimage_composition g f C (And.left (prop_then_binary_relation B C g (And.left h₂))) (And.left (prop_then_binary_relation A B f (And.left h₁)))
              _ = f⁻¹.[dom g] := eq_subst (fun (u) => f⁻¹.[g⁻¹.[C]] = f⁻¹.[u]) (g⁻¹.[C]) (dom g) (Eq.symm (dom_preimage B C g (And.left h₂))) (Eq.refl (f⁻¹.[g⁻¹.[C]]))

          let h₃ := Iff.intro (fun (s : (g ∘ f) ↓↓ x) => eq_subst (fun (u) => x ∈ u) (dom (g ∘ f)) (f⁻¹.[dom g]) (h₀) s)
            (fun (s : x ∈ f⁻¹.[dom g]) => eq_subst (fun (u) => x ∈ u) (f⁻¹.[dom g]) (dom (g ∘ f)) (Eq.symm h₀) (s))

          let h₄: (g ↓↓ f⦅x⦆) ↔ (x ∈ f⁻¹.[dom g]) := part_func_val_preimage_prop f A B (dom g) (h₁) x r

          Or.elim (em (x ∈ f⁻¹.[dom g]))
          (
            fun (t : x ∈ f⁻¹.[dom g]) =>
              let h₅ := Iff.mpr (h₄) (t)
              let h₆ := eq_subst (fun (u) => x ∈ u) (f⁻¹.[dom g]) (dom (g ∘ f)) (Eq.symm h₀) (t)
              (Or.inr : ((((g ∘ f)) ↓↓ x) ∧ (g ↓↓ (f⦅x⦆))) ∧ ((g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆)  → (g ∘ f)（x） ≈ g﹙f⦅x⦆﹚)
              (And.intro (And.intro (h₆) (h₅)) (

                let h₇ := rel_pre_image_eq (dom g) f (And.left (prop_then_binary_relation A B f (And.left h₁)))
                let h₈ := eq_subst (fun (u) => x ∈ u) (f⁻¹.[dom g]) ({a ∈ dom f | ∃ b ∈ (dom g); (a . f . b)}) (h₇) (t)
                let h₉ := Iff.mp (specification_set_is_specification (fun (u) => ∃ b ∈ (dom g); (u . f . b)) (dom f) x) h₈
                Exists.elim (And.right h₉)
                (
                  fun (w) =>
                    fun (hw : w ∈ dom g ∧ (x . f . w)) =>
                      let q₁ := Iff.mp (dom_prop g w) (And.left hw)
                      Exists.elim q₁ (
                        fun (u) =>
                          fun (hu : (w . g . u)) =>
                            let a₁ := partial_function_value_pick_property_defined f A B x (h₁) (And.left h₉)
                            let a₂ := (And.right h₁) x w (f⦅x⦆) (And.right hw) a₁
                            let hu₂ := eq_subst (fun (m) => (m . g . u)) (w) (f⦅x⦆) (a₂) (hu)
                            let a₃ := (And.right h₂) (f⦅x⦆) u (g⦅f⦅x⦆⦆) (hu₂) (partial_function_value_pick_property_defined g B C (f⦅x⦆) (h₂) (Iff.mpr h₄ (t)))
                            let a₄ := Iff.mpr (composition_pair_prop g f x u) (Exists.intro w (And.intro (And.right hw) (hu)))
                            let a₅ := Iff.mp (partial_function_equal_value_prop (g ∘ f) A C (eleventh) x u (Iff.mpr (h₃) (t))) (a₄)
                            eq_subst (fun (m) => m = g⦅f⦅x⦆⦆) u ((g ∘ f)⦅x⦆) (a₅) (a₃)
                      )
                )

              ))

          )
          (
            fun (t : x ∉ f⁻¹.[dom g]) =>
              let h₅ : g ↑↑ f⦅x⦆ := fun (u : g ↓↓ f⦅x⦆) => t (Iff.mp (h₄) (u))
              let h₆ : (g ∘ f) ↑↑ x  := eq_subst (fun (u) => x ∉ u) (f⁻¹.[dom g]) (dom (g ∘ f)) (Eq.symm h₀) (t)
              (Or.inl : (((g ∘ f) ↑↑ x ) ∧ (g ↑↑ (f⦅x⦆)))  → (g ∘ f)（x） ≈ g﹙f⦅x⦆﹚) (And.intro (h₆) (h₅))
          )
    )









theorem function_composition : ∀ f g A B C, (f Fun A To B) → (g Fun B To C) → (((g ∘ f) Fun A To C) ∧ (∀ x ∈ dom f; (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆)) :=
  fun (f g A B C) => fun (h₁ : f Fun A To B) => fun (h₂ : g Fun B To C) =>
    let h₃ := partial_composition f g A B C (And.left h₁) (And.left h₂)
    let h₄ := And.left h₃
    let h₅: is_total (g ∘ f) A := fun (x) => fun (t : x ∈ A) => (
          let h₆ := And.right h₁ x t
          Exists.elim h₆
          (
            fun (w) =>
              fun (hw : (x . f . w)) =>
                let h₇ := And.right (Iff.mp (cartesian_product_pair_prop A B x w) ((And.left (And.left h₁) (x, w) hw)))
                let h₈ := And.right h₂ w h₇
                Exists.elim h₈
                (
                  fun (u) =>
                    fun (hu : (w . g . u)) =>
                      let h₉ := Iff.mpr (composition_pair_prop g f x u) (Exists.intro w (And.intro (hw) (hu)))
                      Exists.intro u h₉
                )
            )
        )
    let h₆ : (g ∘ f) Fun A To C := And.intro h₄ h₅
    And.intro
    (
      h₆
    )
    (
      let _ := And.right h₃
      fun (x) => fun (t : x ∈ dom f) =>
        let a₃ := dom_function f A B h₁
        let a₄ := eq_subst (fun (u) => x ∈ u) (dom f) A (Eq.symm a₃) (t)
        let a₅ := dom_function (g ∘ f) A C h₆
        let a₆: (g ∘ f) ↓↓ x := eq_subst (fun (u) => x ∈ u) (A) (dom (g ∘ f)) (a₅) (a₄)
        let a₇ := dom_function g B C h₂
        let a₈ := val_in_B f A B h₁ x a₄
        let _ : g ↓↓ (f⦅x⦆) := eq_subst (fun (u) => f⦅x⦆ ∈ u) (B) (dom g) (a₇) (a₈)
        Or.elim (em ((g ∘ f) ↓↓ x))
        (
          fun (_ : (g ∘ f) ↓↓ x) =>
            let b₁ := And.right h₃ x t
            Or.elim (b₁)
            (
              fun (b₂ : ((g ∘ f) ↑↑ x) ∧ (g ↑↑ f⦅x⦆)) =>
                let b₃ := And.left b₂
                (False.elim : False → (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆) (b₃ (a₆))
            )
            (
              fun (b₂ : (((g ∘ f) ↓↓ x) ∧ (g ↓↓ f⦅x⦆)) ∧ ((g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆)) =>
                And.right b₂
            )

        )
        (
          fun (n : (g ∘ f) ↑↑ x) =>
            (False.elim : False → (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆) (n (a₆))
        )
    )



theorem function_composition_A : ∀ f g A B C, (f Fun A To B) → (g Fun B To C) → (((g ∘ f) Fun A To C) ∧ (∀ x ∈ A; (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆)) :=
  fun (f g A B C) => fun (h : (f Fun A To B)) => fun (h₁ : (g Fun B To C)) =>
    And.intro (And.left (function_composition f g A B C h h₁)) (
      let u := And.right (function_composition f g A B C h h₁)
      eq_subst (fun (t) => ∀ x ∈ t; (g ∘ f)⦅x⦆ = g⦅f⦅x⦆⦆) (dom f) (A) (Eq.symm (dom_function f A B h)) (u)
    )




noncomputable def lam_fun (A B : Set) (P : Set → Set): Set := {z ∈ A × B | ∃ x, z = (x, P x)}

theorem lam_then_part_fun_prop (P : Set → Set) : ∀ A B, (∀ x ∈ dom (lam_fun A B P); P x ∈ B) → ((lam_fun A B P) PartFun A To B) ∧ (∀ x ∈ dom (lam_fun A B P); (lam_fun A B P)⦅x⦆ = P x) :=
  fun (A B) => fun (h) =>
  let lambda := lam_fun A B P
  let h₁ : binary_relation_between A B (lambda) := specification_set_subset (fun (u) => ∃ x, u = (x, P x)) (A × B)
  let h₂ : is_functional lambda := fun (x y z) => fun (g₁ : (x . lambda . y)) => fun (g₂ : (x . (lambda) . z)) => (
      let a₁ := And.right (Iff.mp (specification_set_is_specification (fun (u) => ∃ x, u = (x, P x)) (A × B) (x, y)) (g₁))
      let a₂ := And.right (Iff.mp (specification_set_is_specification (fun (u) => ∃ x, u = (x, P x)) (A × B) (x, z)) (g₂))
      Exists.elim a₁
      (
        fun (w) =>
          fun (hw : (x, y) = (w, P w)) =>
            let b₁ := And.right (Iff.mp (ordered_pair_set_prop x y w (P w)) hw)
            let b₂ := And.left (Iff.mp (ordered_pair_set_prop x y w (P w)) hw)
            let b₃ : y = P x := eq_subst (fun (u) => y = P u) w x (Eq.symm b₂) (b₁)

            Exists.elim a₂
            (
              fun (u) =>
                fun (hu : (x, z) = (u, P u)) =>
                let b₄ :=  And.right (Iff.mp (ordered_pair_set_prop x z u (P u)) hu)
                let b₅ := And.left (Iff.mp (ordered_pair_set_prop x z u (P u)) hu)
                let b₆: z = P x := eq_subst (fun (t) => z = P t) u x (Eq.symm b₅) (b₄)
                eq_subst (fun (t) => y = t) (P x) (z) (Eq.symm b₆) (b₃)
            )
      )
    )
    let h₃ := And.intro h₁ h₂
    let h₄ := fun (x) => fun (g : (x ∈ dom lambda)) =>
      Eq.symm
        (Iff.mp
          (partial_function_equal_value_prop lambda A B h₃ x (P x) g)
            (Iff.mpr (specification_set_is_specification (fun (u) => ∃ x, u = (x, P x)) (A × B) (x, P x))
              (And.intro (Iff.mpr (cartesian_product_pair_prop A B x (P x)) (And.intro (dom_partial_function lambda A B h₃ x g) (h x g))) (Exists.intro x (Eq.refl (x, P x))))
          )
        )
    And.intro h₃ h₄




theorem lam_then_fun_prop (P : Set → Set) : ∀ A B, (∀ x ∈ A; P x ∈ B) →  (((lam_fun A B P) Fun A To B) ∧ (∀ x ∈ A; (lam_fun A B P)⦅x⦆ = P x)) :=
    fun (A B) => fun (h) =>
    let lambda := lam_fun A B P
    let h₁ : binary_relation_between A B (lambda) := specification_set_subset (fun (u) => ∃ x, u = (x, P x)) (A × B)
    let h₂ : is_functional lambda := fun (x y z) => fun (g₁ : (x . lambda . y)) => fun (g₂ : (x . (lambda) . z)) => (
      let a₁ := And.right (Iff.mp (specification_set_is_specification (fun (u) => ∃ x, u = (x, P x)) (A × B) (x, y)) (g₁))
      let a₂ := And.right (Iff.mp (specification_set_is_specification (fun (u) => ∃ x, u = (x, P x)) (A × B) (x, z)) (g₂))
      Exists.elim a₁
      (
        fun (w) =>
          fun (hw : (x, y) = (w, P w)) =>
            let b₁ := And.right (Iff.mp (ordered_pair_set_prop x y w (P w)) hw)
            let b₂ := And.left (Iff.mp (ordered_pair_set_prop x y w (P w)) hw)
            let b₃ : y = P x := eq_subst (fun (u) => y = P u) w x (Eq.symm b₂) (b₁)

            Exists.elim a₂
            (
              fun (u) =>
                fun (hu : (x, z) = (u, P u)) =>
                let b₄ :=  And.right (Iff.mp (ordered_pair_set_prop x z u (P u)) hu)
                let b₅ := And.left (Iff.mp (ordered_pair_set_prop x z u (P u)) hu)
                let b₆: z = P x := eq_subst (fun (t) => z = P t) u x (Eq.symm b₅) (b₄)
                eq_subst (fun (t) => y = t) (P x) (z) (Eq.symm b₆) (b₃)
            )
      )
    )
    let h₃ : is_total lambda A := fun (x) => fun (g : x ∈ A) => Exists.intro (P x) (Iff.mpr (specification_set_is_specification (fun (t) => ∃ x, t = (x, P x)) (A × B) (x, P x)) (And.intro (Iff.mpr (cartesian_product_pair_prop A B x (P x)) (And.intro (g) (h x g))) (Exists.intro x (Eq.refl (x, P x)))))
    let h₄ : lambda Fun A To B := And.intro (And.intro (h₁) (h₂)) (h₃)
    let h₅ := fun (x) => fun (g : x ∈ A) => Eq.symm (Iff.mp (function_equal_value_prop lambda A B h₄ x (P x) g) (Iff.mpr ((specification_set_is_specification (fun (t) => ∃ x, t = (x, P x)) (A × B) (x, P x))) (And.intro (Iff.mpr (cartesian_product_pair_prop A B x (P x)) (And.intro (g) (h x g))) (Exists.intro x (Eq.refl (x, P x))))))
    And.intro (h₄) (h₅)


open Classical


theorem prop_then_lam_part_fun (P : Set → Set) : ∀ A B f, (f PartFun A To B) → (∀ x ∈ dom f; f⦅x⦆ = P x) → (∀ x, x ∉ dom f → (P x ∉ B)) → (f = lam_fun A B P) :=
  fun (A B f) => fun (g : f PartFun A To B) => fun (h : ∀ x ∈ dom f; (f⦅x⦆ = P x)) => fun (r : ∀ x, x ∉ dom f → (P x ∉ B)) =>
    extensionality f (lam_fun A B P) (
      fun (x) =>
        Iff.intro
        (
          fun (s : x ∈ f) =>
            let h₁ := Iff.mp (cartesian_product_is_cartesian A B x) (And.left (g) x s)
            Exists.elim h₁
            (
              fun (w) =>
                fun (hw : w ∈ A ∧ ∃ u ∈ B; x = (w, u)) =>
                  Exists.elim (And.right hw)
                  (
                    fun (u) =>
                      fun (hu : u ∈ B ∧ x = (w, u)) =>
                        let h₀ := Iff.mpr (dom_prop f w) (Exists.intro u (eq_subst (fun (i) => i ∈ f) x (w, u) (And.right hu) (s)))
                        let h₂ := Iff.mp (partial_function_equal_value_prop f A B g w u h₀) (eq_subst (fun (i) => i ∈ f) x (w, u) (And.right hu) (s))
                        let h₃ := h w h₀
                        let h₄ := eq_subst (fun (m) => u = m) (f⦅w⦆) (P w) (h₃) (h₂)
                        let h₅ := eq_subst (fun (m) => x = (w, m)) u (P w) (h₄) (And.right hu)

                        Iff.mpr (specification_set_is_specification (fun (u) => ∃ t, u = (t, P t)) (A × B) x) (And.intro (And.left (g) x s) (Exists.intro w (h₅)))
                  )
            )
        )
        (
          fun (t : x ∈ (lam_fun A B P)) =>
            let h₁ := Iff.mp (specification_set_is_specification (fun (u) => ∃ t, u = (t, P t)) (A × B) x) t
            let h₂ := And.left h₁
            let h₃ := And.right h₁
            Exists.elim h₃
            (
              fun (w) =>
                fun (hw : x = (w, P w)) =>
                  let h₅ := And.right (Iff.mp (cartesian_product_pair_prop A B w (P w)) (eq_subst (fun (u) => u ∈ (A × B)) x (w, P w) (hw) (h₂)))
                  let h₆ := byContradiction (fun (m : w ∉ dom f) => r w m h₅)
                  let h₄ := Iff.mpr (partial_function_equal_value_prop f A B g w (P w) (h₆)) (Eq.symm (h w h₆))

                  eq_subst (fun (u) => u ∈ f) (w, P w) x (Eq.symm (hw)) (h₄)
            )
        )
    )


theorem prop_then_lam_fun (P : Set → Set) : ∀ A B f, (f Fun A To B) → (∀ x ∈ A; (f⦅x⦆ = P x)) → (f = lam_fun A B P) :=
  fun (A B f) => fun (g : f Fun A To B) => fun (h : ∀ x ∈ A; (f⦅x⦆ = P x)) =>
    extensionality f (lam_fun A B P) (
      fun (x) =>
        Iff.intro
        (
          fun (t : x ∈ f) =>
            let h₁ := Iff.mp (cartesian_product_is_cartesian A B x) (And.left (And.left g) x t)
            Exists.elim h₁
            (
              fun (w) =>
                fun (hw : w ∈ A ∧ ∃ u ∈ B; x = (w, u)) =>
                  Exists.elim (And.right hw)
                  (
                    fun (u) =>
                      fun (hu : u ∈ B ∧ x = (w, u)) =>
                        let h₂ := Iff.mp (function_equal_value_prop f A B g w u (And.left hw)) (eq_subst (fun (i) => i ∈ f) x (w, u) (And.right hu) (t))
                        let h₃ := h w (And.left hw)
                        let h₄ := eq_subst (fun (m) => u = m) (f⦅w⦆) (P w) (h₃) (h₂)
                        let h₅ := eq_subst (fun (m) => x = (w, m)) u (P w) (h₄) (And.right hu)

                        Iff.mpr (specification_set_is_specification (fun (u) => ∃ t, u = (t, P t)) (A × B) x) (And.intro (And.left (And.left g) x t) (Exists.intro w (h₅)))
                  )
            )


        )
        (
          fun (t : x ∈ (lam_fun A B P)) =>
            let h₁ := Iff.mp (specification_set_is_specification (fun (u) => ∃ t, u = (t, P t)) (A × B) x) t
            let h₂ := And.left h₁
            let h₃ := And.right h₁
            Exists.elim h₃
            (
              fun (w) =>
                fun (hw : x = (w, P w)) =>
                  let h₀ := And.left (Iff.mp (cartesian_product_pair_prop A B w (P w)) (eq_subst (fun (u) => u ∈ (A × B)) x (w, P w) (hw) (h₂)))

                  let h₄ := Iff.mpr (function_equal_value_prop f A B g w (P w) (h₀)) (Eq.symm (h w h₀))
                  eq_subst (fun (u) => u ∈ f) (w, P w) x (Eq.symm (hw)) (h₄)
            )
        )
    )


noncomputable def lam_cond_fun (A B : Set) (P : Set → Prop) (c d : Set → Set) :=
  {z ∈ A × B | ∃ x, (P x → z = (x, c x)) ∧ (¬P x → z = (x, d x))}



theorem lam_cond_part_fun_prop : ∀ A B : Set, ∀ P : Set → Prop, ∀ c d : Set → Set,
  ((lam_cond_fun A B P c d) PartFun A To B) ∧
  (∀ x ∈ dom (lam_cond_fun A B P c d) ;
  (P x → (lam_cond_fun A B P c d)⦅x⦆ = c x) ∧ (¬P x → (lam_cond_fun A B P c d)⦅x⦆ = d x)) :=



  fun (A B : Set) => fun (P : Set → Prop) => fun (c d : Set → Set) =>
      let pred := fun (u) => ∃ x, (P x → u = (x, c x)) ∧ (¬P x → u = (x, d x))
      let part_func := (
      (And.intro (specification_set_subset pred (A × B))
      (fun (x y z) => fun (h₁ : (x . (lam_cond_fun A B P c d) . y)) =>
                      fun (h₂ : (x . (lam_cond_fun A B P c d) . z)) =>
        let h₃ := And.right (Iff.mp (specification_set_is_specification pred (A × B) (x, y)) (h₁))
        let h₄ := And.right (Iff.mp (specification_set_is_specification pred (A × B) (x, z)) (h₂))
        Exists.elim h₃
        (
          fun (w) =>
            fun (hw : (P w → (x, y) = (w, c w)) ∧ (¬P w → (x, y) = (w, d w))) =>
              Exists.elim h₄
              (
                fun (u) =>
                  fun (hu : (P u → (x, z) = (u, c u)) ∧ (¬P u → (x, z) = (u, d u))) =>
                    Or.elim (em (P w))
                        (fun (h₅ : P w) =>
                          Or.elim (em (P u))
                            (fun (h₆ : P u) =>
                              let h₇ := And.left hw h₅
                              let h₈ := Iff.mp (ordered_pair_set_prop x y w (c w)) h₇
                              let h₉ := And.left hu h₆
                              let h₀ := Iff.mp (ordered_pair_set_prop x z u (c u)) h₉
                              Eq.trans (And.right h₈)
                              (Eq.symm
                              (eq_subst (fun (t) => z = c t) u w
                              (Eq.trans (Eq.symm (And.left h₀)) (And.left h₈))
                                (And.right h₀))
                              )
                            )
                            (fun (h₆ : ¬P u) =>
                              let h₇ := And.left hw h₅
                              let h₈ := Iff.mp (ordered_pair_set_prop x y w (c w)) h₇
                              let h₉ := And.right hu h₆
                              let h₀ := Iff.mp (ordered_pair_set_prop x z u (d u)) h₉
                              (False.elim : False → (y = z)) (h₆ (eq_subst (fun (t) => P t) w u (Eq.trans (Eq.symm (And.left h₈)) (And.left h₀)) (h₅)))

                            )

                        )
                        (fun (h₅ : ¬P w) =>
                            Or.elim (em (P u))
                              (fun (h₆ : P u) =>
                                let h₇ := And.right hw h₅
                                let h₈ := Iff.mp (ordered_pair_set_prop x y w (d w)) h₇
                                let h₉ := And.left hu h₆
                                let h₀ := Iff.mp (ordered_pair_set_prop x z u (c u)) h₉
                                (False.elim : False → (y = z)) (h₅ (eq_subst (fun (t) => P t) u w (Eq.trans (Eq.symm (And.left h₀)) (And.left h₈)) (h₆)))
                              )
                              (fun (h₆ : ¬P u) =>
                                let h₇ := And.right hw h₅
                                let h₈ := Iff.mp (ordered_pair_set_prop x y w (d w)) h₇
                                let h₉ := And.right hu h₆
                                let h₀ := Iff.mp (ordered_pair_set_prop x z u (d u)) h₉
                                Eq.trans (And.right h₈)
                                (Eq.symm
                                (eq_subst (fun (t) => z = d t) u w
                                (Eq.trans (Eq.symm (And.left h₀)) (And.left h₈))
                                  (And.right h₀))
                                )
                            )
                        )


              )
        )

      ))
      )
     And.intro (part_func) (
          fun (x) => fun (g : x ∈ dom (lam_cond_fun A B P c d)) =>
            And.intro (
              fun (h₀ : P x) =>
                Eq.symm (Iff.mp (partial_function_equal_value_prop (lam_cond_fun A B P c d) A B (part_func) x (c x) g) (
                  let s := Iff.mp (dom_prop (lam_cond_fun A B P c d) x) g
                  Exists.elim s
                  (
                    fun (w) =>
                      fun (hw : (x, w) ∈ (lam_cond_fun A B P c d)) =>
                        let t := And.right (Iff.mp (specification_set_is_specification pred (A × B) (x, w)) hw)
                        Exists.elim t
                        (
                          fun (u) =>
                            fun (hu : ((P u → (x, w) = (u, c u)) ∧ (¬P u → (x, w) = (u, d u)))) =>
                              Or.elim (em (P u))
                              (fun (e : P u) =>
                                let m := And.left hu e
                                let n := Iff.mp (ordered_pair_set_prop x w u (c u)) m
                                eq_subst (fun (l) => (x, l) ∈  (lam_cond_fun A B P c d)) w (c x) (
                                  eq_subst (fun (o) => w = c o) u x (Eq.symm (And.left n)) (And.right n)
                                ) (hw)
                              )
                              (fun (e : ¬P u) =>
                                let m := And.right hu e
                                let n := Iff.mp (ordered_pair_set_prop x w u (d u)) m
                                (False.elim : False → (x, c x) ∈ (lam_cond_fun A B P c d)) (
                                  e (eq_subst (fun (l) => P l) x u (And.left n) (h₀))
                                )

                              )
                        )
                  )
                ))
            ) (
              fun (h₀ : ¬ P x) =>
                Eq.symm (Iff.mp (partial_function_equal_value_prop (lam_cond_fun A B P c d) A B (part_func) x (d x) g) (
                    let s:= Iff.mp (dom_prop (lam_cond_fun A B P c d) x) (g)
                    Exists.elim s
                    (
                      fun (w) =>
                        fun (hw : (x, w) ∈ (lam_cond_fun A B P c d)) =>
                          let t := And.right (Iff.mp (specification_set_is_specification pred (A × B) (x, w)) hw)
                          Exists.elim t
                          (
                            fun (u) =>
                              fun (hu : ((P u → (x, w) = (u, c u)) ∧ (¬P u → (x, w) = (u, d u)))) =>
                                 Or.elim (em (P u))
                                 (fun (e : P u) =>
                                    let m := And.left hu e
                                    let n := Iff.mp (ordered_pair_set_prop x w u (c u)) m
                                    (False.elim : False → (x, d x) ∈ (lam_cond_fun A B P c d)) (
                                      h₀ (eq_subst (fun (l) => P l) u x (Eq.symm (And.left n)) (e))
                                    )
                                 )
                                 (fun (e : ¬P u) =>
                                    let m := And.right hu e
                                    let n := Iff.mp (ordered_pair_set_prop x w u (d u)) m
                                    eq_subst (fun (l) => (x, l) ∈ (lam_cond_fun A B P c d)) w (d x) (
                                      eq_subst (fun (l) => w = d l) u x (Eq.symm (And.left n)) (And.right n)
                                    ) (hw)
                                 )
                          )
                    )
                ))
            )
     )


theorem lam_cond_fun_prop : ∀ A B : Set, ∀ P : Set → Prop, ∀ c d : Set → Set,
  (∀ x ∈ A; (P x → c x ∈ B) ∧ (¬P x → d x ∈ B)) →
  ((lam_cond_fun A B P c d) Fun A To B) ∧
  (∀ x ∈ A ; (P x → (lam_cond_fun A B P c d)⦅x⦆ = c x) ∧ (¬P x → (lam_cond_fun A B P c d)⦅x⦆ = d x)) :=
    fun (A B : Set) => fun (P : Set → Prop) => fun (c d : Set → Set) =>
      fun (h : ∀ x ∈ A; (P x → c x ∈ B) ∧ (¬P x → d x ∈ B)) =>
      let pred := fun (u) => ∃ x, (P x → u = (x, c x)) ∧ (¬P x → u = (x, d x))

      let part_func_prop := And.left (lam_cond_part_fun_prop A B P c d)
      let total_prop : is_total (lam_cond_fun A B P c d) A := fun (x) => fun (h₁ : x ∈ A) =>
        Or.elim (em (P x))
        (fun (h₂ : P x) =>
          let h₃ := Iff.mpr (specification_set_is_specification pred (A × B) (x, c x))

          let h₄ := (And.intro (
            Iff.mpr (cartesian_product_pair_prop A B x (c x)) (And.intro (h₁) (And.left (h x h₁) (h₂)))
          ) (
            let n : pred (x, c x) := Exists.intro x
              (And.intro (
                  fun (_ : P x) => Eq.refl (x, c x)
              ) (
                  fun (h₆ : ¬P x) => (False.elim : False → (x, c x) = (x, d x)) (h₆ h₂)
              ))
            n
          ))

          let h₇ := h₃ h₄
          Exists.intro (c x) (h₇)
        )
        (
          fun (h₂ : ¬P x) =>

            let h₃ := Iff.mpr (specification_set_is_specification pred (A × B) (x, d x))

            let h₄ := (And.intro (
            Iff.mpr (cartesian_product_pair_prop A B x (d x)) (And.intro (h₁) (And.right (h x h₁) (h₂)))
          ) (
            let n : pred (x, d x) := Exists.intro x
              (And.intro (
                  fun (h₅ : P x) => (False.elim : False → (x, d x) = (x, c x)) (h₂ h₅)
              ) (
                  fun (_ : ¬P x) => Eq.refl (x, d x)
              ))
            n
          ))

          let h₇ := h₃ h₄
          Exists.intro (d x) (h₇)
        )
      let fun_lam_cond := And.intro (part_func_prop) (total_prop)
      let dom_prop_h := dom_function (lam_cond_fun A B P c d) A B (fun_lam_cond)

      And.intro (fun_lam_cond) (
        fun (x) => fun (hx : x ∈ A) =>
          And.right ((lam_cond_part_fun_prop A B P c d)) x (
            eq_subst (fun (m) => x ∈ m) A (dom (lam_cond_fun A B P c d)) (dom_prop_h) (hx)
          )
      )






noncomputable def fun_restriction (f A : Set) := f ∩ (A × rng f)
infix:50 (priority := high) "⨡" => fun_restriction


theorem part_fun_restriction_prop : ∀ A B X f, (f PartFun A To B) → (f ⨡ X) PartFun X To B :=
  fun (A B X f) => fun(r : f PartFun A To B) =>
    let h₁ : binary_relation_between X B (f ⨡ X) := fun (x) => fun (t : x ∈ (f ⨡ X)) => (
      let h₂ := Iff.mp (intersect_2sets_prop f (X × rng f) x) t
      let h₄ := And.right h₂
      let h₆ := Iff.mp (cartesian_product_is_cartesian X (rng f) x) h₄
      Exists.elim h₆
      (
        fun (w) =>
          fun (hw : w ∈ X ∧ (∃ u ∈ rng f; x = (w, u))) =>
            Exists.elim (And.right hw)
            (
              fun (u) =>
                fun (hu : u ∈ rng f ∧ x = (w, u)) =>
                  let h₇ := rng_partial_function f A B r u (And.left hu)
                  let h₈ : ∃ w ∈ X; ∃ u ∈ B; x = (w, u) := Exists.intro w (And.intro (And.left hw) (Exists.intro u (And.intro (h₇) (And.right hu))))
                  Iff.mpr (cartesian_product_is_cartesian X B x) h₈

            )
      )
    )
    let h₂ := fun (x) => fun (y) => fun (z) => fun (h : (x . (f ⨡ X) . y)) => fun (g : (x . (f ⨡ X) . z)) => (
      let h₃ := And.left (intersect_2sets_subset_prop f (X × rng f)) (x, y) h
      let h₄ := And.left (intersect_2sets_subset_prop f (X × rng f)) (x, z) g
      And.right r x y z h₃ h₄
    )
    And.intro (h₁) (h₂)



theorem part_fun_restriction_dom_subs_prop : ∀ A B X f, (X ⊆ dom f) →  (f PartFun A To B) → (f ⨡ X) Fun X To B :=
  fun (A B X f) => fun (h : X ⊆ dom f) => fun (r : f PartFun A To B) =>
    let h₁ := part_fun_restriction_prop A B X f r
    let h₂ : X ⊆ dom (f ⨡ X) := fun (x) => fun (t : x ∈ X) => Iff.mpr (dom_prop (f ⨡ X) x)
     (Exists.intro (f⦅x⦆) ((Iff.mpr (intersect_2sets_prop f (X × rng f) (x, (f⦅x⦆))))
     (And.intro (partial_function_value_pick_property_defined f A B x r (h x t)) ((Iff.mpr (cartesian_product_pair_prop X (rng f) x (f⦅x⦆))) (And.intro (t) (part_val_in_rng f A B r x (h x t)))))))
    let h₃ : ∀ x ∈ X; ∃ y, (x . (f ⨡ X) . y) := fun (x) => fun (t : x ∈ X) => Exists.intro ((f ⨡ X)⦅x⦆) (partial_function_value_pick_property_defined (f ⨡ X) X B x h₁ (h₂ x t))
    And.intro (h₁) (h₃)


theorem fun_restriction_prop : ∀ A B X f, (f Fun A To B) → (f ⨡ X) Fun (A ∩ X) To B :=
  fun (A B X f) => fun (r : f Fun A To B) =>
    let h₁ := part_fun_restriction_dom_subs_prop A B (A ∩ X) f (eq_subst (fun (u) => (A ∩ X) ⊆ u) (A) (dom f) (dom_function f A B r) (And.left (intersect_2sets_subset_prop A X))) (And.left r)
    let h₂ : (f ⨡ (A ∩ X)) = (f ⨡ X) := extensionality (f ⨡ (A ∩ X)) (f ⨡ X) (fun (x) => (Iff.intro (
        fun (s : x ∈ (f ⨡ (A ∩ X))) =>
          let h₄ := Iff.mp (intersect_2sets_prop f ((A ∩ X) × (rng f)) x) s
          let h₅ := And.right h₄
          let h₆ := cartesian_product_subset (A ∩ X) (rng f) (X) (rng f) (And.right (intersect_2sets_subset_prop A X)) (subset_refl (rng f))
          let h₇ := h₆ x h₅
          Iff.mpr (intersect_2sets_prop f (X × (rng f)) x) (And.intro (And.left h₄) (h₇))

    ) (
      fun (s : x ∈ (f ⨡ X)) =>
        let h₇ := Iff.mp (intersect_2sets_prop f (X × rng f) x) s
        let h₈ := And.right h₇
        let h₉ := Iff.mp (cartesian_product_is_cartesian X (rng f) x) h₈
        Exists.elim h₉
        (
          fun (w) =>
            fun (hw : w ∈ X ∧ ∃ u ∈ (rng f); x = (w, u)) =>
              Exists.elim (And.right hw)
              (
                fun (u) =>
                  fun (hu : u ∈ (rng f) ∧ x = (w, u)) =>


                    let v₂ := And.left h₇
                    let v₃ := eq_subst (fun (p) => p ∈ f) x (w, u) (And.right hu) (v₂)
                    let v₄ := And.left (And.left r) (w, u) v₃
                    let v₅ := And.left (Iff.mp (cartesian_product_pair_prop A B w u) v₄)
                    let g₁ := Iff.mpr (cartesian_product_is_cartesian A (rng f) x) (Exists.intro w (And.intro (v₅) (Exists.intro u (And.intro (And.left hu) (And.right hu)))))
                    let g₂ := cartesian_product_intersect A (rng f) X (rng f) x (Iff.mpr (intersect_2sets_prop (A × rng f) (X × rng f) x)
                    (And.intro (g₁) (h₈)))
                    let g₃ := eq_subst (fun (p) => x ∈ p) ((A ∩ X) × ((rng f) ∩ (rng f))) ((A ∩ X) × (rng f)) (
                      eq_subst (fun (p) => ((A ∩ X) × ((rng f) ∩ (rng f))) = (A ∩ X) × p) ((rng f) ∩ (rng f)) (rng f) (intersect_2_sets_idemp (rng f)) (Eq.refl (((A ∩ X) × ((rng f) ∩ (rng f)))))
                    ) (g₂)
                    Iff.mpr (intersect_2sets_prop f ((A ∩ X) × rng f) x) (And.intro (And.left h₇) (g₃))

              )

        )



    )))
    eq_subst (fun (u) => u Fun (A ∩ X) To B) (f ⨡ (A ∩ X)) (f ⨡ X) (h₂) (h₁)



theorem inj_restriction_prop : ∀ X f, (is_injective f) → (is_injective (f ⨡ X)) :=
  fun (X f) => fun (h₁ : is_injective f) =>
    fun (a b c) => fun (h₂ : (a . (f ⨡ X) . c)) => fun (h₃ : (b . (f  ⨡ X) . c)) =>
      h₁ a b c (And.left (Iff.mp (intersect_2sets_prop f (X × rng f) (a, c)) (h₂))) (And.left (Iff.mp (intersect_2sets_prop f (X × rng f) (b, c)) (h₃)))


theorem surj_restriction_prop : ∀ Y f, (is_surjective f Y) → (is_surjective (f ⨡ X) (Y ∩ f.[X])) :=
  fun (Y f) => fun (_ : is_surjective f Y) =>
    fun (y) => fun (h₃ : y ∈ (Y ∩ f.[X])) =>

      let g₁ := And.right (Iff.mp (intersect_2sets_prop Y (f.[X]) y) h₃)
      let g₂ := Iff.mp (specification_set_is_specification (fun (u) => ∃ a ∈ X; (a . f . u)) (rng f) y) (g₁)
      Exists.elim (And.right g₂)
      (
        fun (u) =>
          fun (hu : u ∈ X ∧ (u . f . y)) =>
            Exists.intro u (Iff.mpr (intersect_2sets_prop f (X × (rng f)) (u, y)) (And.intro (And.right hu) (Iff.mpr (cartesian_product_pair_prop X (rng f) u y) (And.intro (And.left hu) (And.left (g₂))))))
      )


theorem monotonic_operator_fix_point : ∀ A F, (F Fun 𝒫 A To 𝒫 A) → (∀ X Y ∈ 𝒫 A; X ⊆ Y → F⦅X⦆ ⊆ F⦅Y⦆) → (∃ Z ∈ 𝒫 A; F⦅Z⦆ = Z) :=
  fun (A F) => fun (h₁ : F Fun 𝒫 A To 𝒫 A) => fun (h₂ : ∀ X Y ∈ 𝒫 A; X ⊆ Y → F⦅X⦆ ⊆ F⦅Y⦆) =>
    let S := { X ∈ (𝒫 A) | X ⊆ F⦅X⦆ }
    let Z := ⋃ S
    let g₅ : S ⊆ 𝒫 A := specification_set_subset (fun (u) => u ⊆ F⦅u⦆) (𝒫 A)
    let g₆ : Z ⊆ ⋃ (𝒫 A) := union_subset_monotonic S (𝒫 A) g₅
    let g₇ : Z ⊆ A := eq_subst (fun (u) => Z ⊆ u) (⋃ (𝒫 A)) A (union_boolean A) (g₆)
    let g₈ : Z ∈ 𝒫 A := Iff.mpr (boolean_set_is_boolean A Z) g₇
    let h₃ := fun (X) => fun (h₄ : X ∈ S) =>
      let g₁ := And.right (Iff.mp (specification_set_is_specification (fun (u) => u ⊆ F⦅u⦆) (𝒫 A) X) h₄)
      let g₂ := elem_subset_union S X h₄
      let g₃ := eq_subst (fun (u) => X ⊆ u) (⋃ S) (Z) (Eq.refl Z) (g₂)
      let g₄ := And.left ((Iff.mp (specification_set_is_specification (fun (u) => u ⊆ F⦅u⦆) (𝒫 A) X) h₄))
      let g₉ := h₂ X g₄ Z g₈ g₃
      let h₅ := subset_trans_curry X (F⦅X⦆) (F⦅Z⦆) (g₁) (g₉)
      h₅
    let h₆ : Z ⊆ F⦅Z⦆ := all_ss_then_union_ss S (F⦅Z⦆) (h₃)
    let h₇ : F⦅Z⦆ ∈ 𝒫 A := val_in_B F (𝒫 A) (𝒫 A) (h₁) (Z) (g₈)
    let h₈ : F⦅Z⦆ ⊆ F⦅F⦅Z⦆⦆ := h₂ Z g₈ (F⦅Z⦆) h₇ (h₆)
    let h₉ : F⦅Z⦆ ∈ S := Iff.mpr (specification_set_is_specification (fun (u) => u ⊆ F⦅u⦆) (𝒫 A) (F⦅Z⦆)) (And.intro (h₇) (h₈))
    let h : F⦅Z⦆ ⊆ Z := elem_subset_union S (F⦅Z⦆) h₉
    Exists.intro Z (And.intro (g₈) (subset_then_equality (F⦅Z⦆) (Z) (And.intro (h) (h₆))))



noncomputable def injection (f A B : Set) := (f Fun A To B) ∧ (is_injective f)
noncomputable def surjection (f A B : Set) := (f Fun A To B) ∧ (is_surjective f B)
noncomputable def bijection (f A B : Set) := (f Fun A To B) ∧ (is_injective f) ∧ (is_surjective f B)


syntax term "Inj" term "To" term : term
syntax term "Surj" term "To" term : term
syntax term "Bij" term "To" term : term


macro_rules
  | `($f:term Inj $A:term To $B:term) => `(injection $f $A $B)
  | `($f:term Surj $A:term To $B:term) => `(surjection $f $A $B)
  | `($f:term Bij $A:term To $B:term) => `(bijection $f $A $B)



theorem id_is_bij : ∀ A, (id_ A) Bij A To A :=
  fun (A) =>
    let h₁ : id_ A ⊆ A × A := specification_set_subset (fun (u) => ∃ x, u = (x, x)) (A × A)
    let h₂ := fun (x y z) => fun (h₃ : (x . (id_ A) . y)) => fun (h₄ : (x . (id_ A) . z)) =>
      let g := And.left (And.left (id_prop A x y h₃))
      let g₁ := And.left (And.left (id_prop A x z h₄))
      Eq.trans (Eq.symm g) (g₁)
    let h₅ : ∀ x ∈ A; ∃ y, (x . (id_ A) . y) := fun (x) =>
      fun (h₉ : x ∈ A) =>
        Exists.intro x (prop_then_id A x h₉)
    let h₆ := fun (x y z) => fun (h₃ : (x . (id_ A) . z)) => fun (h₄ : (y . (id_ A) . z)) =>
      let g := And.left (And.left (id_prop A x z h₃))
      let g₁ := And.left (And.left (id_prop A y z h₄))
      Eq.trans (g) (Eq.symm g₁)
    let h₇ : ∀ y ∈ A; ∃ x, (x . (id_ A) . y) := fun (y) =>
      fun (h₉ : y ∈ A) =>
        Exists.intro y (prop_then_id A y h₉)
    And.intro (And.intro (And.intro (h₁) (h₂)) (h₅)) (
      And.intro (h₆) (h₇)
    )



theorem bij_is_inj : ∀ A B f, (f Bij A To B) → (f Inj A To B) :=
  fun (A B f) => fun (s : f Bij A To B) => And.intro (And.left s) (And.left (And.right (s)))

theorem bij_is_surj : ∀ A B f, (f Bij A To B) → (f Surj A To B) :=
  fun (A B f) => fun (s : f Bij A To B) => And.intro (And.left s) (And.right (And.right (s)))


theorem inj_surj_is_bij : ∀ A B f, (f Inj A To B) → (f Surj A To B) → (f Bij A To B) :=
  fun (A B f) => fun (h₁ : f Inj A To B) => fun (h₂ : f Surj A To B) =>
    And.intro (And.left h₁) (And.intro (And.right h₁) (And.right h₂))


theorem func_inj_prop : ∀ A B f, (f Fun A To B) → ((f Inj A To B) ↔ (∀ x y ∈ A; (f⦅x⦆ = f⦅y⦆) → x = y)) :=
  fun (A B f) => fun (h₁ : f Fun A To B) =>
    Iff.intro
    (
      fun (h₂ : (f Inj A To B)) =>
        fun (x) => fun (h₄ : x ∈ A) => fun (y) => fun (h₅ : y ∈ A) =>
          fun (h₆ : f⦅x⦆ = f⦅y⦆) =>
            And.right h₂ x y (f⦅x⦆) (function_value_pick_property f A B x h₄ h₁)
            (eq_subst (fun (u) => (y . f . (u))) (f⦅y⦆) (f⦅x⦆) (Eq.symm h₆) (function_value_pick_property f A B y h₅ h₁) )
    )
    (
      fun (h₂ : ∀ x y ∈ A; (f⦅x⦆ = f⦅y⦆) → x = y) =>
        And.intro (h₁) (fun (x y z) => fun (h₃ : (x . f . z)) => fun (h₄ : (y . f . z)) =>
          let h₅ := And.left (Iff.mp (cartesian_product_pair_prop A B x z) (And.left (And.left h₁) (x, z) h₃))
          let h₆ := And.left (Iff.mp (cartesian_product_pair_prop A B y z) (And.left (And.left h₁) (y, z) h₄))
          let h₇ := (Iff.mp (function_equal_value_prop f A B h₁ x z h₅)) h₃
          let h₈ := (Iff.mp (function_equal_value_prop f A B h₁ y z h₆)) h₄
          h₂ x h₅ y h₆ (Eq.trans (Eq.symm (h₇)) (h₈))
        )
    )


theorem func_surj_prop : ∀ A B f, (f Fun A To B) → ((f Surj A To B) ↔ (∀ y ∈ B; ∃ x ∈ A; y = f⦅x⦆)) :=
  fun (A B f) => fun (h₂ : f Fun A To B) =>
    Iff.intro
    (
      fun (h₃ : (f Surj A To B)) =>
        fun (y) => fun (h₄ : y ∈ B) =>
          let h₅ := And.right h₃ y h₄
          Exists.elim h₅
          (
            fun (w) =>
              fun (hw : (w . f . y)) =>
                let g₁ := (And.left (Iff.mp (cartesian_product_pair_prop A B w y) (And.left (And.left h₂) (w, y) (hw))))
                Exists.intro w (And.intro (g₁) (Iff.mp (function_equal_value_prop f A B h₂ w y (g₁)) (hw)))
          )
    )
    (
      fun (h₃ : (∀ y ∈ B; ∃ x ∈ A; y = f⦅x⦆)) =>
        And.intro (h₂) (fun (y) => fun (h₄ : y ∈ B) =>
          Exists.elim (h₃ y h₄)
          (
            fun (x) =>
              fun (hx : x ∈ A ∧ y = f⦅x⦆) =>
                Exists.intro x (
              eq_subst (fun (u) => (x, u) ∈ f) (f⦅x⦆) (y) (Eq.symm (And.right hx)) (function_value_pick_property f A B x (
                And.left hx) (h₂))
            )
          )
        )
    )



theorem func_surj_crit : ∀ A B f, (f Fun A To B) → ((f Surj A To B) ↔ rng f = B) :=
  fun (A B f) =>
    fun (h : (f Fun A To B)) =>
      Iff.intro
      (
        fun (h₁ : (f Surj A To B)) =>
          Iff.mp (subs_subs_eq (rng f) (B)) (And.intro (rng_partial_function f A B (And.left h)) (
            fun (x) =>
              fun (hx : x ∈ B) =>
                Iff.mpr (rng_prop f x) (
                  And.right h₁ x hx
                )
          ))
      )
      (
        fun (h₁ : (rng f = B)) =>
          And.intro (h) (
            fun (x) =>
              fun (hx : x ∈ B) =>
                let hrngB := eq_subst (fun (t) => x ∈ t) (B) (rng f) (Eq.symm h₁) (hx)
                Iff.mp (rng_prop f x) (hrngB)
          )
      )





theorem injection_composition : ∀ f g A B C, (f Inj A To B) → (g Inj B To C) → (((g ∘ f) Inj A To C)) :=
  fun (f g A B C) => fun (h₁ : (f Inj A To B)) => fun (h₂ : (g Inj B To C)) =>
    And.intro (And.left (function_composition f g A B C (And.left h₁) (And.left h₂))) (composition_injective g f (And.right h₂) (And.right h₁))


theorem surjection_composition : ∀ f g A B C, (f Surj A To B) → (g Surj B To C) → (((g ∘ f) Surj A To C)) :=
  fun (f g A B C) => fun (h₁ : (f Surj A To B)) => fun (h₂ : (g Surj B To C)) =>
    And.intro (And.left (function_composition f g A B C (And.left h₁) (And.left h₂))) (composition_surjective g f C B (And.left (And.left (And.left h₂))) (And.right h₂) (And.right h₁))


theorem bijection_composition : ∀ f g A B C, (f Bij A To B) → (g Bij B To C) → ((g ∘ f) Bij A To C) :=
  fun (f g A B C) => fun (h₁ : (f Bij A To B)) => fun (h₂ : (g Bij B To C)) =>
    inj_surj_is_bij A C (g ∘ f) (injection_composition f g A B C (bij_is_inj A B f h₁) (bij_is_inj B C g h₂))
     (surjection_composition f g A B C (bij_is_surj A B f h₁) (bij_is_surj B C g h₂))


theorem bijection_inv_mp : ∀ f A B, ((f Bij A To B) → (f⁻¹ Bij B To A)) :=
  fun (f A B) =>
    (
      fun (h : (f Bij A To B)) =>
        let h₁ := And.left h
        let h₂ := And.left h₁
        let h₃ := And.left h₂
        let h₄ := And.right h₂
        let h₅ := And.left (prop_then_binary_relation A B f h₃)
        let h₆ := And.left (And.right h)
        let h₇ := And.right (And.right h)
        let h₈ := And.right h₁
        And.intro (And.intro (And.intro (inv_between A B f h₃) (Iff.mp (inj_inv_func f h₅) (h₆)))
         (Iff.mp (surj_inv_tot f B h₅) (h₇))) (And.intro (Iff.mp (func_inv_inj f h₅) (h₄)) (Iff.mp (tot_inv_surj f A h₅) (h₈)))
    )



theorem bijection_inv : ∀ f A B, binary_relation f → ((f Bij A To B) ↔ (f⁻¹ Bij B To A)) :=
  fun (f A B) => fun (g : binary_relation f) =>
    Iff.intro
    (
      bijection_inv_mp f A B
    )
    (
      fun (h : (f⁻¹ Bij B To A)) =>
        let h₁ := bijection_inv_mp (f⁻¹) B A h
        eq_subst (fun (u) => bijection u A B) ((f⁻¹)⁻¹) f (inv_prop f (g)) (h₁)
    )


theorem id_func_criterion : ∀ f A B, binary_relation_between A B f → ((is_functional f) ↔ (f ∘ f⁻¹ ⊆ id_ B)) :=
  fun (f A B) => fun (h₁ : binary_relation_between A B f) =>
    Iff.intro
    (
      fun (h₂ : is_functional f) =>
        rel_subset (f ∘ f⁻¹) (id_ B) (composition_is_rel f (f⁻¹)) (id_is_rel B) (fun (x y) =>
          fun (h₃ : (x, y) ∈ f ∘ f⁻¹) =>
            let g := Iff.mp (composition_pair_prop f (f⁻¹) x y) h₃
            Exists.elim g
            (
              fun (z) =>
                fun (hz : (x, z) ∈ f⁻¹ ∧ (z, y) ∈ f) =>
                  let g₁ := Iff.mpr (inv_pair_prop f (And.left (prop_then_binary_relation A B f h₁)) z x) (And.left hz)
                  let g₂ := h₂ z x y g₁ (And.right hz)
                  let g₃ := h₁ (z, x) g₁
                  let g₄ := And.right (Iff.mp (cartesian_product_pair_prop A B z x) g₃)
                  eq_subst (fun (u) => (x, u) ∈ id_ B) x y (g₂) (prop_then_id B x (g₄))
            )
        )


    )
    (
      fun (h₂ : f ∘ f⁻¹ ⊆ id_ B) =>
        fun (x y z) =>
          fun (h₃ : (x . f . y)) =>
            fun (h₄ : (x . f . z)) =>
              let h₅ := Iff.mp ((inv_pair_prop f (And.left (prop_then_binary_relation A B f h₁))) x y) h₃
              let h₆ := Iff.mpr (composition_pair_prop f (f⁻¹) y z) (Exists.intro x (And.intro (h₅) (h₄)))
              let h₇ := h₂ (y, z) h₆
              let h₈ := id_prop B y z h₇
              And.left (And.left h₈)
    )

theorem id_inj_criterion : ∀ f A B, binary_relation_between A B f → ((is_injective f) ↔ (f⁻¹ ∘ f ⊆ id_ A)) :=
  fun (f A B) => fun (h₁ : binary_relation_between A B f) =>
    Iff.intro
    (
      fun (h₂ : is_injective f) =>
        rel_subset (f⁻¹ ∘ f) (id_ A) (composition_is_rel (f⁻¹) (f)) (id_is_rel A) (fun (x y) =>
          fun (h₃ : (x, y) ∈ f⁻¹ ∘ f) =>
            let g := Iff.mp (composition_pair_prop (f⁻¹) (f) x y) h₃
            Exists.elim g
            (
              fun (z) =>
                fun (hz : (x, z) ∈ f ∧ (z, y) ∈ f⁻¹) =>
                  let g₁ := Iff.mpr (inv_pair_prop f (And.left (prop_then_binary_relation A B f h₁)) y z) (And.right hz)
                  let g₂ := h₂ y x z g₁ (And.left hz)
                  let g₃ := h₁ (y, z) g₁
                  let g₄ := And.left (Iff.mp (cartesian_product_pair_prop A B y z) g₃)
                  eq_subst (fun (u) => (u, y) ∈ id_ A) y x (g₂) (prop_then_id A y (g₄))
            )
        )
    )
    (
      fun (h₂ : f⁻¹ ∘ f ⊆ id_ A) =>
        fun (x y z) =>
          fun (h₃ : (x . f . z)) =>
            fun (h₄ : (y . f . z)) =>
              let h₅ := Iff.mp ((inv_pair_prop f (And.left (prop_then_binary_relation A B f h₁))) x z) h₃
              let h₆ := Iff.mpr (composition_pair_prop (f⁻¹) f y x) (Exists.intro z (And.intro (h₄) (h₅)))
              let h₇ := h₂ (y, x) h₆
              let h₈ := id_prop A y x h₇
              Eq.symm (And.left (And.left h₈))
    )

theorem id_tot_criterion : ∀ f A B, binary_relation_between A B f → ((is_total f A) ↔ (id_ A ⊆ f⁻¹ ∘ f)) :=
  fun (f A B) => fun (h₁ : binary_relation_between A B f) =>
    Iff.intro
    (
      fun (h₂ : is_total f A) =>
        rel_subset (id_ A) (f⁻¹ ∘ f) (id_is_rel A) (composition_is_rel (f⁻¹) f) (fun (x y) =>
          fun (h₃ : (x, y) ∈ id_ A) =>
            let h₄ := And.left (And.left (id_prop (A) x y h₃))
            let h₅ := And.right (And.left (id_prop (A) x y h₃))
            Iff.mpr (composition_pair_prop (f⁻¹) (f) x y) (
              let h₆ := h₂ x h₅
              Exists.elim h₆
              (
                fun (w) =>
                  fun (hw : (x . f . w)) =>
                    Exists.intro w (And.intro (hw) (
                      eq_subst (fun (u) => (w . (f⁻¹) . u)) x y (h₄) (Iff.mp (inv_pair_prop f (And.left (prop_then_binary_relation A B f h₁)) x w) (hw))
                    ))
              )
            )
        )
    )
    (
      fun (h₂ : id_ A ⊆ f⁻¹ ∘ f) =>
        fun (x) => fun (h₃ : x ∈ A) =>
          let h₄ := h₂ (x, x) (prop_then_id A x h₃)
          let h₅ := Iff.mp (composition_pair_prop (f⁻¹) (f) x x) h₄
          Exists.elim h₅
          (
            fun (z) =>
              fun (hz : (x, z) ∈ f ∧ (z, x) ∈ f⁻¹) =>
                Exists.intro z (And.left hz)
          )
    )

theorem id_surj_criterion : ∀ f A B, binary_relation_between A B f → ((is_surjective f B) ↔ (id_ B ⊆ f ∘ f⁻¹)) :=
  fun (f A B) => fun (h₁ : binary_relation_between A B f) =>
    Iff.intro
    (
      fun (h₂ : is_surjective f B) =>
        rel_subset (id_ B) (f ∘ f⁻¹) (id_is_rel B) (composition_is_rel (f) (f⁻¹)) (fun (x y) =>
          fun (h₃ : (x, y) ∈ id_ B) =>
            let h₄ := And.left (And.left (id_prop (B) x y h₃))
            let h₅ := And.right (And.left (id_prop (B) x y h₃))
            Iff.mpr (composition_pair_prop (f) (f⁻¹) x y) (
              let h₆ := h₂ x h₅
              Exists.elim h₆
              (
                fun (w) =>
                  fun (hw : (w . f . x)) =>
                    Exists.intro w (And.intro (Iff.mp (inv_pair_prop f (And.left (prop_then_binary_relation A B f h₁)) w x) (hw)) (
                      eq_subst (fun (u) => (w . f . u)) x y (h₄) (hw))
                    ))
              )
            )
    )
    (
      fun (h₂ : id_ B ⊆ f ∘ f⁻¹) =>
        fun (x) => fun (h₃ : x ∈ B) =>
          let h₄ := h₂ (x, x) (prop_then_id B x h₃)
          let h₅ := Iff.mp (composition_pair_prop (f) (f⁻¹) x x) h₄
          Exists.elim h₅
          (
            fun (z) =>
              fun (hz : (x, z) ∈ f⁻¹ ∧ (z, x) ∈ f) =>
                Exists.intro z (And.right hz)
          )
    )



theorem id_bijection_criterion : ∀ f A B, binary_relation_between A B f → ((f Bij A To B) ↔ ((f⁻¹ ∘ f = id_ A) ∧ (f ∘ f⁻¹ = id_ B))) :=
  fun (f A B) => fun (h₁ : binary_relation_between A B f) =>
    Iff.intro
    (
      fun (h₂ : f Bij A To B) =>
        let h₃ := And.left (And.right h₂)
        let h₄ := And.right (And.right h₂)
        let h₅ := And.right (And.left h₂)
        let h₆ := And.right (And.left (And.left h₂))
        let h₇ := Iff.mp (id_func_criterion f A B h₁) h₆
        let h₈ := Iff.mp (id_tot_criterion f A B h₁) h₅
        let h₉ := Iff.mp (id_inj_criterion f A B h₁) h₃
        let h₀ := Iff.mp (id_surj_criterion f A B h₁) h₄
        let g₁ := subset_then_equality (f⁻¹ ∘ f) (id_ A) (And.intro (h₉) (h₈))
        let g₂ := subset_then_equality (f ∘ f⁻¹) (id_ B) (And.intro (h₇) (h₀))
        And.intro (g₁) (g₂)
    )
    (
      fun (h₂ : (f⁻¹ ∘ f = id_ A) ∧ (f ∘ f⁻¹ = id_ B)) =>
        let h₃ := equality_then_subset (f⁻¹ ∘ f) (id_ A) (And.left h₂)
        let h₄ := equality_then_subset (id_ A) (f⁻¹ ∘ f) (Eq.symm (And.left h₂))
        let h₅ := equality_then_subset (f ∘ f⁻¹) (id_ B) (And.right h₂)
        let h₆ := equality_then_subset (id_ B) (f ∘ f⁻¹) (Eq.symm (And.right h₂))
        let h₇ := Iff.mpr (id_func_criterion f A B h₁) (h₅)
        let h₈ := Iff.mpr (id_tot_criterion f A B h₁) (h₄)
        let h₉ := Iff.mpr (id_inj_criterion f A B h₁) (h₃)
        let h₀ := Iff.mpr (id_surj_criterion f A B h₁) (h₆)
        And.intro (And.intro (And.intro (h₁) (h₇)) (h₈)) (And.intro (h₉) (h₀))
    )


noncomputable def left_reversable (f A B : Set) : Prop := (f Fun A To B) ∧ ∃ g, (g Fun B To A) ∧ (g ∘ f = id_ A)
noncomputable def right_reversable (f A B : Set) : Prop := (f Fun A To B) ∧ ∃ g, (g Fun B To A) ∧ (f ∘ g = id_ B)
noncomputable def reversable (f A B : Set) : Prop := (f Fun A To B) ∧ ∃ g, (g Fun B To A) ∧ (g ∘ f = id_ A) ∧ (f ∘ g = id_ B)
syntax term "LeftRev" term "To" term : term
macro_rules
  | `($f:term LeftRev $A:term To $B:term)  => `(left_reversable $f $A $B)
syntax term "RightRev" term "To" term : term
macro_rules
  | `($f:term RightRev $A:term To $B:term) => `(right_reversable $f $A $B)
syntax term "Rev" term "To" term : term
macro_rules
  | `($f:term Rev $A:term To $B:term) => `(reversable $f $A $B)


theorem injection_condition :
∀ f A B, (f LeftRev A To B) → (f Inj A To B) :=
  fun (f A B) =>
    fun (hleftrev : f LeftRev A To B) =>
        let h := And.left hleftrev
        let g₁ :=And.right hleftrev
        Exists.elim g₁
        (
          fun (g) =>
            fun (h₀ : (g Fun B To A) ∧ (g ∘ f = id_ A)) =>
              And.intro (h) (
                fun (x y z) =>
                  fun (h₁ : (x . f . z)) =>
                    fun (h₂ : (y . f . z)) =>
                      let h₃ := And.left ((Iff.mp (cartesian_product_pair_prop A B x z)) (And.left (And.left h) (x, z) h₁))
                      let h₄ := prop_then_id A x h₃
                      let h₅ := eq_subst (fun (t) => (x, x) ∈ t) (id_ A) (g ∘ f) (Eq.symm (And.right (h₀))) (h₄)
                      let h₆ := Iff.mp (composition_pair_prop g f x x) h₅
                      let h₇ := And.left ((Iff.mp (cartesian_product_pair_prop A B y z)) (And.left (And.left h) (y, z) h₂))
                      let h₈ := prop_then_id A y h₇
                      let h₉ := eq_subst (fun (t) => (y, y) ∈ t) (id_ A) (g ∘ f) (Eq.symm (And.right h₀)) (h₈)
                      let hh₁ := Iff.mp (composition_pair_prop g f y y) h₉
                      Exists.elim h₆
                      (
                        fun (m) =>
                          fun (s : ((x, m) ∈ f) ∧ (m, x) ∈ g) =>
                            Exists.elim hh₁
                            (
                              fun (n) =>
                                fun (t : (y, n) ∈ f ∧ (n, y) ∈ g) =>
                                  let func₁ := And.right (And.left h)
                                  let func₂ := func₁ x m z (And.left s) (h₁)
                                  let func₃ := func₁ y n z (And.left t) (h₂)
                                  let eq₄ := Eq.trans (func₂) (Eq.symm (func₃))
                                  let func₄ := And.right (And.left (And.left h₀)) m x y (And.right s)
                                  func₄ (eq_subst (fun (r) => (r, y) ∈ g) n m (Eq.symm eq₄) (And.right t))

                            )
                      )
              )
        )



theorem left_reverse_property :
  ∀ f A B, (f LeftRev A To B) → (A ≠ ∅ ∨ B = ∅) :=
    fun (f A B) =>
      fun (hleftrev : (f LeftRev A To B)) =>
        let h₀ := And.right hleftrev
        Or.elim (em (A = ∅))
        (
          fun (g₀ : A = ∅) =>
            Or.inr (

              Exists.elim h₀
              (
                fun (g) =>
                  fun (hg : (g Fun B To A) ∧ (g ∘ f = id_ A)) =>
                    let hg₀ := And.left hg
                    byContradiction (
                      fun (hB : B ≠ ∅) =>
                        let u : ¬ empty B := fun (g₀ : empty B) => (
                          hB (Iff.mp (subs_subs_eq B ∅) (And.intro (
                            fun (x) => fun (hx : x ∈ B) =>
                              False.elim (g₀ x (hx))
                          ) (empty_set_is_subset_any B)))
                        )
                        let v := Iff.mpr (morgan_exi Set (fun (t) => t ∉ B)) u
                        let v₂ := Exists.elim v (
                          fun (x₀) =>
                            fun (hx₀ : ¬x₀ ∉ B) =>
                              Exists.intro x₀ (byContradiction hx₀)
                        )

                        Exists.elim v₂
                        (
                          fun (x₀) =>
                            fun (hx₀ : x₀ ∈ B) =>
                              let v₃ := val_in_B g B A hg₀ x₀ hx₀
                              empty_set_is_empty (g⦅x₀⦆) (
                                eq_subst (fun (t) => g⦅x₀⦆ ∈ t) (A) (∅) (g₀) (v₃)
                              )
                        )

                    )
              )

            )
        )
        (
          fun (h : A ≠ ∅) =>
            Or.inl h
        )



theorem injection_property_simple :
  ∀ f A B, (B = ∅) → (f Inj A To B) → (f LeftRev A To B) :=
  fun (f A B) =>
      fun (h₀ : B = ∅) =>
        fun (hinj : (f Inj A To B)) =>
          let h := And.left hinj
          And.intro (h) (
            Exists.intro ∅ (

              And.intro


              (And.intro (And.intro (empty_set_is_subset_any (B × A)) (

                fun (x y z) =>
                  fun (hx : (x . ∅ . y)) =>
                    fun (_ : (x . ∅ . z)) =>
                      False.elim (empty_set_is_empty (x, y) (hx))

              )) (
                fun (x) =>
                  fun (hx : x ∈ B) =>
                    False.elim (empty_set_is_empty x (eq_subst (fun (t) => x ∈ t) B ∅ (h₀) (hx)))
              ))

              (
                relation_equality (∅ ∘ f) (id_ A) (composition_is_rel ∅ f) (id_is_rel A)
                (
                  fun (x y) =>
                    Iff.intro
                    (
                      fun (hxy : (x, y) ∈ (∅ ∘ f)) =>
                        False.elim (
                          let u := Iff.mp (composition_pair_prop ∅ f x y) hxy
                          Exists.elim u
                          (
                            fun (z) =>
                              fun (hx : (x, z) ∈ f ∧ (z, y) ∈ ∅) =>
                                empty_set_is_empty (z, y) (And.right hx)
                          )
                        )
                    )
                    (
                      fun (hxy : (x, y) ∈ (id_ A)) =>
                        False.elim (
                          let u := And.right (id_prop A x y hxy)
                          let v := val_in_B f A B h y u
                          empty_set_is_empty (f⦅y⦆) (eq_subst (fun (t) => f⦅y⦆ ∈ t) B ∅ (h₀) (v)))
                        )
                    )

                )
              )
          )





theorem injection_property_hard :
∀ f A B, (A ≠ ∅) → (f Inj A To B) → (f LeftRev A To B) :=
  fun (f A B) =>
    fun (h₀ : (A ≠ ∅)) =>
      fun (hinj : (f Inj A To B)) =>
        let h := And.left hinj
        And.intro (h) (
          let h₁ : ¬ empty A := fun (g₀ : empty A) => h₀ (Iff.mp (subs_subs_eq A ∅) (And.intro (
            fun (x) => fun (hx : x ∈ A) => False.elim (g₀ x (hx))
          ) (empty_set_is_subset_any A)))
            let hm := Iff.mpr (morgan_exi Set (fun (t) => t ∉ A)) h₁
            let hm₂ : ∃ x, x ∈ A := Exists.elim hm (
              fun (y) =>
                fun (hy : ¬ y ∉ A) =>
                  Exists.intro y (byContradiction hy)
            )
            Exists.elim hm₂
            (
              fun (x₀) =>
                fun (hx₀ : x₀ ∈ A) =>
                    let P := (fun (x) => x ∈ rng f)
                    let c := (fun (x) => f⁻¹⦅x⦆)
                    let d := (fun (_) => x₀)
                    let g := lam_cond_fun B A P c d
                    Exists.intro g
                    (



                      let f_binary_prop := And.left (prop_then_binary_relation A B f (And.left (And.left (h))))

                      let dom_prop₀ := inv_dom f f_binary_prop

                      let finv_binary_prop := inv_between_mp A B f (And.left (And.left h))
                      let finv_parial_func : (f⁻¹) PartFun B To A := And.intro (finv_binary_prop) (Iff.mp (inj_inv_func f (f_binary_prop)) (And.right hinj))


                      let c_prop : ∀ x ∈ B; (P x → c x ∈ A) := fun (x) => fun (_ : x ∈ B) =>
                        fun (hx₂ : x ∈ rng f) =>
                          let hx₃ := eq_subst (fun (S) => x ∈ S) (rng f) (dom (f⁻¹)) (Eq.symm dom_prop₀) (hx₂)
                          part_val_in_B (f⁻¹) B A finv_parial_func x hx₃

                      let d_prop : ∀ x ∈ B; (¬P x → d x ∈ A) := fun (x) => fun (_ : x ∈ B) => fun (_ : ¬ (x ∈ rng f)) => hx₀


                      let h₃ := lam_cond_fun_prop B A P c d (fun (x) => fun (hx₄ : x ∈ B) => And.intro (c_prop x hx₄) (d_prop x hx₄))

                      let g_func := And.left h₃


                      And.intro (g_func) (

                        Iff.mpr (equal_functions_abc_A (g ∘ f) (id_ A) A A A (
                          And.left (function_composition f g A B A h g_func)
                        ) (
                          And.left (id_is_bij A)
                        )) (fun (x) =>
                              fun (hxA : x ∈ A) =>
                            (

                                let first := Iff.mp (function_equal_value_prop (id_ A) A A (And.left (id_is_bij A)) x x hxA) (prop_then_id A x hxA)
                                let second := And.right (function_composition_A f g A B A (h) (g_func)) x hxA
                                Eq.trans (Eq.trans (second) (

                                  Or.elim (em (P (f⦅x⦆)))
                                  (
                                    fun (hpfx : P ( f⦅x⦆ )) =>

                                      let val_in_B_prop := val_in_B f A B h x hxA
                                      let some_prov_result : g⦅f⦅x⦆⦆ = c (f⦅x⦆) := And.left (And.right (h₃) (f⦅x⦆) val_in_B_prop) hpfx
                                      Eq.trans (some_prov_result) (

                                        let some_prop_result := And.right (partial_composition f (f⁻¹) A B A (And.left h) (finv_parial_func)) x (
                                          eq_subst (fun (M) => x ∈ M) (A) (dom f) (dom_function f A B h) (hxA)
                                        )

                                        let fxdomfinv := eq_subst (fun (t) => f⦅x⦆ ∈ t) (rng f) (dom (f⁻¹)) (Eq.symm dom_prop₀) (val_in_rng f A B h x hxA)

                                        Or.elim (some_prop_result)
                                        (
                                          fun (stup : ((f⁻¹ ∘ f) ↑↑ x) ∧ (f⁻¹ ↑↑ (f⦅x⦆))) =>
                                            False.elim (And.right stup (fxdomfinv))
                                        )
                                        (
                                          fun (real : (((f⁻¹ ∘ f) ↓↓ x) ∧ (f⁻¹ ↓↓ (f⦅x⦆))) ∧ ((f⁻¹ ∘ f)⦅x⦆ = f⁻¹⦅f⦅x⦆⦆)) =>
                                            Eq.trans (Eq.symm (And.right real)) (

                                              let second := Iff.mp (id_tot_criterion f A B (And.left (And.left (h)))) (And.right h)
                                              let third := Iff.mp (id_inj_criterion f A B (And.left (And.left h))) (And.right hinj)
                                              let fourth := Iff.mp (subs_subs_eq (f⁻¹ ∘ f) (id_ A)) (And.intro (third) (second))
                                              let fifth := eq_subst (fun (t) => (f⁻¹ ∘ f)⦅x⦆ = t⦅x⦆) (f⁻¹ ∘ f) (id_ A) (fourth) (Eq.refl ((f⁻¹ ∘ f)⦅x⦆))
                                              let sixth := Iff.mp (function_equal_value_prop (id_ A) A A (And.left (id_is_bij A)) x x hxA) (prop_then_id A x hxA)
                                              Eq.trans (fifth) (Eq.symm (sixth))

                                            )
                                        )

                                      )

                                  )
                                  (
                                    fun (hnpfx : ¬ P ( f⦅x⦆ )) =>
                                      let hpfx := val_in_rng f A B h x hxA
                                      False.elim (hnpfx (hpfx))
                                  )


                                )) (first)
                            )
                        )
                      )
                  )
            )
        )



theorem left_rev_criterion:
  ∀ f A B, (f LeftRev A To B) ↔ ((f Inj A To B) ∧ (A ≠ ∅ ∨ B = ∅))  :=
    fun (f A B) =>
      Iff.intro
      (
        fun (hleftrev: f LeftRev A To B) =>
          And.intro (injection_condition f A B hleftrev) (left_reverse_property f A B hleftrev)
      )
      (
        fun (hinjab : (f Inj A To B) ∧ (A ≠ ∅ ∨ B = ∅)) =>
          let hab := And.right hinjab
          Or.elim hab
          (
            fun (ha : (A ≠ ∅)) =>
              injection_property_hard f A B ha (And.left hinjab)
          )
          (
            fun (hb : (B = ∅)) =>
              injection_property_simple f A B hb (And.left hinjab)
          )
      )



theorem surjection_condition:
∀ f A B, (f RightRev A To B) → (f Surj A To B) :=
  fun (f A B) =>
    fun (hrightrev : f RightRev A To B) =>
      let h := And.left hrightrev
      let g₁ := And.right hrightrev
      Exists.elim g₁
      (
        fun (g) =>
          fun (hg : (g Fun B To A) ∧ (f ∘ g = id_ B)) =>
            And.intro (h) (
              fun (y) =>
                fun (hy : y ∈ B) =>
                  Exists.intro (g⦅y⦆) (
                    let v := And.left (function_composition g f B A B (And.left hg) h)
                    let u := Iff.mp (equal_functions_abc (f ∘ g) (id_ B) B B B v (And.left (id_is_bij B))) (And.right hg) y
                    let s := Iff.mp (function_equal_value_prop (id_ B) B B (And.left (id_is_bij B)) y y hy) (prop_then_id B y hy)
                    let s₂ := Eq.trans (u) (Eq.symm s)
                    let s₃ := And.right (function_composition_A g f B A B (And.left hg) h) y hy
                    let s₄ := Eq.trans (Eq.symm (s₃)) (s₂)
                    Iff.mpr (function_equal_value_prop f A B h (g⦅y⦆) y (val_in_B g B A (And.left hg) y hy)) (Eq.symm (s₄))
                  )
            )
      )


theorem rev_condition :
 ∀ f A B, (f Rev A To B) ↔ (f Bij A To B) :=
  fun (f A B) =>
      Iff.intro
      (
        fun (hg₁ : (f Fun A To B) ∧ ∃ g, (g Fun B To A) ∧ (g ∘ f = id_ A) ∧ (f ∘ g = id_ B)) =>
            let h := And.left hg₁
            let g₁ := And.right hg₁
            Exists.elim g₁
            (
              fun (g) =>
                fun (hg : (g Fun B To A) ∧ (g ∘ f = id_ A) ∧ (f ∘ g = id_ B)) =>
                  And.intro (h) (
                    And.intro (And.right (injection_condition f A B (And.intro (h) (Exists.intro g (And.intro (And.left hg) (And.left (And.right hg)))))))
                    (
                      And.right (surjection_condition f A B (And.intro (h) (
                        Exists.intro g (And.intro (And.left hg) (And.right (And.right hg)))
                      )))
                    )
                  )
            )
      )
      (
        fun (h₁ : f Bij A To B) =>
          let h := And.left h₁
          And.intro (h) (Exists.intro (f⁻¹) (

            And.intro (

              And.left (bijection_inv_mp f A B h₁)

              ) (Iff.mp (id_bijection_criterion f A B (And.left (And.left h))) h₁)
          ))

      )







def fun_indexation (A I : Set) : Prop := ∃ X, A Fun I To X
syntax term "IndxFun" term : term
macro_rules
| `($A:term IndxFun $I:term) => `(fun_indexation  $A $I)
noncomputable def indexed_family (A I : Set) := A.[I]
syntax "{" term "of" term "where" term "in" term "}" : term
macro_rules
| `({ $A:term of $_:term where $_:term in $I:term }) => `(indexed_family $A $I)
noncomputable def indexed_set (A i : Set) := A⦅i⦆
infix:60 (priority := high) " _ " => indexed_set
def indexation (A I : Set) : Prop := (∀ x, (x ∈ ({A of i where i in I})) ↔ (∃ i ∈ I; x = (A _ i)))
syntax term "Indx" term : term
macro_rules
| `($A:term Indx $I:term) => `(indexation  $A $I)
noncomputable def indexed_union (A I : Set) := ⋃ (A.[I])
syntax "⋃[" term "in" term "]" term "at" term : term
macro_rules
| `(⋃[ $_:term in $I:term ] $A:term at $_:term ) => `(indexed_union $A $I)
noncomputable def indexed_intersection (A I : Set) := ⋂ (A.[I])
syntax "⋂[" term "in" term "]" term "at" term : term
macro_rules
| `(⋂[ $_:term in $I:term ] $A:term at $_:term ) => `(indexed_intersection $A $I)



theorem fun_indexed_is_indexed :
∀ A I, (A IndxFun I) → (A Indx I) :=
  fun (A I) =>
    fun (hindfun : (A IndxFun I)) =>
      fun (x) =>
        Iff.intro
        (
          fun (hxaiw : x ∈ ({A of i where i in I})) =>
            let rngA := rng A
            let P := fun (a) => ∃ i ∈ I; (i . A . a)
            let spec_prop := And.right (Iff.mp (specification_set_is_specification P rngA x) hxaiw)
            Exists.elim spec_prop
            (
              fun (i) =>
                fun (hi : i ∈ I ∧ (i . A . x)) =>
                  Exists.intro i (And.intro (And.left hi) (

                    Exists.elim hindfun
                    (
                      fun (X) =>
                        fun (hx : A Fun I To X) =>
                          Iff.mp (function_equal_value_prop A I X hx i x (And.left hi)) (And.right hi)
                    )
                  ))
            )
        )
        (
          fun (hi : ∃ i ∈ I; x = (A _ i)) =>
            Exists.elim hindfun
            (
              fun (X) =>
                fun (hx : A Fun I To X) =>
                  Exists.elim hi
                  (
                    fun (i) =>
                      fun (hi : i ∈ I ∧ x = (A _ i)) =>
                        let rngA := rng A
                        let P := fun (a) => ∃ i ∈ I; (i . A . a)
                        Iff.mpr (specification_set_is_specification P rngA x) (
                          And.intro (
                            let u := val_in_rng A I X hx i (And.left hi)
                            eq_subst (fun (t) => t ∈ rngA) (A _ i) (x) (Eq.symm (And.right hi)) (u)

                          ) (
                            Exists.intro i (And.intro (And.left hi) (
                              let u := function_value_pick_property A I X i (And.left hi) hx
                              eq_subst (fun (t) => (i, t) ∈ A) (A _ i) (x) (Eq.symm (And.right hi)) (u)

                            ))
                          )
                        )
                  )
            )
        )




theorem indexed_union_is_union :
  ∀ A I, (A Indx I) → ∀ x, (x ∈ (⋃[ i in I ] A at i)) ↔ (∃ i ∈ I; x ∈ (A _ i)) :=
    fun (A I) =>
      fun (h : A Indx I) =>
        fun (x) =>
          Iff.intro
          (
            fun (hx : x ∈ (⋃[ i in I ] A at i)) =>
              let un_prop := Iff.mp (union_set_is_union (A.[I]) x) hx
              Exists.elim un_prop
              (
                fun (A₀) =>
                  fun (hA₀ : A₀ ∈ (A.[I]) ∧ x ∈ A₀) =>
                    let indx := Iff.mp (h A₀) (And.left hA₀)
                    Exists.elim indx
                    (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ A₀ = (A _ i)) =>
                          Exists.intro i (And.intro (And.left hi) (
                            eq_subst (fun (t) => x ∈ t) (A₀) (A _ i) (And.right hi) (And.right hA₀)
                          ))
                    )
              )
          )
          (
            fun (hx : (∃ i ∈ I; x ∈ (A _ i))) =>
              Exists.elim hx
              (
                fun (i) =>
                  fun (hi : i ∈ I ∧ x ∈ (A _ i)) =>
                    Iff.mpr (union_set_is_union (A.[I]) x) (
                      Exists.intro (A _ i) (And.intro (

                        Iff.mpr (h (A _ i)) (
                          Exists.intro i (And.intro (And.left hi) (Eq.refl (A _ i)))
                        )
                      ) (And.right hi))
                    )
              )
          )



theorem indexed_intersection_is_intersection :
∀ A I, (I ≠ ∅) → (A IndxFun I) → ∀ x, (x ∈ (⋂[ i in I ] A at i)) ↔ (∀ i ∈ I; x ∈ (A _ i)) :=
  fun (A I) =>
    fun (Inonempty) =>
      fun (hindxFun : (A IndxFun I)) =>
        let hindx := fun_indexed_is_indexed A I hindxFun

        let first := Iff.mpr (morgan_exi Set (fun (t) => t ∉ I)) (
                fun (hempty : ∀ x, x ∉ I) =>
                  Inonempty (Iff.mp (subs_subs_eq I (∅)) (And.intro (fun (y) => fun (hy : y ∈ I) => False.elim (hempty y hy))
                  (empty_set_is_subset_any I)))
              )
        let second := Exists.elim (first) (fun (y) => fun (hy : ¬ y ∉ I) => Exists.intro y (byContradiction hy))
        Exists.elim hindxFun
        (
          fun (X) =>
            fun (hX : A Fun I To X) =>

            let exi_AI : A.[I] ≠ ∅ := Exists.elim second (
              fun (y) =>
                fun (hy : y ∈ I) =>
                  let rngA := rng A
                  let P := fun (a) => ∃ i ∈ I; (i . A . a)
                  let spec_prop : (A _ y) ∈ A.[I] := Iff.mpr (specification_set_is_specification P rngA (A _ y)) (
                    And.intro (

                            val_in_rng A I X hX y hy
                    )
                    (Exists.intro y (And.intro (hy) (

                      Iff.mpr (function_equal_value_prop A I X hX y (A _ y) hy) (Eq.refl (A _ y))


                    )))
                  )
                  fun (hAI : A.[I] = ∅) =>
                    empty_set_is_empty (A _ y) (
                      eq_subst (fun (t) => (A _ y ∈ t)) (A.[I]) (∅) (hAI) (spec_prop)
                    )
            )



            fun (x) =>
              Iff.intro
              (
                fun (hx : (x ∈ (⋂[ i in I ] A at i))) =>
                  let u := Iff.mp (intersection_non_empty (A.[I]) (exi_AI) x) hx
                  fun (i) => fun (hi : i ∈ I) =>
                    u (A _ i) (
                      Iff.mpr (hindx (A _ i)) (Exists.intro i (And.intro hi (Eq.refl (A _ i))))
                    )

              )
              (
                fun (hx : (∀ i ∈ I; x ∈ (A _ i))) =>
                  Iff.mpr (intersection_non_empty (A.[I]) (exi_AI) x) (
                    fun (A₀) => fun (hA₀ : A₀ ∈ A.[I]) =>
                      let v := Iff.mp (hindx A₀) hA₀
                      Exists.elim v
                      (
                        fun (i) =>
                          fun (hi : i ∈ I ∧ A₀ = (A _ i)) =>
                            eq_subst (fun (t) => x ∈ t) (A _ i) (A₀) (Eq.symm (And.right hi)) (
                              hx i (And.left hi)
                            )
                      )
                  )
              )

          )




noncomputable def power_set (B A : Set) : Set := {f ∈ 𝒫 (A × B) | f Fun A To B}

syntax term "ℙow" term : term
macro_rules
  |`($A:term ℙow $B:term) => `(power_set $A $B)


theorem power_set_prop : ∀ A B f, f ∈ (B ℙow A) ↔ f Fun A To B :=
  fun (A B f) =>
    Iff.intro
    (
      fun (h₁ : f ∈ (B ℙow A)) =>
        And.right (Iff.mp (specification_set_is_specification (fun (t) => t Fun A To B) (𝒫 (A × B)) f) h₁)
    )
    (
      fun (h₁ : f Fun A To B) =>
        let res₁ := And.left (And.left h₁)
        let res₂ := Iff.mpr (boolean_set_is_boolean (A × B) f) res₁
        Iff.mpr (specification_set_is_specification ((fun (t) => t Fun A To B)) (𝒫 (A × B)) f) (And.intro (res₂) (h₁))
    )




noncomputable def choice_function (A f : Set) : Prop := (f Fun A To (⋃ A)) ∧ (∀ X ∈ A; f⦅X⦆ ∈ X)
syntax term "Choice" term : term
infix:60 (priority := high) " Choice " => fun (f) => fun (A) => choice_function A f

def choice_ax : Prop := ∀ A, ∅ ∉ A → ∃ f, f Choice A

axiom axiom_of_choice : choice_ax


def all_not_inter_choice_prop : Prop := ∀ A, ∅ ∉ A → (∀ B C ∈ A; B ≠ C → B ∩ C = ∅) → (∃ f, f Choice A)


theorem AC_inter_eq_AC : choice_ax ↔ all_not_inter_choice_prop :=
  Iff.intro
  (
    fun (AC : choice_ax) =>
      fun (A) =>
        fun (hA : (∅ ∉ A)) =>
          fun (_ : (∀ B C ∈ A; B ≠ C → B ∩ C = ∅)) =>
            AC A hA
  )
  (
    fun (ACNI : all_not_inter_choice_prop) =>
      fun (A) =>
        fun (hA : (∅ ∉ A)) =>
          let P := fun (a) => { z ∈ (A × (⋃ A)) | ∃ y, z = (a, y) ∧ y ∈ a }
          let f := lam_fun A (𝒫 (A × (⋃ A))) P

          let f_prop := lam_then_fun_prop P A (𝒫 (A × (⋃ A))) (
            fun (x) => fun (_ : x ∈ A) =>
              let R := fun (t) => ∃ y, t = (x, y) ∧ y ∈ x
              let u := specification_set_subset R (A × (⋃ A))
              Iff.mpr (boolean_set_is_boolean (A × (⋃ A)) (P x)) (u)
          )

          let Af := {f of i where i in A}

          let FIn : ∃ X, f Fun A To X := Exists.intro (𝒫 (A × (⋃ A))) (And.left f_prop)

          let In := fun_indexed_is_indexed f A FIn

          let Afnempt := fun (hemp : ∅ ∈ Af) =>
            let inemp := Iff.mp (In ∅) hemp
            Exists.elim inemp (
              fun (a) =>
                fun (ha : a ∈ A ∧ ∅ = f _ a) =>
                  let P_a : f _ a  = P a := And.right f_prop a (And.left ha)
                  let pa_emp := Eq.trans (And.right ha) P_a

                  let xneq_emp : a ≠ ∅ := fun (xeq_emp : a = ∅) =>
                    hA (eq_subst (fun (t) => t ∈ A) (a) (∅) (xeq_emp) (And.left ha))
                  let exi := non_empty_uni_then_exi (fun (_ : Set) => True) a xneq_emp (fun (y) => fun (_ : y ∈ a) => True.intro)
                  Exists.elim exi
                  (
                    fun (y) =>
                      fun (hy : y ∈ a ∧ True) =>
                        let un_prop := Iff.mpr (union_set_is_union A y) (Exists.intro a (And.intro (And.left ha) (And.left hy)))
                        let xyin := Iff.mpr (cartesian_product_pair_prop (A) (⋃ A) a y) (And.intro (And.left ha) (un_prop))
                        let R := fun (s) => ∃ y, s = (a, y) ∧ y ∈ a
                        let spec := Iff.mpr (specification_set_is_specification R (A × (⋃ A)) (a, y)) (
                          And.intro (xyin) (Exists.intro y (And.intro (Eq.refl (a, y)) (And.left hy)))
                        )
                        let subst := eq_subst (fun (t) => (a, y) ∈ t) (P a) (∅) (Eq.symm pa_emp) (spec)
                        empty_set_is_empty (a, y) (subst)
                  )
            )

          let ACNI₁ := ACNI Af Afnempt


          let Afninter : ∀ b c ∈ Af; b ≠ c → b ∩ c = ∅ := fun (b) =>
            fun (hb : b ∈ Af) =>
              fun (c) =>
                fun (hc : c ∈ Af) =>
                  fun (hbc : b ≠ c) =>
                    let bInd := Iff.mp (In b) hb
                    let cInd := Iff.mp (In c) hc
                    Exists.elim bInd (
                      fun (i) =>
                        fun (hi : i ∈ A ∧ b = f _ i) =>
                          Exists.elim cInd
                          (
                            fun (j) =>
                              fun (hj : j ∈ A ∧ c = f _ j) =>
                                let inj : i ≠ j := fun (hij : i = j) =>
                                  let d := eq_subst (fun (t) => f _ i = f _ t) i j (hij) (Eq.refl (f _ i))
                                  let e := Eq.trans (And.right hi) (Eq.trans (d) (Eq.symm (And.right hj)))
                                  hbc e

                                byContradiction (
                                  fun (hbcnemp : b ∩ c ≠ ∅) =>
                                    let bcexi := non_empty_uni_then_exi (fun (_) => True) (b ∩ c) hbcnemp (fun (x) => fun (_ : x ∈ (b ∩ c)) => True.intro)
                                    Exists.elim bcexi
                                    (
                                      fun (r) =>
                                        fun (hr : r ∈ (b ∩ c) ∧ True) =>
                                          let int_bc := Iff.mp (intersect_2sets_prop b c r) (And.left hr)
                                          let int_fi := eq_subst (fun (t) => r ∈ t) b (f _ i) (And.right hi) (And.left int_bc)
                                          let int_fj := eq_subst (fun (t) => r ∈ t) c (f _ j) (And.right hj) (And.right int_bc)
                                          let P_ifi : f _ i  = P i := And.right f_prop i (And.left hi)
                                          let P_jfj : f _ j  = P j := And.right f_prop j (And.left hj)
                                          let int_pi := eq_subst (fun (t) => r ∈ t) (f _ i) (P i) (P_ifi) int_fi
                                          let int_pj := eq_subst (fun (t) => r ∈ t) (f _ j) (P j) (P_jfj) int_fj
                                          let P_cur_i := fun (k) => ∃ y, k = (i, y) ∧ y ∈ i
                                          let P_cur_j := fun (k) => ∃ y, k = (j, y) ∧ y ∈ j
                                          let pi_spec := And.right (
                                            Iff.mp (specification_set_is_specification (P_cur_i) (A × ⋃ A) r) int_pi)
                                          let pj_sepc :=  And.right (
                                            Iff.mp (specification_set_is_specification (P_cur_j) (A × ⋃ A) r) int_pj)
                                          Exists.elim pi_spec
                                          (
                                            fun (y₁) =>
                                              fun (hy₁ : r = (i, y₁) ∧ y₁ ∈ i) =>
                                                Exists.elim pj_sepc (
                                                  fun (y₂) =>
                                                    fun (hy₂ : r = (j, y₂) ∧ (y₂ ∈ j)) =>
                                                      let ijy := Eq.trans (Eq.symm (And.left hy₁)) (And.left hy₂)
                                                      inj (And.left (Iff.mp (ordered_pair_set_prop i y₁ j y₂) (ijy)))
                                                )
                                          )

                                    )
                                )

                          )
                    )

          let ACNI₂ := ACNI₁ Afninter

          Exists.elim ACNI₂
          (
            fun (g) =>
              fun (hg : g Choice Af) =>

                let Q := fun (a) => snd_coor (g⦅f _ a⦆)

                let ψ := lam_fun A (⋃ A) Q

                let ch := fun (a) => fun (ha : a ∈ A) =>
                  let u := And.right hg (f _ a) (
                    Iff.mpr (In (f _ a)) (Exists.intro a (And.intro ha (Eq.refl (f _ a))))
                  )
                  let v : f _ a  = P a := And.right f_prop a (ha)
                  let v₂ := eq_subst (fun (t) => g⦅f _ a⦆ ∈ t) (f _ a) (P a) (v) (u)
                  let R := fun (t) => ∃ y, t = (a, y) ∧ y ∈ a
                  let v₃ := specification_set_subset R (A × ⋃ A) (g⦅f _ a⦆) v₂
                  snd_coor_set A (⋃ A) (g⦅f _ a⦆) v₃

                let func_prop := lam_then_fun_prop Q A (⋃ A) (ch)



                Exists.intro ψ (And.intro (And.left func_prop) (
                  fun (a) =>
                    fun (ha : a ∈ A) =>
                      let u₀ : ψ ⦅a⦆ = Q a := And.right func_prop a ha
                      let u := And.right hg (f _ a) (
                          Iff.mpr (In (f _ a)) (Exists.intro a (And.intro ha (Eq.refl (f _ a))))
                      )
                      let v : f _ a = P a := And.right (f_prop) a ha
                      let v₂ := eq_subst (fun (t) => g⦅f _ a⦆ ∈ t) (f _ a) (P a) (v) (u)
                      let R := fun (t) => ∃ y, t = (a, y) ∧ y ∈ a
                      let v₃ := And.right (Iff.mp (specification_set_is_specification R (A × (⋃ A)) (g⦅f _ a⦆)) v₂)
                      Exists.elim v₃ (
                        fun (y) =>
                          fun (hy : g⦅f _ a⦆ = (a, y) ∧ y ∈ a) =>
                            eq_subst (fun (t) => t ∈ a) (Q a) (ψ ⦅a⦆) (Eq.symm u₀) (
                              eq_subst (fun (t) => snd_coor t ∈ a) ((a, y)) (g⦅f _ a⦆) (Eq.symm (And.left hy)) (
                                eq_subst (fun (t) => t ∈ a) y (snd_coor (a, y)) (Eq.symm (coordinates_snd_corr a y)) (And.right hy)
                              )
                            )
                      )
                ))
          )
  )



def right_rev_criterion_prop : Prop := ∀ f A B, (f RightRev A To B) ↔ (f Surj A To B)





theorem rightrev_criterion_AC_eq:
  choice_ax ↔ right_rev_criterion_prop :=
  Iff.intro (
    fun (AC : choice_ax) =>
      fun (f A B) =>
    Iff.intro
    (
      surjection_condition f A B
    )
    (
      fun (hsurj : (f Surj A To B)) =>
        let h := And.left hsurj
        And.intro h (

          let X := 𝒫 A \ {∅}

          let first : ∅ ∉ X := fun (hempty : ∅ ∈ X) =>
              And.right (Iff.mp (difference_prop (𝒫 A) ({∅}) ∅) hempty) (elem_in_singl ∅)


          let second := union_boolean A
          let third := equality_then_subset (⋃ (𝒫 A)) (A) second
          let fourth := difference_subset_prop (𝒫 A) ({∅})
          let fifth := union_subset_monotonic (𝒫 A \ {∅}) (𝒫 A) fourth
          let fifth := subset_trans_curry (⋃ X) (⋃ (𝒫 A)) A fifth third

          let sixth : A ⊆ ⋃ X := fun (x) => fun (hx : x ∈ A) =>
            Iff.mpr (union_set_is_union X x) (Exists.intro ({x}) (
              And.intro (
                Iff.mpr (difference_prop (𝒫 A) ({∅}) {x}) (
                  And.intro (
                    Iff.mpr (boolean_set_is_boolean A {x}) (
                      fun (t) =>
                        fun (hxp : t ∈ {x}) =>
                          let r := in_singl_elem x t hxp
                          eq_subst (fun (el) => el ∈ A) x t (Eq.symm r) (hx)
                    )
                  ) (fun (hxempty : {x} ∈ {∅}) =>
                      let s := in_singl_elem ∅ {x} hxempty
                      empty_set_is_empty x (eq_subst (fun (elem) => x ∈ elem) {x} ∅ (s) (elem_in_singl x))
                  )
                )

              ) (elem_in_singl x)
            ))

          let seventh := Iff.mp (subs_subs_eq A (⋃ X)) (And.intro (sixth) (fifth))

          let eighth := AC X first

          Exists.elim eighth
          (
            fun (ξ) =>
              fun (hξ : (ξ Fun X To (⋃ X)) ∧ ∀ C ∈ X; ξ⦅C⦆ ∈ C) =>
                let hfun₀ := And.left hξ
                let hfun := eq_subst (fun (St) => ξ Fun X To St) (⋃ X) (A) (Eq.symm seventh) (hfun₀)
                let hprop := And.right hξ

                let g := lam_fun B A (fun (b) => ξ⦅f⁻¹.[{b}]⦆)

                Exists.intro g (


                  let surjprop : ∀ b ∈ B; f⁻¹.[{b}] ≠ ∅ := fun (b) =>
                    fun (hb : b ∈ B) =>
                      let u := And.right (hsurj) b hb
                      Exists.elim u
                      (
                        fun (y) =>
                          fun (hy : (y, b) ∈ f) =>
                            let fbinaryrel := And.left (prop_then_binary_relation A B f (And.left (And.left h)))
                            let ydomf := Iff.mpr (dom_prop f y) (Exists.intro b hy)
                            let St := dom f
                            let P := fun (a) => ∃ c ∈ {b}; (a . f . c)
                            let preimprop : f⁻¹.[{b}] = specification_set (fun x => P x) St := rel_pre_image_eq {b} f fbinaryrel
                            let finvpreimgprop₀ := Iff.mpr (specification_set_is_specification P St y) (
                              And.intro (ydomf) (Exists.intro b (And.intro (elem_in_singl b) (hy)))
                            )
                            let finvpreimgprop :=
                            eq_subst (fun (Stt) => y ∈ Stt) ({a ∈ dom f | ∃ y ∈ {b}; (a . f . y)}) (f⁻¹.[{b}]) (
                              Eq.symm (preimprop)) (finvpreimgprop₀)

                            fun (hemptyinv : f⁻¹.[{b}] = ∅) =>
                                empty_set_is_empty y (eq_subst (fun (Sttt) => y ∈ Sttt) (f⁻¹.[{b}]) (∅)
                                 (hemptyinv) (finvpreimgprop))
                      )



                    let surjprop₂ : ∀ b ∈ B; (f⁻¹.[{b}] ∈ X) := fun (b) => fun (hb : b ∈ B) =>
                      Iff.mpr (difference_prop (𝒫 A) ({∅}) (f⁻¹.[{b}])) (
                        And.intro (

                          Iff.mpr (boolean_set_is_boolean A (f⁻¹.[{b}])) (
                            let fbinaryrel := And.left (prop_then_binary_relation A B f (And.left (And.left h)))
                            let St := dom f
                            let P := fun (a) => ∃ c ∈ {b}; (a . f . c)
                            let N := {a ∈ St | P a}
                            let preimprop : f⁻¹.[{b}] = specification_set (fun x => P x) St := rel_pre_image_eq {b} f fbinaryrel
                            eq_subst (fun (sttt) => sttt ⊆ A) (N) (f⁻¹.[{b}]) (Eq.symm preimprop) (

                              subset_trans_curry (N) (dom f) (A) (
                                specification_set_subset P St
                              ) (dom_partial_function f A B (And.left h))
                            )
                          )
                        ) (
                          fun (hemptyprop : f⁻¹.[{b}] ∈ {∅}) =>
                            surjprop b hb (in_singl_elem ∅ (f⁻¹.[{b}]) hemptyprop)
                        )
                      )

                    let surjprop₃ : ∀ b ∈ B; ξ⦅f⁻¹.[{b}]⦆ ∈ A := fun (b) => fun (hb : b ∈ B) =>
                      val_in_B ξ X A hfun (f⁻¹.[{b}]) (surjprop₂ b hb)

                    let g_correct_func := And.left (lam_then_fun_prop (fun (b) => ξ⦅f⁻¹.[{b}]⦆) B A surjprop₃)

                    And.intro (

                      g_correct_func

                    ) (
                        Iff.mpr (equal_functions_abc_A (f ∘ g) (id_ B) B B B (

                          And.left (function_composition_A g f B A B g_correct_func h)

                        ) (
                          And.left (id_is_bij B)
                        ))
                        (

                          fun (b) =>
                            fun (hb : b ∈ B) =>
                              let u := Iff.mp (function_equal_value_prop (id_ B) B B (And.left (id_is_bij B)) b b hb) (prop_then_id B b hb)
                              Eq.trans (

                                let v := And.right (function_composition_A g f B A B g_correct_func h) b hb

                                Eq.trans (v) (

                                  let g_prop : g⦅b⦆ = ξ⦅f⁻¹.[{b}]⦆
                                   := And.right (lam_then_fun_prop (fun (b) => ξ⦅f⁻¹.[{b}]⦆) B A surjprop₃) b hb

                                  let fg_prop : f⦅g⦅b⦆⦆ = f⦅ξ⦅f⁻¹.[{b}]⦆⦆
                                   := eq_subst (fun (t) => f⦅g⦅b⦆⦆ = f⦅t⦆) (g⦅b⦆) (ξ⦅f⁻¹.[{b}]⦆) (g_prop) (Eq.refl (f⦅g⦅b⦆⦆))

                                  Eq.trans (fg_prop) (
                                    let U := ξ⦅f⁻¹.[{b}]⦆

                                    Eq.symm (
                                      Iff.mp (function_equal_value_prop f A B h (U) b (surjprop₃ b hb)) (



                                        let axiom_prop : U ∈ f⁻¹.[{b}] := hprop (f⁻¹.[{b}]) (surjprop₂ b hb)
                                        let fbinaryrel := And.left (prop_then_binary_relation A B f (And.left (And.left h)))
                                        let St := dom f
                                        let P := fun (a) => ∃ c ∈ {b}; (a . f . c)
                                        let N := {a ∈ St | P a}
                                        let preimprop : f⁻¹.[{b}] = specification_set (fun x => P x) St :=
                                        rel_pre_image_eq  {b} f fbinaryrel

                                        let axiom_prop_preim : U  ∈ {a ∈ St | P a} :=
                                          eq_subst (fun (t) => U ∈ t) (f⁻¹.[{b}]) N (preimprop) (axiom_prop)

                                        let spec_prop := And.right (Iff.mp (specification_set_is_specification P St (U)) axiom_prop_preim)

                                        Exists.elim spec_prop
                                        (
                                          fun (c) =>
                                            fun (hc : c ∈ {b} ∧ (U . f . c)) =>
                                              let cbeq := in_singl_elem b c (And.left hc)
                                              eq_subst (fun (t) => (U, t) ∈ f) c b (cbeq) (And.right hc)
                                        )
                                      )
                                    )
                                  )
                                )
                              ) (u)
                        )
                      )
                )
          )
        )
    )
  ) (
    fun (rev_crit : right_rev_criterion_prop) =>
      Iff.mpr (AC_inter_eq_AC) (
        fun (A) =>
          fun (hnempty : ∅ ∉ A) =>
            fun (hnint : (∀ B C ∈ A; B ≠ C → B ∩ C = ∅)) =>

              let exi_uni_property : ∀ a ∈ ⋃ A; ∃! t ∈ A; a ∈ t := fun (a) => fun (ha : a ∈ ⋃ A) =>
                let un_prop := Iff.mp (union_set_is_union A a) ha
                Exists.elim un_prop
                (
                  fun (y) =>
                    fun (hy : y ∈ A ∧ a ∈ y) =>
                      Exists.intro y (And.intro (hy) (
                        fun (z) =>
                          fun (hz : z ∈ A ∧ a ∈ z) =>
                            Or.elim (em (y = z))
                            (
                              fun (hyz : (y = z)) =>
                                hyz
                            )
                            (
                              fun (hnyz : (y ≠ z)) =>
                                let inter := hnint y (And.left hy) z (And.left hz) hnyz
                                let interyza := Iff.mpr (intersect_2sets_prop y z a) (And.intro (And.right hy) (And.right hz))
                                let aempt : a ∈ ∅ := eq_subst (fun (t) => a ∈ t) (y ∩ z) (∅) (inter) (interyza)
                                False.elim (empty_set_is_empty a (aempt))

                            )

                      ))
                )


              let P := fun (z) => ∃ x y, z = (x, y) ∧ x ∈ y


              let g := {z ∈ (⋃ A) × A | P z}


              let g_bin_prop : binary_relation_between (⋃ A) A g := specification_set_subset P ((⋃ A) × A)

              let g_func_prop : is_functional g := fun (x y z) =>
                fun (hxy : (x . g . y)) =>
                  fun (hxz : (x . g . z)) =>
                    Or.elim (em (x ∈ ⋃ A))
                    (
                      fun (hxA : x ∈ ⋃ A) =>
                        let exi_uni_prop := exi_uni_property x hxA
                        Exists.elim exi_uni_prop (
                          fun (t) =>
                            fun (ht : (t ∈ A ∧ x ∈ t) ∧ ∀ s, ((s ∈ A ∧ x ∈ s) → t = s)) =>
                              let yA := And.right ((Iff.mp (cartesian_product_pair_prop (⋃ A) (A) x y) (g_bin_prop (x, y) hxy) ))
                              let zA := And.right ((Iff.mp (cartesian_product_pair_prop (⋃ A) (A) x z) (g_bin_prop (x, z) hxz) ))
                              let yspec := Exists.elim (
                                And.right (Iff.mp (specification_set_is_specification P ((⋃ A) × A) (x, y)) hxy))
                                (
                                  fun (x₀) =>
                                    fun (hx₀ : ∃ y₀, (x, y) = (x₀, y₀) ∧ x₀ ∈ y₀) =>
                                      Exists.elim hx₀ (
                                        fun (y₀) =>
                                          fun (hy₀ : (x, y) = (x₀, y₀) ∧ x₀ ∈ y₀) =>
                                            let v := Iff.mp (ordered_pair_set_prop x y x₀ y₀) (And.left hy₀)
                                            eq_subst (fun (t) => t ∈ y) (x₀) (x) (Eq.symm (And.left v)) (
                                              eq_subst (fun (s) => x₀ ∈ s) (y₀) (y) (Eq.symm (And.right v)) (And.right hy₀)
                                            )
                                      )
                                )

                              let zspec := Exists.elim (
                                And.right (Iff.mp (specification_set_is_specification P ((⋃ A) × A) (x, z)) hxz))
                                (
                                  fun (x₀) =>
                                    fun (hx₀ : ∃ z₀, (x, z) = (x₀, z₀) ∧ x₀ ∈ z₀) =>
                                      Exists.elim hx₀ (
                                        fun (z₀) =>
                                          fun (hz₀ : (x, z) = (x₀, z₀) ∧ x₀ ∈ z₀) =>
                                            let v := Iff.mp (ordered_pair_set_prop x z x₀ z₀) (And.left hz₀)
                                            eq_subst (fun (t) => t ∈ z) (x₀) (x) (Eq.symm (And.left v)) (
                                              eq_subst (fun (s) => x₀ ∈ s) (z₀) (z) (Eq.symm (And.right v)) ((And.right hz₀)
                                            )
                                      )
                                    )
                                )

                              let propt₁ := And.right ht y (And.intro (yA) (yspec))
                              let propt₂ := And.right ht z (And.intro (zA) (zspec))

                              Eq.trans (Eq.symm propt₁) (propt₂)


                        )
                    )
                    (fun (hnxA : x ∉ ⋃ A) =>
                      let u := g_bin_prop (x, y) hxy
                      let v := And.left (Iff.mp (cartesian_product_pair_prop (⋃ A) (A) x y) u)
                      False.elim (hnxA (v))
                    )

              let g_tot_prop : is_total g (⋃ A) := fun (x) => fun (hx : x ∈ ⋃ A) =>
                let exi_uni_prop := exi_uni_property x hx
                Exists.elim exi_uni_prop (
                  fun (y) =>
                    fun (hy : (y ∈ A ∧ x ∈ y) ∧ ∀ z, ((z ∈ A ∧ x ∈ z) → y = z)) =>
                      Exists.intro y (
                        Iff.mpr (specification_set_is_specification P ((⋃ A) × A) (x, y)) (
                          And.intro (Iff.mpr (cartesian_product_pair_prop (⋃ A) A x y) (And.intro (hx) (And.left (And.left hy))))
                          (Exists.intro x (Exists.intro y (And.intro (Eq.refl (x, y)) (And.right (And.left hy)))))
                        )
                      )
                )

              let g_surj_prop : is_surjective g A := fun (y) => fun (hy : y ∈ A) =>
                let hy_nempt := fun (hy_empt : y = ∅) =>
                  hnempty (eq_subst (fun (t) => t ∈ A) y (∅) (hy_empt) hy)
                let exi_pr := non_empty_uni_then_exi (fun (_) => True) y (hy_nempt) (fun (t) => fun (_ : t ∈ y) => True.intro)
                Exists.elim exi_pr (
                  fun (x) =>
                    fun (hx : x ∈ y ∧ True) =>
                      Exists.intro x (
                        Iff.mpr (specification_set_is_specification P ((⋃ A) × A) (x, y)) (
                          And.intro (Iff.mpr (cartesian_product_pair_prop (⋃ A) (A) x y) (And.intro (
                            Iff.mpr (union_set_is_union A x) (Exists.intro y (And.intro (hy) (And.left hx)))
                          ) (hy)) ) (
                            Exists.intro x (Exists.intro y (And.intro (Eq.refl (x, y)) (And.left hx)))
                          )
                        )

                      )
                )


              let gsurj : g Surj (⋃ A) To A
              := And.intro (And.intro (And.intro (g_bin_prop) (g_func_prop)) (g_tot_prop)) (g_surj_prop)


              let grightrev := And.right (Iff.mpr (rev_crit g (⋃ A) A) gsurj)

              Exists.elim grightrev
              (
                fun (f) =>
                  fun (hf : (f Fun A To (⋃ A)) ∧ (g ∘ f = id_ A)) =>
                      Exists.intro f (And.intro (And.left hf) (

                        fun (x) =>
                          fun (hx : x ∈ A) =>

                            let gfid_x : (g ∘ f)⦅x⦆ = (id_ A)⦅x⦆ :=
                              eq_subst (fun (t) => (g ∘ f)⦅x⦆ = t⦅x⦆) (g ∘ f) (id_ A) (And.right hf) (Eq.refl ((g ∘ f)⦅x⦆))
                            let ida_x := And.left (And.left (id_prop A x ((id_ A)⦅x⦆) (
                              let u := And.left (id_is_bij A)
                              function_value_pick_property (id_ A) A A x (hx) u
                                )
                              )
                            )

                            let comp_x := And.right (function_composition_A f g (A) (⋃ A) (A) (And.left hf) (And.left gsurj)) x hx

                            let eq_res := Eq.trans (Eq.symm (comp_x)) (Eq.trans (gfid_x) (Eq.symm ida_x))

                            let valx_in := val_in_B f (A) (⋃ A) (And.left hf) x hx

                            let in_res := Iff.mpr (function_equal_value_prop g (⋃ A) (A) (And.left gsurj) (f⦅x⦆) (x) valx_in) (
                              Eq.symm eq_res
                            )

                            let spec_g_fxx := And.right (Iff.mp (specification_set_is_specification P (⋃ A × A) (f⦅x⦆, x)) in_res)

                            Exists.elim spec_g_fxx
                            (
                              fun (x₀) =>
                                fun (hx₀ : ∃ y₀, (f⦅x⦆, x) = (x₀, y₀) ∧ x₀ ∈ y₀) =>
                                    Exists.elim hx₀
                                    (
                                      fun (y₀) =>
                                        fun (hy₀ : (f⦅x⦆, x) = (x₀, y₀) ∧ x₀ ∈ y₀) =>
                                          let ord_fin := Iff.mp (ordered_pair_set_prop (f⦅x⦆) x (x₀) (y₀)) (And.left hy₀)
                                          let prefin := eq_subst (fun (t) => x₀ ∈ t) (y₀) (x) (Eq.symm (And.right ord_fin)) (And.right hy₀)
                                          eq_subst (fun (t) => t ∈ x) (x₀) (f⦅x⦆) (Eq.symm (And.left (ord_fin))) (prefin)
                                    )
                            )
                      ))
              )

      )

  )





noncomputable def indexed_product (A I : Set) := {f ∈ ((⋃[ i in I ] A at i) ℙow (I)) | ∀ i ∈ I; f⦅i⦆ ∈ (A _ i)}
syntax "∏[" term "in" term "]" term "at" term : term
macro_rules
  |  `(∏[ $_:term in $I:term ] $A:term at $_:term ) => `(indexed_product $A $I)
def product_non_empty_prop : Prop := (∀ A I, (A IndxFun I) → (∀ I ∈ I; (A _ I) ≠ ∅) → (∏[ i in I ] A at i) ≠ ∅)


theorem lemma_power_emp : ∀ A B, (A = ∅) → ((B ℙow A) = {∅}) :=
  fun (A B) =>
    fun (hAemp : (A = ∅)) =>
      extensionality (B ℙow A) {∅} (
        fun (t) =>
          Iff.intro
          (
            fun (ht : t ∈ B ℙow A) =>
              eq_subst (fun (r) => r ∈ {∅}) (∅) t (Eq.symm (
                extensionality t (∅) (fun (u) =>
                Iff.intro (
                  fun (hut : u ∈ t) =>
                    let v := And.left (And.left (Iff.mp (power_set_prop A B t) ht)) u hut
                    let m := Iff.mp (cartesian_product_is_cartesian A B u) v
                    Exists.elim m
                    (
                      fun (x) =>
                        fun (hx : x ∈ A ∧ ∃ y ∈ B; u = (x, y)) =>
                          False.elim (
                            empty_set_is_empty x (
                              eq_subst (fun (i) => x ∈ i) (A) (∅) (hAemp) (And.left hx)
                            )
                          )
                    )
                ) (empty_set_is_subset_any t u))
              )) (elem_in_singl ∅)
          )
          (
            fun (ht : t ∈ {∅}) =>
              let u := in_singl_elem ∅ t ht
              eq_subst (fun (i) => i ∈ (B ℙow A)) ∅ t (Eq.symm u) (
                Iff.mpr (power_set_prop A B ∅) (
                  And.intro (And.intro (empty_set_is_subset_any (A × B)) (
                    fun (x y _) =>
                      fun (hxy : (x . ∅ . y)) =>
                        False.elim (
                          empty_set_is_empty (x, y) (hxy)
                        )
                  )) (
                    fun (x) =>
                      fun (hx : x ∈ A) =>
                        let u := eq_subst (fun (i) => x ∈ i) A ∅ (hAemp) (hx)
                        False.elim (
                          empty_set_is_empty x u
                        )
                  )
                )
              )
          )
      )


theorem prod_pow_emp : ∀ A I B, (I = ∅) → (∏[ i in I ] A at i) = B ℙow I :=
  fun (A I B) =>
    fun (hI : (I = ∅)) =>
          extensionality (∏[ i in I ] A at i) (B ℙow I) (
            fun (f) =>
              Iff.intro
              (
                fun (hf : f ∈ (∏[ i in I ] A at i)) =>
                  let P := fun (f) => ∀ i ∈ I; f⦅i⦆ ∈ (A _ i)
                  let S := ((⋃[ i in I ] A at i) ℙow (I))
                  let res₁ := specification_set_subset P S f hf
                  let res₂ := lemma_power_emp I (⋃[ i in I ] A at i) hI
                  let res₃ := lemma_power_emp I B hI
                  let res₄ := Eq.trans (res₂) (Eq.symm res₃)
                  eq_subst (fun (M) => f ∈ M) S (B ℙow I) (res₄) (res₁)
              )
              (
                fun (hf : f ∈ (B ℙow I)) =>
                  let P := fun (f) => ∀ i ∈ I; f⦅i⦆ ∈ (A _ i)
                  let S := ((⋃[ i in I ] A at i) ℙow (I))
                  let res₂ := lemma_power_emp I (⋃[ i in I ] A at i) hI
                  let res₃ := lemma_power_emp I B hI
                  let res₄ := Eq.trans (res₂) (Eq.symm res₃)
                  let res₅ := eq_subst (fun (M) => f ∈ M) (B ℙow I) S (Eq.symm (res₄)) (hf)
                  Iff.mpr (specification_set_is_specification P S f) (
                    And.intro (res₅) (fun (i) =>
                      fun (hi : i ∈ I) =>
                        False.elim (
                          empty_set_is_empty i (
                            eq_subst (fun (M) => i ∈ M) I ∅ (hI) (hi)
                          )
                        )
                    )
                  )
              )
          )




theorem prod_pow_nemp : ∀ A I B, (I ≠ ∅) → (A Indx I) → (∀ i ∈ I; (A _ i = B)) → (∏[ i in I ] A at i) = B ℙow I :=
  fun (A I B) =>
    fun (hI : (I ≠ ∅)) =>
      fun (hAI : (A Indx I)) =>
          fun (hB : ∀ i ∈ I; (A _ i = B)) =>
            let u := extensionality (⋃[ i in I ] A at i) (B) (
              fun (t) =>
                Iff.intro
                (
                  fun (ht : t ∈ (⋃[ i in I ] A at i)) =>
                    let u := Iff.mp (indexed_union_is_union A I hAI t) ht
                    Exists.elim u (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ t ∈ (A _ i)) =>
                          eq_subst (fun (r) => t ∈ r) (A _ i) B (hB i (And.left hi)) (And.right hi)
                    )
                )
                (
                  fun (ht : t ∈ B) =>
                    let u := Iff.mpr (indexed_union_is_union A I hAI t)
                    let v := non_empty_uni_then_exi (fun (i) => (A _ i = B)) I hI hB

                    Exists.elim v (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ A _ i = B) =>
                          u (
                            Exists.intro i (And.intro (And.left hi) (
                              eq_subst (fun (r) => t ∈ r) B (A _ i) (Eq.symm (And.right hi)) (ht)
                            ))
                          )
                    )



                )
            )
            extensionality ((∏[ i in I ] A at i)) (B ℙow I) (
              fun (t) =>
                Iff.intro
                (
                  fun (ht : t ∈ (∏[ i in I ] A at i)) =>
                    let P := fun (f) => ∀ i ∈ I; f⦅i⦆ ∈ (A _ i)
                    let S := ((⋃[ i in I ] A at i) ℙow (I))
                    let res₁ := specification_set_subset P S t ht
                    eq_subst (fun (m) => t ∈ m ℙow I) ((⋃[ i in I ] A at i)) (B) (u) (res₁)
                )
                (
                  fun (ht : t ∈ (B ℙow I)) =>
                    let P := fun (f) => ∀ i ∈ I; f⦅i⦆ ∈ (A _ i)
                    let S := ((⋃[ i in I ] A at i) ℙow (I))
                    let res₁ := eq_subst (fun (m) => t ∈ m ℙow I) (B) ((⋃[ i in I ] A at i)) (Eq.symm u) (ht)
                    Iff.mpr (specification_set_is_specification P S t) (
                      And.intro (res₁) (
                        fun (i) =>
                          fun (hi : i ∈ I) =>
                            let res₂ := Iff.mp (power_set_prop I B t) ht
                            let res₃ := val_in_B t I B (res₂) i hi
                            eq_subst (fun (R) => (t⦅i⦆) ∈ R) B (A _ i) (Eq.symm (hB i hi)) (res₃)
                      )
                    )
                )
            )



theorem prod_pow : ∀ A I B, (A Indx I) → (∀ i ∈ I; (A _ i = B)) → (∏[ i in I ] A at i) = B ℙow I :=
  fun (A I B) =>
    fun (hI : (A Indx I)) =>
      fun (hi : (∀ i ∈ I; (A _ i = B))) =>
        Or.elim (em (I = ∅))
        (
          fun (hemp : (I = ∅)) =>
            prod_pow_emp A I B hemp
        )
        (fun (hnemp : (I ≠ ∅)) =>
            prod_pow_nemp A I B hnemp hI hi
        )




theorem product_AC_eq : choice_ax ↔ product_non_empty_prop :=
  Iff.intro
  (
    fun (h : (∀ A, (∅ ∉ A) → ∃ f, f Choice A)) =>
      fun (A I) =>
        fun (hind : (A IndxFun I)) =>
          fun (hnempty : (∀ I ∈ I; (A _ I) ≠ ∅)) =>
            let first : ∅ ∉ A.[I] := fun (s : ∅ ∈ A.[I]) =>
              let second := Iff.mp (fun_indexed_is_indexed A I hind ∅) s
              Exists.elim second
              (
                fun (i) =>
                  fun (hi : i ∈ I ∧ ∅ = (A _ i)) =>
                    hnempty i (And.left hi) (Eq.symm (And.right hi))

              )
            let second := h (A.[I]) first
            Exists.elim second
            (
              fun (g) =>
                fun (hg : (g Fun A.[I] To (⋃[ i in I ] A at i)) ∧ (∀ X ∈ A.[I]; g⦅X⦆ ∈ X)) =>
                  let f := lam_fun I (A.[I]) (fun (i) => (A _ i))
                  let third := lam_then_fun_prop (fun (i) => (A _ i)) I (A.[I]) (
                    fun (i) => fun (hi : i ∈ I) =>
                      let hindx := fun_indexed_is_indexed A I hind
                      Iff.mpr (hindx (A _ i)) (Exists.intro i (And.intro (hi) (Eq.refl (A _ i))))
                  )

                  let fourth : f Fun I To A.[I] := And.left third
                  let fifth : ∀ i ∈ I; f⦅i⦆ = (A _ i) := And.right third
                  fun (hempty : (∏[ i in I ] A at i) = ∅) =>
                    empty_set_is_empty (g ∘ f) (
                      eq_subst (fun (t) => (g ∘ f) ∈ t) (∏[ i in I ] A at i) (∅) (hempty) (
                        let ST := ((⋃[ i in I ] A at i) ℙow (I))
                        let P := fun (f) => ∀ i ∈ I; f⦅i⦆ ∈ (A _ i)
                        Iff.mpr (specification_set_is_specification P ST (g ∘ f)) (

                          let func_comp_prop := function_composition_A f g I (A.[I]) (⋃[ i in I ] A at i) fourth (And.left hg)

                          And.intro (

                            Iff.mpr (power_set_prop I (⋃[ i in I ] A at i) (g ∘ f)) (And.left (func_comp_prop))

                          ) (

                            fun (i) => fun (hi : i ∈ I) =>

                              eq_subst (fun (t) => t ∈ (A _ i)) (g⦅f⦅i⦆⦆) ((g ∘ f)⦅i⦆) (Eq.symm (And.right func_comp_prop i (hi))) (

                                let u := fifth i hi

                                let v := eq_subst (fun (t) => g⦅t⦆ = g⦅f⦅i⦆⦆) (f⦅i⦆) (A _ i) (u) (Eq.refl (g⦅f⦅i⦆⦆))

                                eq_subst (fun (t) => t ∈ (A _ i)) (g⦅A _ i⦆) (g⦅f⦅i⦆⦆) (v) (
                                  And.right hg (A _ i) (
                                    Iff.mpr (fun_indexed_is_indexed A I hind (A _ i)) (Exists.intro i (
                                      And.intro (hi) (Eq.refl (A _ i))
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
  (
    fun (hAI : (∀ A I, (A IndxFun I) → (∀ I ∈ I; (A _ I) ≠ ∅) → (∏[ i in I ] A at i) ≠ ∅)) =>
      fun (B) => fun (hB : ∅ ∉ B) =>
        let Afunc := lam_fun B B (fun (i) => i)
        let first := hAI Afunc B
        let second := lam_then_fun_prop (fun (i) => i) B B (
          fun (x) => fun (hx : x ∈ B) => hx
        )
        let third := And.left second
        let fourth : ∃ X, (Afunc Fun B To X) := Exists.intro (B) third
        let fifth := first fourth

        let sixth := fun (i) => fun (hi : i ∈ B) =>
          fun (hempty : Afunc⦅i⦆ = ∅) =>
            hB (eq_subst (fun (t) => t ∈ B) (Afunc⦅i⦆) (∅) (hempty) (
              eq_subst (fun (t) => t ∈ B) (i) (Afunc⦅i⦆) (Eq.symm (And.right second i hi)) (hi)
            ))

        let seventh := fifth sixth

        let eight := Iff.mpr (morgan_exi Set (fun (i) => i ∉ (∏[ i in B ] Afunc at i))) (
          fun (hempty : ∀ x, x ∉ (∏[ i in B ] Afunc at i)) =>
            seventh (Iff.mp (subs_subs_eq (∏[ i in B ] Afunc at i) (∅)) (And.intro (
              fun (t) => fun (ht : t ∈ (∏[ i in B ] Afunc at i)) =>
                False.elim (hempty t (ht))
            ) (empty_set_is_subset_any (∏[ i in B ] Afunc at i))))
        )


        let nine := Exists.elim eight (
          fun (t) => fun (ht :  ¬ (t ∉ (∏[ i in B ] Afunc at i))) =>
            Exists.intro t (byContradiction ht)
        )

        Exists.elim nine (
          fun (f) => fun (hf : f ∈ (∏[ i in B ] Afunc at i)) =>
            Exists.intro f (

              And.intro (

                let ST := ((⋃[ i in B ] Afunc at i) ℙow (B))
                let P := fun (g) => ∀ i ∈ B; g⦅i⦆ ∈ (Afunc _ i)
                let tenth := specification_set_subset P ST f (hf)
                let eleventh := Iff.mp (power_set_prop B (⋃[ i in B ] Afunc at i) f) tenth


                let twelveth := extensionality (⋃ B) (⋃[ i in B ] Afunc at i) (
                  fun (x) =>
                    Iff.intro
                    (
                      fun (hx : x ∈ ⋃ B) =>
                        let un_prop := Iff.mp (union_set_is_union B x) hx
                        Exists.elim un_prop
                        (
                          fun (y) =>
                            fun (hy : y ∈ B ∧ x ∈ y) =>
                              Iff.mpr (indexed_union_is_union Afunc B (fun_indexed_is_indexed Afunc B fourth) x) (
                                Exists.intro y (And.intro (And.left hy) (
                                  eq_subst (fun (t) => x ∈ t) (y) (Afunc⦅y⦆) (Eq.symm (And.right second y (And.left hy))) (And.right hy)
                                ))
                            )
                        )


                    )
                    (
                      fun (hx : (x ∈ (⋃[ i in B ] Afunc at i))) =>
                        let u := fun_indexed_is_indexed Afunc B fourth
                        let v := Iff.mp (indexed_union_is_union Afunc B u x) hx
                        Exists.elim v
                        (
                          fun (y) =>
                            fun (hy : y ∈ B ∧ x ∈ (Afunc _ y)) =>
                              Iff.mpr (union_set_is_union B x) (
                                Exists.intro y (And.intro (And.left hy) (
                                  eq_subst (fun (t) => x ∈ t) (Afunc _ y) y (And.right second y (And.left hy)) (And.right hy)
                                ))
                              )
                        )
                    )
                )

                eq_subst (fun (t) => f Fun B To t) (⋃[ i in B ] Afunc at i) (⋃ B) (Eq.symm (twelveth)) (eleventh)

              ) (

                fun (x) => fun (hx : x ∈ B) =>
                  let ST := ((⋃[ i in B ] Afunc at i) ℙow (B))
                  let P := fun (g) => ∀ i ∈ B; g⦅i⦆ ∈ (Afunc _ i)
                  let u := And.right (Iff.mp (specification_set_is_specification P ST f) (hf)) x hx
                  eq_subst (fun (t) => f⦅x⦆ ∈ t) (Afunc _ x) x (And.right second x hx) (u)

              )

            )
        )
  )
