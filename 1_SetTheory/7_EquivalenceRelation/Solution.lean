import «Header»

def equivalence_relation (A R : Set) := (R BinRelOn A) ∧ (refl R A) ∧ (symm R) ∧ (transit R)
syntax term "EquivRel" term : term
macro_rules
| `($R EquivRel $A) => `(equivalence_relation $A $R)


theorem equivrel_refl : ∀ A R, (R EquivRel A) → (refl R A) :=
  fun (_) =>
    fun (_) =>
      fun (hRA) =>
        And.left (And.right hRA)


theorem equivrel_symm : ∀ A R, (R EquivRel A) → (symm R) :=
  fun (_) =>
    fun (_) =>
      fun (hRA) =>
        And.left (And.right (And.right hRA))


theorem equivrel_trans : ∀ A R, (R EquivRel A) → (transit R) :=
  fun (_) =>
    fun (_) =>
      fun (hRA) =>
        And.right (And.right (And.right hRA))


noncomputable def eqrelset (A : Set) := {R ∈ 𝒫 (A × A) | R EquivRel A}
syntax "Eq" term : term
macro_rules
| `(Eq $A) => `(eqrelset $A)

theorem eqrel_crit : ∀ A R, (R ∈ Eq A) ↔ (R EquivRel A) :=
  fun (A R) =>
    let P := fun (R) => (R EquivRel A)
    let u₁ := spec_is_spec P (𝒫 (A × A))
    Iff.intro
    (
      fun (hR) =>
        And.right (Iff.mp (u₁ R) hR)
    )
    (
      fun (hR) =>
        Iff.mpr (u₁ R) (
          And.intro (Iff.mpr (boolean_set_is_boolean (A × A) R) (And.left hR)) (hR)
        )
    )

theorem id_eqrel : ∀ A, ((id_ A) EquivRel A) :=
  fun (A) =>
    let u₀ := id_is_binon A
    And.intro (u₀) (And.intro (prop_then_id A) (And.intro (
      fun (x y hxy) =>
        let u₁ := id_prop A x y hxy
        eq_subst (fun (t) => (t, x) ∈ id_ A) x y (And.left (And.left u₁)) (prop_then_id A x (And.right (And.left u₁)))
    ) (
      fun (x y z) =>
        fun (hxyz) =>
          let u₁ := id_prop A x y (And.left hxyz)
          let u₂ := id_prop A y z (And.right hxyz)
          let u₃ := Eq.trans (And.left (And.left u₁)) (And.left (And.left u₂))
          eq_subst (fun (t) => (x, t) ∈ id_ A) x z (u₃) (prop_then_id A x (And.right (And.left u₁)))
    )))

theorem allpairs_eqrel : ∀ A, ((A × A) EquivRel A) :=
  fun (A) =>
    let u₀ := subset_refl (A × A)
    And.intro u₀ (
      And.intro (
        fun (x hx) =>
          Iff.mpr (cartesian_product_pair_prop A A x x) (And.intro (hx) (hx))
      ) (
        And.intro (
          fun (x y hxy) =>
          let u₁ := Iff.mp (cartesian_product_pair_prop A A x y) hxy
          Iff.mpr (cartesian_product_pair_prop A A y x) (
            And.intro (And.right u₁) (And.left u₁)
          )
        ) (
          fun (x y z) =>
            fun (hxyz) =>
              let u₁ := Iff.mp (cartesian_product_pair_prop A A x y) (And.left hxyz)
              let u₂ := Iff.mp (cartesian_product_pair_prop A A y z) (And.right hxyz)
              Iff.mpr (cartesian_product_pair_prop A A x z) (
                And.intro (And.left u₁) (And.right u₂)
              )
        )
      )
    )


theorem eq_rel_between : ∀ A R, (R EquivRel A) → (((id_ A) ⊆ (R)) ∧ (R ⊆ (A × A))) :=
  fun (A R hRA) =>
    And.intro (Iff.mp (refl_crit A R (And.left hRA)) (And.left (And.right hRA))) (And.left hRA)


theorem equivrel_is_equivrel (φ : Set → Set → Prop) : ∀ A x y, (x, y) ∈ {R ∈ (A × A) | φ (π₁ R) (π₂ R)} ↔ (x ∈ A ∧ y ∈ A ∧ φ x y) :=
  fun (A x y) =>
    let B := A × A
    let P := fun (R) => φ (π₁ R) (π₂ R)
    let u₀ := spec_is_spec P B
    Iff.intro
    (
      fun (hxy) =>
        let u₁ := Iff.mp (u₀ (x, y) ) hxy
        let u₂ := Iff.mp (cartesian_product_pair_prop A A x y) (And.left u₁)
        let u₃ := And.right u₁
        let v₂ := eq_subst (fun (t) => φ x t) (π₂ (x, y)) y (coordinates_snd_coor x y) (
                eq_subst (fun (t) => φ t (π₂ (x, y))) (π₁ (x, y)) x (coordinates_fst_coor x y) (
                  u₃
                )
              )
        And.intro (And.left u₂) (And.intro (And.right u₂) (v₂))
    )
    (
      fun (hxy) =>
        let u₁ := Iff.mpr (cartesian_product_pair_prop A A x y) (And.intro (And.left hxy) (And.left (And.right hxy)))
        let v₅ := eq_subst (fun (t) => φ (π₁ (x, y)) t) y (π₂ (x, y)) (Eq.symm (coordinates_snd_coor x y)) (
                    eq_subst (fun (t) => φ t y) x (π₁ (x, y)) (Eq.symm (coordinates_fst_coor x y)) (
                    And.right (And.right hxy)
            )
        )
        Iff.mpr (u₀ (x, y)) (
          And.intro (u₁) (
            v₅
          )
        )
    )




theorem bin_equivrel (φ : Set → Set → Prop) :
∀ A, ((∀ x ∈ A; φ x x) ∧ (∀ x y, φ x y → φ y x) ∧ (∀ x y z, (φ x y ∧ φ y z) → (φ x z))) → ({R ∈ (A × A) | φ (π₁ R) (π₂ R)} EquivRel A) :=
  fun (A) =>
    fun (hφ) =>
      let B := A × A
      let P := fun (R) => φ (π₁ R) (π₂ R)
      let u₀ := specification_set_subset P B
      let u₂ := And.left hφ
      let u₃ := And.left (And.right hφ)
      let u₄ := And.right (And.right hφ)
      And.intro (u₀) (
        And.intro (
          fun (x hx) =>
            let u₁ := eq_subst (fun (t) => φ (π₁ (x, x)) t) (x) (π₂ (x, x)) (Eq.symm (coordinates_snd_coor x x)) (
              eq_subst (fun (t) => φ t x) (x) (π₁ (x, x)) (Eq.symm (coordinates_fst_coor x x)) (
                u₂ x hx
              )
            )
            Iff.mpr (spec_is_spec P B (x, x)) (And.intro (
              Iff.mpr (cartesian_product_pair_prop A A x x) (And.intro hx hx)
            ) (u₁))

        ) (
          And.intro (
            fun (x y hxy) =>
              let u₁ := Iff.mp (spec_is_spec P B (x, y)) hxy
              let v₁ := And.right u₁
              let v₂ := eq_subst (fun (t) => φ x t) (π₂ (x, y)) y (coordinates_snd_coor x y) (
                eq_subst (fun (t) => φ t (π₂ (x, y))) (π₁ (x, y)) x (coordinates_fst_coor x y) (
                  v₁
                )
              )
              let v₃ := u₃ x y v₂
              let v₄ := eq_subst (fun (t) => φ (π₁ (y, x)) t) x (π₂ (y, x)) (Eq.symm (coordinates_snd_coor y x)) (
                eq_subst (fun (t) => φ t x) y (π₁ (y, x)) (Eq.symm (coordinates_fst_coor y x)) (
                  v₃
                )
              )

              let v₅ := Iff.mp (cartesian_product_pair_prop A A x y) (And.left u₁)

              Iff.mpr (spec_is_spec P B (y, x)) (
                And.intro (Iff.mpr (cartesian_product_pair_prop A A y x) (
                  And.intro (And.right v₅) (And.left v₅)
                )) (v₄)
              )
          ) (
            fun (x y z) =>
              fun (hxyz) =>
                let u₁ := Iff.mp (spec_is_spec P B (x, y)) (And.left hxyz)
                let v₁ := Iff.mp (spec_is_spec P B (y, z)) (And.right hxyz)
                let v₂ := eq_subst (fun (t) => φ x t) (π₂ (x, y)) y (coordinates_snd_coor x y) (
                  eq_subst (fun (t) => φ t (π₂ (x, y))) (π₁ (x, y)) x (coordinates_fst_coor x y) (
                    And.right u₁
                  )
                )
                let v₃ := eq_subst (fun (t) => φ y t) (π₂ (y, z)) z (coordinates_snd_coor y z) (
                  eq_subst (fun (t) => φ t (π₂ (y, z))) (π₁ (y, z)) y (coordinates_fst_coor y z) (
                    And.right v₁
                  )
                )
                let v₄ := u₄ x y z (And.intro v₂ v₃)
                let v₅ := eq_subst (fun (t) => φ (π₁ (x, z)) t) z (π₂ (x, z)) (Eq.symm (coordinates_snd_coor x z)) (
                    eq_subst (fun (t) => φ t z) x (π₁ (x, z)) (Eq.symm (coordinates_fst_coor x z)) (
                    v₄
                  )
                )
                let v₆ := Iff.mp (cartesian_product_pair_prop A A x y) (And.left u₁)

                let v₇ := Iff.mp (cartesian_product_pair_prop A A y z) (And.left v₁)
                Iff.mpr (spec_is_spec P B (x, z)) (
                  And.intro (Iff.mpr (cartesian_product_pair_prop A A x z) (
                    And.intro (And.left v₆) (And.right v₇)
                  )) (v₅)
                )
          )
        )
      )

noncomputable def equinum_rel (A : Set) := {R ∈ (A × A) | ((π₁ R) ~ (π₂ R))}
syntax "Equin" term : term
macro_rules
| `(Equin $A) => `(equinum_rel $A)

noncomputable def oiso_rel (A : Set) := {R ∈ (A × A) | (π₁ R) ≃O (π₂ R)}
syntax "Oiso" term : term
macro_rules
| `(Oiso $A) => `(oiso_rel $A)




theorem equinum_equivrel : ∀ A, ((Equin A) EquivRel A) :=
  fun (A) =>
    let φ := fun (x) => fun (y) => x ~ y
    bin_equivrel φ A (
      And.intro (fun (x _) => equinum_refl x) (And.intro (equinum_symm) (fun(x y z hxyz) => equinum_trans x y z (And.left hxyz) (And.right hxyz)))
    )


theorem oiso_equivrel : ∀ A, ((Oiso A) EquivRel A) :=
  fun (A) =>
    let φ := fun (x) => fun (y) => x ≃O y
    bin_equivrel φ A (
      And.intro (fun (x _) => iso_refl x) (And.intro (iso_symm) (fun(x y z hxyz) => iso_trans x y z (And.left hxyz) (And.right hxyz)))
    )

theorem equivrel_inv : ∀ R A, (R EquivRel A) → (R = (R⁻¹)) :=
  fun (R A hRA) =>
    Iff.mp (symmetric_crit_eq A R (And.left hRA)) (
      And.left (And.right (And.right hRA))
    )

noncomputable def cart_equiv (A B R S : Set) :=
{pr ∈ ((A × B) × (A × B)) | ((π₁ (π₁ pr)) . R . (π₁ (π₂ pr))) ∧ ((π₂ (π₁ pr)) . S . (π₂ (π₂ pr)))}
syntax term "Cart" term "On" term "And" term : term
macro_rules
| `($R Cart $S On $A And $B) => `(cart_equiv $A $B $R $S)

theorem eqrel_cart_prop :
∀ A B R S x y, ((x, y) ∈ (R Cart S On A And B)) ↔ (x ∈ (A × B) ∧ y ∈ (A × B) ∧ ((π₁ x) . R  . (π₁ y)) ∧ ((π₂ x) . S . (π₂ y))) :=
fun (A B R S x y) =>
  equivrel_is_equivrel (fun (x) => fun (y) => ((π₁ x) . R  . (π₁ y)) ∧ ((π₂ x) . S . (π₂ y))) (A × B) x y

theorem equivrel_cart : ∀ A B R S, (R EquivRel A) → (S EquivRel B) → ((R Cart S On A And B) EquivRel (A × B)) :=
  fun (A B R S hRA hSB) =>
    bin_equivrel (fun (x) => fun (y) => ((π₁ x) . R  . (π₁ y)) ∧ ((π₂ x) . S . (π₂ y))) (A × B) (
      And.intro (
        fun (T hT) =>
          And.intro (And.left (And.right (hRA)) (π₁ T) (fst_coor_set A B T hT)) (
            And.left (And.right (hSB)) (π₂ T) (snd_coor_set A B T hT)
          )
      ) (And.intro (
        fun (x y hxy) =>
          let u₁ := And.left (And.right (And.right hRA)) (π₁ x) (π₁ y) (And.left hxy)
          let u₂ := And.left (And.right (And.right hSB)) (π₂ x) (π₂ y) (And.right hxy)
          And.intro (u₁) (u₂)
      ) (
        fun (x y z hxyz) =>
          let u₁ := And.right (And.right (And.right hRA)) (π₁ x) (π₁ y) (π₁ z) (And.intro (And.left (And.left hxyz)) (And.left (And.right hxyz)))
          let u₂ := And.right (And.right (And.right hSB)) (π₂ x) (π₂ y) (π₂ z) (And.intro (And.right (And.left hxyz)) (And.right (And.right hxyz)))
          And.intro (u₁) (u₂)
      ))
    )

theorem equivrel_int: ∀ X A, (X ≠ ∅) → (∀ R ∈ X; (R EquivRel A)) → ((⋂ X) EquivRel A) :=
  fun (X A hX hRX) =>
    let u₁ := (all_ss_then_union_ss X (A × A) (
      fun (R hR) =>
        And.left (hRX R hR)
    ))
    let u₂ := intersection_sub_union X
    let u₃ := subset_trans (⋂ X) (⋃ X) (A × A) u₂ u₁
    And.intro (u₃) (
      And.intro (
        fun (x hx) =>
          Iff.mpr (intersection_non_empty X hX (x, x)) (
            fun (R hR) =>
              And.left (And.right (hRX R hR)) x hx
          )
      ) (And.intro (
        fun (x y hxy) =>
          let u₅ := Iff.mp (intersection_non_empty X hX (x, y)) hxy
          Iff.mpr (intersection_non_empty X hX (y, x)) (
            fun (R hR) =>
              And.left (And.right (And.right (hRX R hR))) x y (u₅ R hR)
          )
      ) (
        fun (x y z hxyz) =>
          let u₅ := Iff.mp (intersection_non_empty X hX (x, y)) (And.left hxyz)
          let u₆ := Iff.mp (intersection_non_empty X hX (y, z)) (And.right hxyz)
          Iff.mpr (intersection_non_empty X hX (x, z)) (
            fun (R hR) =>
              And.right (And.right (And.right (hRX R hR))) x y z (
                And.intro (u₅ R hR) (u₆ R hR)
              )
          )
      ))
    )



theorem equivrel_int2 : ∀ R S, (R EquivRel A) → (S EquivRel A) → ((R ∩ S) EquivRel A) :=
  fun (R S hRA hSA) =>
    let u₀ := Iff.mpr (set_non_empty_iff_non_empty {R, S}) (
      Exists.intro R (left_unordered_pair R S)
    )
    let u₁ := intersect_2sets_is_intersect R S
    let u₂ := fun (x) => fun (hx : x ∈ {R, S}) => Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair R S x) hx) (
      fun(hR) =>
        eq_subst (fun (t) => (t EquivRel A)) (R) (x) (Eq.symm hR) (hRA)
       ) (fun (hS) => eq_subst (fun (t) => (t EquivRel A)) (S) (x) (Eq.symm hS) (hSA))
    eq_subst (fun (t) => (t EquivRel A)) (⋂ {R, S}) (R ∩ S) (u₁) (
      equivrel_int {R, S} A (u₀) (u₂)
    )


theorem equivrel_intind : ∀ B I A, (I ≠ ∅) → (B IndxFun I) → (∀ i ∈ I; ((B _ i) EquivRel A)) → ((⋂[ i in I ] B at i) EquivRel A) :=
  fun (B I A hI hBI heq) =>
    let u₁ := Iff.mpr (set_non_empty_iff_non_empty (B.[I])) (
      Exists.elim (Iff.mp (set_non_empty_iff_non_empty I) hI) (
        fun (i) =>
          fun (hi) =>
            Exists.intro (B _ i) (
              Iff.mpr (image_prop B I (B _ i)) (
                Exists.intro i (
                  And.intro (hi) (
                    Exists.elim hBI (
                      fun (Y) =>
                        fun (hY) =>
                          Iff.mpr (function_equal_value_prop B I Y hY i (B _ i) hi) (
                            Eq.refl (B _ i)
                          )
                    )
                  )
                )
              )
            )
      )
    )
    equivrel_int (B.[I]) A (u₁) (fun (Bi hBi) =>
        let u₂ := Iff.mp (image_prop B I Bi) hBi
        Exists.elim u₂ (
          fun (i) =>
            fun (hi) =>

              Exists.elim hBI (
                fun (Y) =>
                  fun (hY) =>
                    let u₂ := Iff.mp (function_equal_value_prop B I Y hY i Bi (And.left hi)) (And.right hi)
                    eq_subst (fun (t) => t EquivRel A) (B _ i) (Bi) (Eq.symm u₂) (
                      heq i (And.left hi)
                    )
              )
        ))



noncomputable def kernel_func (f A : Set) := {R ∈ (A × A) | f⦅π₁ R⦆ = f⦅π₂ R⦆}
syntax "ker" term "On" term : term
macro_rules
| `(ker $f On $A) => `(kernel_func $f $A)





theorem kernel_crit : ∀ f A, ∀ x y ∈ A; ((x, y) ∈ (ker f On A)) ↔ (f⦅x⦆ = f⦅y⦆) :=
  fun (f A x hx y hy) =>
    let P := fun (t) => f⦅π₁ t⦆ = f⦅π₂ t⦆
    Iff.intro
    (
      fun (hxy) =>
        let u₁ := Iff.mp (spec_is_spec P (A × A) (x, y)) hxy
        let u₂ := coordinates_fst_coor x y
        let u₃ := coordinates_snd_coor x y
        eq_subst (fun (t) => f⦅x⦆ = f⦅t⦆) (π₂ (x, y)) y (u₃) (
          eq_subst (fun (t) => f⦅t⦆ = f⦅π₂ (x, y) ⦆ ) (π₁ (x, y)) (x) (u₂) (
            And.right u₁
          )
        )

    )
    (
      fun (hxy) =>
        let u₂ := coordinates_fst_coor x y
        let u₃ := coordinates_snd_coor x y
        let u₃ : P (x, y) := eq_subst (fun (t) => f⦅π₁ (x, y) ⦆ = f⦅t⦆) y (π₂ (x, y)) (Eq.symm (u₃)) (
          eq_subst (fun (t) => f⦅t⦆ = f⦅y⦆ ) (x) (π₁ (x, y)) (Eq.symm u₂) (
            hxy
          )
        )

        Iff.mpr (spec_is_spec P (A × A) (x, y)) (
          And.intro (Iff.mpr (cartesian_product_pair_prop A A x y) (And.intro (hx) (hy))) (u₃)
        )
    )


theorem kernel_equivrel : ∀ A f, ((ker f On A) EquivRel A) :=
  fun (A f) =>
    let φ := fun (x) => fun (y) => f⦅x⦆ = f⦅y⦆
    bin_equivrel φ A (
      And.intro (fun (x _) => Eq.refl (f⦅x⦆)) (
        And.intro (fun (_) => fun(_ hxy) => Eq.symm (hxy)) (
          fun (_) => fun(_) => fun(_ hxyz) => Eq.trans (And.left hxyz) (And.right hxyz)
        )
      )
    )

theorem kernel_inj_crit : ∀ A B f, (f Fun A To B) → ((f Inj A To B) ↔ ((ker f On A) = id_ A)) :=
  fun (A B f hf) =>
    let C := A × A
    let P := fun (R) => f⦅π₁ R⦆ = f⦅π₂ R⦆
    Iff.intro
    (
      fun (hinj) =>


        extensionality (ker f On A) (id_ A) (
          fun (R) =>
            Iff.intro
            (
              fun (hR) =>
                let u₁ := Iff.mp (spec_is_spec P C R) hR
                let u₂ := Iff.mp (func_inj_prop A B f hf) hinj (π₁ R) (fst_coor_set A A R (And.left u₁)) (π₂ R) (snd_coor_set A A R (And.left u₁)) (And.right u₁)
                eq_subst (fun (t) => t ∈ (id_ A)) (π₁ R, π₂ R) R (Eq.symm (fst_snd_then_unique A A R (And.left u₁))) (
                  eq_subst (fun (t) => (π₁ R, t) ∈ (id_ A)) (π₁ R) (π₂ R) (u₂) (
                    prop_then_id A (π₁ R) (fst_coor_set A A R (And.left u₁))
                  )
                )
            )
            (
              fun (hR) =>
                let u₁ := id_is_binon A R hR
                let u₂ := id_prop A (π₁ R) (π₂ R) (eq_subst (fun (t) => t ∈ (id_ A)) (R) (π₁ R, π₂ R) (fst_snd_then_unique A A R u₁) hR)
                Iff.mpr (spec_is_spec P C R) (
                  And.intro (u₁) (
                    eq_subst (fun (t) => (f⦅t⦆ = f⦅π₂ R⦆)) (π₂ R) (π₁ R) (Eq.symm (And.left (And.left u₂))) (Eq.refl (f⦅π₂ R⦆))

                  )
                )
            )
        )
    )
    (
      fun (hkerid) =>
        Iff.mpr (func_inj_prop A B f hf) (
          fun (x hx y hy hxy) =>
            let u₁ := Iff.mpr (spec_is_spec P C (x, y)) (
              And.intro (Iff.mpr (cartesian_product_pair_prop A A x y) (And.intro hx hy)) (
                eq_subst (fun (t) => f⦅(π₁ (x, y))⦆ = f⦅t⦆) y (π₂ (x, y)) (Eq.symm (coordinates_snd_coor x y)) (
                eq_subst (fun (t) => f⦅t⦆ = f⦅y⦆) x (π₁ (x, y)) (Eq.symm (coordinates_fst_coor x y)) (
                  hxy
                )
              )
              )
            )
            let u₂ := eq_subst (fun (t) => (x, y) ∈ t) (ker f On A) (id_ A) (hkerid) (u₁)
            And.left (And.left (id_prop A x y u₂))
        )
    )


noncomputable def equiv_class (R A x) := {y ∈ A | (x . R . y)}
syntax "[" term "]" "Of" term "On" term : term
macro_rules
| `([ $x ] Of $R On $A) => `(equiv_class $R $A $x)


theorem equiv_class_sub : ∀ A R x, ([x] Of R On A) ⊆ A :=
  fun (A R x) =>
    let P := fun (y) => (x . R . y)
    specification_set_subset P A


theorem in_euiv_class₁ : ∀ A R x, ∀ y ∈ A; ((y ∈ ([x] Of R On A)) ↔ (x . R . y)) :=
  fun (A R x y hy) =>
    let P := fun (y) => (x . R . y)
    Iff.intro
    (
      fun (hyin) =>
        And.right (Iff.mp (spec_is_spec P A y) hyin)

    )
    (
      fun (hxy) =>
        Iff.mpr (spec_is_spec P A y) (And.intro hy hxy)
    )


theorem in_euiv_class₂ : ∀ A R x y, ((y ∈ ([x] Of R On A)) ↔ (y ∈ A ∧ (x . R . y))) :=
  fun (A R x y) =>
    let P := fun (y) => (x . R . y)
    spec_is_spec P A y


theorem equiv_class_x_in : ∀ A R, ∀ x ∈ A; (R EquivRel A) → (x ∈ ([x] Of R On A)) :=
  fun (A R x hx hRA) =>
    let P := fun (y) => (x . R . y)
    Iff.mpr (spec_is_spec P A x) (
      And.intro (hx) (equivrel_refl A R hRA x hx)
    )

theorem equiv_class_internemp₁ : ∀ A R, ∀ x y, (R EquivRel A) → ((([x] Of R On A) ∩ ([y] Of R On A) ≠ ∅) → (x . R . y)) :=
  fun (A R x y hRA hnemp) =>
    let C := ([x] Of R On A)
    let D := ([y] Of R On A)
    let u₁ := Iff.mp (set_non_empty_iff_non_empty (C ∩ D)) hnemp

    Exists.elim u₁ (
      fun (z) =>
        fun (hz) =>
          let u₂ := Iff.mp (intersect_2sets_prop C D z) hz
          let u₃ := Iff.mp (in_euiv_class₂ A R x z) (And.left u₂)
          let u₄ := Iff.mp (in_euiv_class₂ A R y z) (And.right u₂)
          let u₅ := equivrel_symm A R hRA y z (And.right u₄)
          equivrel_trans A R hRA x z y (And.intro (And.right u₃) (u₅))
    )


theorem equiv_class_internemp₂ : ∀ A R x y, (R EquivRel A) → ((x . R . y) → (([x] Of R On A) = ([y] Of R On A))) :=
  fun (A R x y hRA hxy) =>
    let C := ([x] Of R On A)
    let D := ([y] Of R On A)
    extensionality C D (
      fun (z) =>
        Iff.intro
        (
          fun (hz) =>
            let u₁ := Iff.mp (in_euiv_class₂ A R x z) hz
            let u₂ := equivrel_symm A R hRA x y hxy
            let u₃ := equivrel_trans A R hRA y x z (And.intro u₂ (And.right u₁))
            Iff.mpr (in_euiv_class₂ A R y z) (And.intro (And.left u₁) (u₃))

        )
        (
          fun (hz) =>
            let u₁ := Iff.mp (in_euiv_class₂ A R y z) hz
            let u₃ := equivrel_trans A R hRA x y z (And.intro (hxy) (And.right u₁))
            Iff.mpr (in_euiv_class₂ A R x z) (And.intro (And.left u₁) (u₃))
        )
    )

theorem equiv_class_internemp₃ : ∀ A R, ∀ x ∈ A; ∀ y, (R EquivRel A) → (([x] Of R On A) = ([y] Of R On A)) → (([x] Of R On A) ∩ ([y] Of R On A) ≠ ∅) :=
  fun (A R x hx y hRA hxy) =>
    let C := ([x] Of R On A)
    let D := ([y] Of R On A)
    Iff.mpr (set_non_empty_iff_non_empty (C ∩ D)) (
      Exists.intro x (
        Iff.mpr (intersect_2sets_prop C D x) (
          let u₁ := equiv_class_x_in A R x hx hRA
          And.intro (u₁) (
            eq_subst (fun (t) => x ∈ t) C D (hxy) (u₁)
          )
        )
      )
    )


theorem equiv_class_internemp : ∀ A R, ∀ x y ∈ A; (R EquivRel A) →
(((([x] Of R On A) ∩ ([y] Of R On A) ≠ ∅) ↔ (x . R . y)) ∧
((([x] Of R On A) ∩ ([y] Of R On A) ≠ ∅) ↔ (([x] Of R On A) = ([y] Of R On A))) ∧
((x . R . y) ↔ (([x] Of R On A) = ([y] Of R On A)))) :=
  fun (A R x hx y _ hRA) =>
    let u₁ := equiv_class_internemp₁ A R x y hRA
    let u₂ := equiv_class_internemp₂ A R x y hRA
    let u₃ := equiv_class_internemp₃ A R x hx y hRA
    let u₄ := fun (s : (x . R . y)) => u₃ ((u₂) s)
    let u₅ := fun (s : ([x] Of R On A) ∩ ([y] Of R On A) ≠ ∅) => u₂ (u₁ s)
    let u₆ := fun (s :([x] Of R On A) = ([y] Of R On A) ) => u₁ (u₃ s)

    And.intro (Iff.intro (u₁) (u₄)) (And.intro (Iff.intro (u₅) (u₃)) (Iff.intro (u₂) (u₆)))


theorem equiv_class_id : ∀ A, ∀ x ∈ A; ([x] Of (id_ A) On A) = {x} :=
fun (A x hx) =>
  let B := ([x] Of (id_ A) On A)
  let C := {x}
  extensionality B C (
    fun (y) =>
      Iff.intro
      (
        fun (hy) =>
          eq_subst (fun (t) => t ∈ C) x y (
            let u₁ := Iff.mp (in_euiv_class₂ A (id_ A) x y ) hy
            let u₂ := And.right u₁
            let u₃ := id_prop A x y u₂
            And.left (And.left u₃)

          ) (elem_in_singl x)
      )
      (
        fun (hy) =>
          eq_subst (fun (t) => t ∈ B) x y (
            Eq.symm (in_singl_elem x y (hy))
          ) (equiv_class_x_in A (id_ A) x hx (id_eqrel A))
      )
  )


theorem equiv_class_all_pair : ∀ A, ∀ x ∈ A; ([x] Of (A × A) On A) = A :=
  fun (A x hx) =>
    let B := ([x] Of (A × A) On A)
    let C := A
    extensionality B C (
      fun (y) =>
        Iff.intro
        (
          fun (hy) =>
            equiv_class_sub A (A × A) x y hy
        )
        (
          fun (hy) =>
            Iff.mpr (in_euiv_class₁ A (A × A) x y hy) (
              Iff.mpr (cartesian_product_pair_prop A A x y) (
                And.intro (hx) (hy)
              )
            )
        )
    )


theorem kernel_as_equivclass : ∀ A B f, (f Fun A To B) → ∀ x ∈ A; ([x] Of (ker f On A) On A) = f⁻¹.[{f⦅x⦆}] :=
  fun (A B f hf x hx) =>
    let M := ([x] Of (ker f On A) On A)
    let C := f⁻¹.[{f⦅x⦆}]
    extensionality M C (
      fun (y) =>
        let P := fun (a) => ∃ b ∈ {f⦅x⦆}; (a . f . b)
        let N := {a ∈ dom f | P a}
        let u₃₀ := And.left (And.left hf)
        let u₄ := rel_pre_image_eq {f⦅x⦆} f (And.left (prop_then_binary_relation A B f (u₃₀)))
        Iff.intro
        (
          fun (hy) =>

            let u₁ := Iff.mp (in_euiv_class₂ A (ker f On A) x y) hy
            let u₂ := And.right u₁
            let u₃ := Iff.mp (kernel_crit f A x hx y (And.left u₁)) u₂


            eq_subst (fun (t) => y ∈ t) N C (Eq.symm u₄) (
              Iff.mpr (spec_is_spec P (dom f) y) (
                And.intro (eq_subst (fun (t) => y ∈ t) (A) (dom f) (dom_function f A B hf) (And.left u₁)) (
                  Exists.intro (f⦅x⦆) (And.intro (elem_in_singl (f⦅x⦆)) (
                    Iff.mpr (function_equal_value_prop f A B hf y (f⦅x⦆) (And.left u₁)) (u₃)
                  ))
                )
              )
            )
        )
        (
          fun (hy) =>
            let u₁ := eq_subst (fun (t) => y ∈ t) (C) (N) (u₄) (hy)
            let u₂ := Iff.mp (spec_is_spec P (dom f) y) u₁
            let u₃ := eq_subst (fun (t) => y ∈ t) (dom f) (A) (Eq.symm (dom_function f A B hf)) (And.left u₂)
            Iff.mpr (in_euiv_class₂ A (ker f On A) x y) (
              And.intro (u₃) (
                Exists.elim (And.right u₂) (
                  fun (z) =>
                    fun (hz) =>
                      let u₅ := in_singl_elem (f⦅x⦆) z (And.left hz)
                      let u₆ := eq_subst (fun (t) => (y, t) ∈ f) (z) (f⦅x⦆) (u₅) (And.right hz)
                      let u₇ := Iff.mp (function_equal_value_prop f A B hf y (f⦅x⦆) u₃) u₆
                      Iff.mpr (kernel_crit f A x hx y u₃) (u₇)
                )
              )
            )
        )
    )


noncomputable def factor_set (R A) := {S ∈ 𝒫 (A) | ∃ x ∈ A; S = ([x] Of R On A)}
syntax term "./" term : term
macro_rules
| `($A ./ $R) => `(factor_set $R $A)


theorem factorset_prop : ∀ A R S, (S ∈ (A ./ R) ↔ (∃ x ∈ A; S = ([x] Of R On A))) :=
  fun (A R S) =>
      let P := fun (S) => (∃ x ∈ A; S = ([x] Of R On A))
      Iff.intro
      (
        fun (hS) =>
          And.right (Iff.mp (spec_is_spec P (𝒫 A) S) (hS))
      )
      (
        fun (hS) =>
          Exists.elim hS (
            fun (x) =>
              fun (hx) =>
                let Q := fun (y) => (x . R . y)
                let u₁ := specification_set_subset Q A
                let u₂ := eq_subst (fun (t) => t ⊆ A) ([x] Of R On A) (S) (Eq.symm (And.right (hx))) (u₁)
                Iff.mpr (spec_is_spec P (𝒫 A) S) (
                  And.intro (Iff.mpr (boolean_set_is_boolean A S) (
                    u₂
                  )) (hS)
                )
          )
      )

theorem factor_set_in : ∀ A R, ∀ x ∈ A; ([x] Of R On A) ∈ (A ./ R) :=
  fun (A R x hx) =>
    let S := ([x] Of R On A)
    Iff.mpr (factorset_prop A R S) (
      Exists.intro x (And.intro hx (Eq.refl S))
    )


theorem factor_set_union : ∀ A R, (R EquivRel A) → (⋃ (A ./ R)) = A :=
  fun (A R hRA) =>

    extensionality (⋃ (A ./ R)) A (
      fun (x) =>
        Iff.intro
        (
          fun (hx) =>
            let u₁ := Iff.mp (union_set_is_union (A ./ R) x) hx
            Exists.elim u₁ (
              fun (S) =>
                fun (hS) =>
                  let u₂ := Iff.mp (factorset_prop A R S) (And.left hS)
                  Exists.elim u₂ (
                    fun (y) =>
                      fun (hy) =>
                        let u₃ := eq_subst (fun (t) => x ∈ t) (S) ([y] Of R On A) (And.right hy) (And.right hS)
                        equiv_class_sub A R y x u₃
                  )
            )
        )
        (
          fun (hx) =>
            Iff.mpr (union_set_is_union (A ./ R) x) (
              Exists.intro ([x] Of R On A) (
                And.intro (factor_set_in A R x hx) (equiv_class_x_in A R x hx hRA)
              )
            )
        )
    )



theorem factor_id : ∀ A, (A ./ (id_ A)) = 𝒫₁ A :=
  fun (A) =>
    let B := (A ./ (id_ A))
    let C := 𝒫₁ A
    extensionality B C (
      fun (S) =>
        let u₁ : S ∈ B ↔ (∃ x ∈ A; S = ([x] Of (id_ A) On A)) := factorset_prop A (id_ A) S
        let u₂ := fun (x) => fun (hx : x ∈ A) => equiv_class_id A x hx
        Iff.intro
        (
          fun (hSB) =>
            let u₃ := Iff.mp u₁ hSB
            Exists.elim u₃ (
              fun (x) =>
                fun (hx) =>
                  let m := [x] Of (id_ A) On A
                  Iff.mpr (singlbool_set_prop A S) (
                    Exists.intro x (And.intro (And.left hx) (eq_subst (fun (t) => S = t) (m) ({x}) (u₂ x (And.left hx)) (And.right hx)))
                  )
            )
        )
        (
          fun (hsC) =>
            let u₀ := Iff.mp (singlbool_set_prop A S) hsC
            Exists.elim u₀ (
              fun (x) =>
                fun (hx) =>
                  let m := [x] Of (id_ A) On A
                  Iff.mpr (u₁) (
                    let hx₁ := And.left hx
                    Exists.intro x (And.intro (hx₁) (eq_subst (fun (t) => S = t) {x} m (Eq.symm (u₂ x hx₁)) (And.right hx)))
                  )
            )
        )
    )



theorem factor_allpairnemp : ∀ A, (A ≠ ∅) → (A ./ (A × A)) = {A} :=
  fun (A hA) =>
    let B := (A ./ (A × A))
    let C := {A}
    extensionality B C (
      fun (y) =>
        Iff.intro
        (
          fun (hy) =>
            let u₀ := Iff.mp (factorset_prop A (A × A) y) hy
            Exists.elim u₀ (
              fun (x) =>
                fun (hx) =>
                  eq_subst (fun (t) => t ∈ C) A y (
                    let u₁ := equiv_class_all_pair A x (And.left hx)
                    Eq.trans (Eq.symm u₁) (Eq.symm (And.right hx))
                  ) (elem_in_singl A)
            )
        )
        (
          fun (hy) =>
            let u₀ := in_singl_elem A y hy
            let u₁ := Iff.mp (set_non_empty_iff_non_empty A) hA
            Exists.elim u₁ (
              fun (s) =>
                fun (hs) =>
                  let u₂ := factor_set_in A (A × A) s hs
                  let u₃ := eq_subst (fun (t) => t ∈ B) ([s] Of (A × A) On A) A (equiv_class_all_pair A s hs) u₂
                  eq_subst (fun (t) => t ∈ B) A y (Eq.symm u₀) (u₃)
            )
        )
    )



theorem factor_allpairemp : ∀ A, (A = ∅) → (A ./ (A × A)) = A :=
  fun (A hA) =>
    let B := A ./ (A × A)
    eq_subst (fun (t) => B = t) ∅ A (Eq.symm hA) (
      Iff.mpr (set_empty_iff_empty (B)) (
        fun (S hS) =>
          let u₁ := Iff.mp (factorset_prop A (A × A) S) hS
          Exists.elim u₁ (
            fun (x) =>
              fun (hx) =>
                (Iff.mp (set_empty_iff_empty A) hA x) (
                  And.left hx
                )
          )
      )
    )



noncomputable def all_preimage_set (A f) := {S ∈ 𝒫 (A) | ∃ z ∈ rng f; S = f⁻¹.[{z}]}
syntax "PreImAll" term "On" term : term
macro_rules
| `(PreImAll $f On $A) => `(all_preimage_set $A $f)


theorem preimgall_prop : ∀ A B f S, (f Fun A To B) → ((S ∈ (PreImAll f On A)) ↔ (∃ z ∈ rng f; S = f⁻¹.[{z}])) :=

  fun (A B f S hf) =>
    let P := fun (t) => ∃ z ∈ rng f; t = f⁻¹.[{z}]
    Iff.intro
    (
      fun (hS) =>
        And.right (Iff.mp (spec_is_spec P (𝒫 A) S) (hS))
    )
    (
      fun (hS) =>
        Iff.mpr (spec_is_spec P (𝒫 A) S) (
          And.intro (Iff.mpr (boolean_set_is_boolean A S) (
            Exists.elim hS (
              fun (z) =>
                fun (hz) =>
                  let u₀ := And.left (prop_then_binary_relation A B f (And.left (And.left hf)))
                  let u₁ := rel_pre_image_eq {z} f u₀
                  let Q := fun (m) =>  ∃ b ∈ {z}; (m . f . b)
                  let R := {a ∈ dom f | ∃ b ∈ {z}; (a . f . b)}
                  let u₂ := eq_subst (fun (t) => t ⊆ A) R (f⁻¹.[{z}]) (Eq.symm u₁) (
                    eq_subst (fun (t) => R ⊆ t) (dom f) (A) (Eq.symm (dom_function f A B hf)) (specification_set_subset Q (dom f))
                  )
                  eq_subst (fun (t) => t ⊆ A) (f⁻¹.[{z}]) (S) (Eq.symm (And.right hz)) (
                    u₂
                  )
            )
          )) (hS)
        )
    )




theorem factor_kernel : ∀ A B f, (f Fun A To B) → (A ./ (ker f On A)) = PreImAll f On A :=
  fun (A B f hf) =>
    let C := (A ./ (ker f On A))
    let D := PreImAll f On A

    extensionality C D (
      fun (S) =>
        Iff.intro
        (
          fun (hSC) =>
            Iff.mpr (preimgall_prop A B f S hf) (
              let u₁ := Iff.mp (factorset_prop A (ker f On A) S) hSC
              Exists.elim u₁ (
                fun (x) =>
                  fun (hx) =>
                    Exists.intro (f⦅x⦆) (
                      And.intro (val_in_rng f A B hf x (And.left hx)) (
                        let u₁ := And.right hx
                        Eq.trans (u₁) (kernel_as_equivclass A B f hf x (And.left hx))

                      )
                    )
              )
            )
        )
        (
          fun (hSD) =>
            Iff.mpr (factorset_prop A (ker f On A) S) (
              let u₁ := Iff.mp (preimgall_prop A B f S hf) hSD
              Exists.elim u₁ (
                fun (z) =>
                  fun (hz) =>
                    let u₂ := Iff.mp (rng_prop f z) (And.left hz)
                    Exists.elim u₂ (
                      fun (x) =>
                        fun (hx) =>
                          let hx₀ := Iff.mpr (dom_prop f x) (Exists.intro z (hx))
                          let hx₁ := eq_subst (fun (t) => x ∈ t) (dom f) (A) (Eq.symm (dom_function f A B hf)) (hx₀)
                          let u₃ := Iff.mp (function_equal_value_prop f A B hf x z (hx₁)) hx
                          Exists.intro x (
                            And.intro (hx₁) (
                              let u₄ := And.right hz
                              let M := ([x] Of (ker f On A) On A)
                              Eq.trans (u₄) (Eq.symm (
                                eq_subst (fun (t) => M = f⁻¹.[{t}]) (f⦅x⦆) (z) (Eq.symm u₃) (kernel_as_equivclass A B f hf x (hx₁))
                              ))
                            )
                          )
                    )
              )
            )
        )
    )


noncomputable def natural_projection (A R : Set) := lam_fun A (A ./ R) (fun (x) => [x] Of R On A)
syntax term "ProjFun" term : term
macro_rules
| `($R ProjFun $A) => `(natural_projection $A $R)


theorem natproj_fun : ∀ A R, (R ProjFun A) Fun A To (A ./ R) :=
  fun (A R) =>
    let P := (fun (x) => [x] Of R On A)
    let u₁ := fun (x hx) => factor_set_in A R x hx
    And.left (lam_then_fun_prop P A (A ./ R) u₁)


theorem natproj_prop : ∀ A R, ∀ x ∈ A; (R ProjFun A)⦅x⦆ = [x] Of R On A :=
  fun (A R) =>
    let P := (fun (x) => [x] Of R On A)
    let u₁ := fun (x hx) => factor_set_in A R x hx
    And.right (lam_then_fun_prop P A (A ./ R) u₁)


theorem kerneleq_cond : ∀ A R f, (R EquivRel A) → ((R = ker f On A) ↔ (∀ x y ∈ A; (x . R . y) ↔ (f⦅x⦆ = f⦅y⦆))) :=
  fun (A R f hRA) =>
  Iff.intro
  (
    fun (hker) =>
      fun (x) =>
        fun (hx : x ∈ A) =>
            fun (y) =>
              fun (hy : y ∈ A) =>
                let s₁ := kernel_crit f A x hx y hy
                let s₂ := eq_subst (fun (t) => ((x, y) ∈ R) ↔ (x, y) ∈ t) R (ker f On A) hker (
                  Iff.intro (fun (m) => m) (fun (m) => m))
                iff_transitivity ((x, y) ∈ R) ((x, y) ∈ (ker f On A)) (f⦅x⦆ = f⦅y⦆) s₂ s₁
  )
  (
    fun (hprop) =>
      let u₁ := And.left hRA
      let u₂ := And.left (kernel_equivrel A f)
      relation_equality_btw R (ker f On A) A A (u₁) (u₂) (
        fun (x hx y hy) =>
          let u₃ := kernel_crit f A x hx y hy
          let u₄ := hprop x hx y hy
          Iff.intro (fun (h₁) => Iff.mpr (u₃) (Iff.mp u₄ h₁)) (fun (h₂) => Iff.mpr (u₄) (Iff.mp u₃ h₂))
      )
  )






theorem equivrel_kernel_natproj : ∀ A R, (R EquivRel A) → (R = ker (R ProjFun A) On A) :=
  fun (A R hRA) =>
    let P := (fun (x) => [x] Of R On A)
    let f := (R ProjFun A)
    let u₂ := natproj_prop A R
    let u₃ := And.left hRA
    let u₄ := And.left (kernel_equivrel A f)
    relation_equality_btw (R) (ker f On A) A A (u₃) (u₄) (
      fun (x hx y hy) =>
        let u₅ := kernel_crit f A x hx y hy
        iff_transitivity (x . R . y) (f⦅x⦆ = f⦅y⦆) (x . (ker f On A) . y) (

          eq_subst (fun (t) => ((x, y) ∈ R) ↔ (t = f⦅y⦆)) (P x) (f⦅x⦆) (Eq.symm (u₂ x hx)) (
            eq_subst (fun (t) => ((x, y) ∈ R) ↔ (P x = t)) (P y) (f⦅y⦆) (Eq.symm (u₂ y hy)) (
              And.right (And.right (equiv_class_internemp A R x hx y hy (hRA)))
            )
          )

        ) (Iff.intro (Iff.mpr u₅) (Iff.mp u₅))
    )




theorem equivrel_kernel : ∀ A R, (R EquivRel A) → (∃ f B, (f Fun A To B) ∧ (R = ker f On A)) :=
  fun (A R hRA) =>
    Exists.intro (R ProjFun A) (Exists.intro (A ./ R) (And.intro (natproj_fun A R) (equivrel_kernel_natproj A R hRA)))



theorem natproj_surj : ∀ A R, ((R ProjFun A) Surj A To (A ./ R)) :=
  fun (A R) =>
    let u₁ := natproj_fun A R
    Iff.mpr (func_surj_prop A (A ./ R) (R ProjFun A) u₁) (
      fun (S) =>
        fun (hS) =>
          let u₂ := Iff.mp (factorset_prop A R S) hS
          Exists.elim u₂ (
            fun (x) =>
              fun (hx) =>
                Exists.intro x (And.intro (And.left hx) (
                  let u₃ := natproj_prop A R x (And.left hx)

                  Eq.trans (And.right hx) (Eq.symm u₃)
                ))
          )
    )


noncomputable def induced_func (A B R f) := {s ∈ (A ./ R) × B | ∃ x ∈ A; s = ([x] Of R On A, f⦅x⦆)}
syntax term "IndFun" term "To" term "Of" term : term
macro_rules
| `($f IndFun $A To $B Of $R) => `(induced_func $A $B $R $f)


theorem induced_crit : ∀ A B R f, (f Fun A To B) →
(∀ s₁ s₂, ((s₁, s₂) ∈ (f IndFun A To B Of R)) ↔ (∃ x ∈ A; (s₁ = [x] Of R On A) ∧ (s₂ = f⦅x⦆))) :=
  fun (A B R f hf s₁ s₂) =>
    let P := fun (s) => ∃ x ∈ A; s = ([x] Of R On A, f⦅x⦆)
    Iff.intro
    (
      fun (hs) =>
        let u₁ := Iff.mp (spec_is_spec P ((A ./ R) × B) (s₁, s₂)) hs
        let u₂ := And.right u₁
        Exists.elim u₂ (
          fun (x) =>
            fun (hx) =>
              Exists.intro x (
                And.intro (And.left hx) (
                  Iff.mp (ordered_pair_set_prop (s₁) (s₂) ([x] Of R On A) (f⦅x⦆)) (
                    And.right hx
                  )
                )
              )
        )
    )
    (
      fun (hxs) =>
        Exists.elim hxs (
          fun (x) =>
            fun (hx) =>

            Iff.mpr (spec_is_spec P ((A ./ R) × B) (s₁, s₂)) (
              And.intro (Iff.mpr (cartesian_product_pair_prop (A ./ R) B s₁ s₂) (
                And.intro (
                  eq_subst (fun (t) => t ∈ (A ./ R)) ([x] Of R On A) (s₁) (Eq.symm (And.left (And.right hx))) (
                    factor_set_in A R x (And.left hx)
                  )
                ) (
                  eq_subst (fun (t) => t ∈ B) (f⦅x⦆) (s₂) (Eq.symm (And.right (And.right hx))) (
                    val_in_B f A B hf x (And.left hx)
                  )
                )
              )) (
                Exists.intro x (
                  And.intro (And.left hx) (
                    Iff.mpr (ordered_pair_set_prop (s₁) (s₂) ([x] Of R On A) (f⦅x⦆)) (
                      And.right hx
                    )
                  )
                )
              )
            )
        )
    )



theorem kernat_ind : ∀ A B R f, (R EquivRel A) → (f Fun A To B) → (R = (ker f On A)) →
((f IndFun A To B Of R) Fun (A ./ R) To B) ∧ f = (f IndFun A To B Of R) ∘ (R ProjFun A) :=
  fun (A B R f hRA hf hker) =>

    let h₁ := natproj_fun A R

    let g := f IndFun A To B Of R

    let C := (A ./ R) × B
    let P := fun (s) => ∃ x ∈ A; s = ([x] Of R On A, f⦅x⦆)

    let u₀ := Iff.mp (kerneleq_cond A R f hRA) hker

    let u₁ : g BinRelBtw (A ./ R) AND B := specification_set_subset P C

    let u₂ : g PartFun (A ./ R) To B := And.intro (u₁) (
      fun (s₁ s₂ s₃ hss₁ hss₂) =>
        let v₀ := Iff.mp (induced_crit A B R f hf s₁ s₂) hss₁
        let v₁ := Iff.mp (induced_crit A B R f hf s₁ s₃) hss₂
        Exists.elim v₀ (
          fun (x) =>
            fun (hx) =>
              Exists.elim v₁ (
                fun (y) =>
                  fun (hy) =>
                    let v₄ := Eq.trans (Eq.symm (And.left (And.right hx))) (And.left (And.right hy))
                    let v₅ := Iff.mpr (And.right (And.right (equiv_class_internemp A R x (And.left hx) y (And.left hy) hRA))) v₄
                    let v₆ := Iff.mp (u₀ x (And.left hx) y (And.left hy)) v₅
                    Eq.trans (And.right (And.right hx)) (Eq.trans (v₆) (Eq.symm (And.right (And.right hy))))
              )
        )
    )
    let u₃ : g Fun (A ./ R) To B := And.intro (u₂) (
      fun (S hS) =>
        let u₄ := Iff.mp (factorset_prop A R S) hS
        Exists.elim u₄ (
          fun (x) =>
            fun (hx) =>
              Exists.intro (f⦅x⦆) (
                Iff.mpr (spec_is_spec P ((A ./ R) × B) (S, (f⦅x⦆))) (
                  And.intro (
                    Iff.mpr (cartesian_product_pair_prop (A ./ R) B S (f⦅x⦆) ) (
                      And.intro (hS) (val_in_B f A B hf x (And.left hx))
                    )
                  ) (
                    Exists.intro x (
                      And.intro (And.left hx) (
                        Iff.mpr (ordered_pair_set_prop S (f⦅x⦆) ([x] Of R On A) (f⦅x⦆)) (
                          And.intro (And.right hx) (Eq.refl (f⦅x⦆))
                        )
                      )
                    )
                  )
                )
              )
        )
    )
    (And.intro (u₃) (

      let P := fun (s) => ∃ x ∈ A; s = ([x] Of R On A, f⦅x⦆)

      let u₄ := composition_is_relbtw (f IndFun A To B Of R) (R ProjFun A) A (A ./ R) B (
        specification_set_subset P ((A ./ R) × B)
      ) (
        And.left (And.left (natproj_fun A R))
      )
      relation_equality_btw f ((f IndFun A To B Of R) ∘ (R ProjFun A)) A B (And.left (And.left hf)) (u₄) (
        fun (x hx y _) =>
          Iff.intro
          (
            fun (hfxy) =>
              let fprop := Iff.mp (function_equal_value_prop f A B hf x y hx) hfxy
              Iff.mpr (composition_pair_prop (f IndFun A To B Of R) (R ProjFun A) x y) (
                let z := [x] Of R On A
                Exists.intro (z) (
                  And.intro (Iff.mpr (function_equal_value_prop (R ProjFun A) A (A ./ R) (h₁) x z hx) (
                    Eq.symm (natproj_prop A R x hx)
                  )) (
                    eq_subst (fun (t) => (z, t) ∈ (f IndFun A To B Of R)) (f⦅x⦆) (y) (Eq.symm fprop) (
                      Iff.mpr (induced_crit A B R f hf z (f⦅x⦆)) (
                        Exists.intro x (
                          And.intro (hx) (
                            And.intro (Eq.refl z) (Eq.refl (f⦅x⦆))
                          )
                        )
                      )
                    )
                  )
                )
              )

          )
          (
            fun (hcoxy) =>
              Iff.mpr (function_equal_value_prop f A B hf x y hx) (
                let h₀ := Iff.mp (composition_pair_prop (f IndFun A To B Of R) (R ProjFun A) x y) hcoxy
                Exists.elim h₀ (
                  fun (z) =>
                    fun (hz) =>
                      let h₂ := Iff.mp (function_equal_value_prop (R ProjFun A) A (A ./ R) h₁ x z hx) (And.left hz)
                      let h₃ := natproj_prop A R x hx
                      let h₄ := Eq.trans h₂ h₃
                      let h₅ := Iff.mp (induced_crit A B R f hf z y) (And.right hz)
                      Exists.elim h₅ (
                        fun (s) =>
                          fun (hs) =>
                            let h₆ := And.left (And.right hs)
                            let h₇ := And.right (And.right hs)
                            let h₈ := Eq.trans (Eq.symm h₆) (h₄)
                            let h₉ := Iff.mpr (And.right (And.right (equiv_class_internemp A R x hx s (And.left hs) hRA))) (
                              Eq.symm h₈)
                            let h₁₀ := Iff.mp (u₀ x hx s (And.left hs)) h₉

                            eq_subst (fun (t) => y = t) (f⦅s⦆) (f⦅x⦆) (Eq.symm (h₁₀)) (h₇)
                      )
                )
              )
          )
      )

    ))


theorem kernat_ind₂ : ∀ A B R f, (R EquivRel A) → (f Fun A To B) → (∀ x y ∈ A; (x . R . y) → (f⦅x⦆ = f⦅y⦆)) →
((f IndFun A To B Of R) Fun (A ./ R) To B) ∧ f = (f IndFun A To B Of R) ∘ (R ProjFun A) :=
  fun (A B R f hRA hf hker) =>

    let h₁ := natproj_fun A R

    let g := f IndFun A To B Of R

    let C := (A ./ R) × B
    let P := fun (s) => ∃ x ∈ A; s = ([x] Of R On A, f⦅x⦆)

    let u₀ := hker

    let u₁ : g BinRelBtw (A ./ R) AND B := specification_set_subset P C

    let u₂ : g PartFun (A ./ R) To B := And.intro (u₁) (
      fun (s₁ s₂ s₃ hss₁ hss₂) =>
        let v₀ := Iff.mp (induced_crit A B R f hf s₁ s₂) hss₁
        let v₁ := Iff.mp (induced_crit A B R f hf s₁ s₃) hss₂
        Exists.elim v₀ (
          fun (x) =>
            fun (hx) =>
              Exists.elim v₁ (
                fun (y) =>
                  fun (hy) =>
                    let v₄ := Eq.trans (Eq.symm (And.left (And.right hx))) (And.left (And.right hy))
                    let v₅ := Iff.mpr (And.right (And.right (equiv_class_internemp A R x (And.left hx) y (And.left hy) hRA))) v₄
                    let v₆ := u₀ x (And.left hx) y (And.left hy) v₅
                    Eq.trans (And.right (And.right hx)) (Eq.trans (v₆) (Eq.symm (And.right (And.right hy))))
              )
        )
    )
    let u₃ : g Fun (A ./ R) To B := And.intro (u₂) (
      fun (S hS) =>
        let u₄ := Iff.mp (factorset_prop A R S) hS
        Exists.elim u₄ (
          fun (x) =>
            fun (hx) =>
              Exists.intro (f⦅x⦆) (
                Iff.mpr (spec_is_spec P ((A ./ R) × B) (S, (f⦅x⦆))) (
                  And.intro (
                    Iff.mpr (cartesian_product_pair_prop (A ./ R) B S (f⦅x⦆) ) (
                      And.intro (hS) (val_in_B f A B hf x (And.left hx))
                    )
                  ) (
                    Exists.intro x (
                      And.intro (And.left hx) (
                        Iff.mpr (ordered_pair_set_prop S (f⦅x⦆) ([x] Of R On A) (f⦅x⦆)) (
                          And.intro (And.right hx) (Eq.refl (f⦅x⦆))
                        )
                      )
                    )
                  )
                )
              )
        )
    )
    (And.intro (u₃) (

      let P := fun (s) => ∃ x ∈ A; s = ([x] Of R On A, f⦅x⦆)

      let u₄ := composition_is_relbtw (f IndFun A To B Of R) (R ProjFun A) A (A ./ R) B (
        specification_set_subset P ((A ./ R) × B)
      ) (
        And.left (And.left (natproj_fun A R))
      )
      relation_equality_btw f ((f IndFun A To B Of R) ∘ (R ProjFun A)) A B (And.left (And.left hf)) (u₄) (
        fun (x hx y _) =>
          Iff.intro
          (
            fun (hfxy) =>
              let fprop := Iff.mp (function_equal_value_prop f A B hf x y hx) hfxy
              Iff.mpr (composition_pair_prop (f IndFun A To B Of R) (R ProjFun A) x y) (
                let z := [x] Of R On A
                Exists.intro (z) (
                  And.intro (Iff.mpr (function_equal_value_prop (R ProjFun A) A (A ./ R) (h₁) x z hx) (
                    Eq.symm (natproj_prop A R x hx)
                  )) (
                    eq_subst (fun (t) => (z, t) ∈ (f IndFun A To B Of R)) (f⦅x⦆) (y) (Eq.symm fprop) (
                      Iff.mpr (induced_crit A B R f hf z (f⦅x⦆)) (
                        Exists.intro x (
                          And.intro (hx) (
                            And.intro (Eq.refl z) (Eq.refl (f⦅x⦆))
                          )
                        )
                      )
                    )
                  )
                )
              )

          )
          (
            fun (hcoxy) =>
              Iff.mpr (function_equal_value_prop f A B hf x y hx) (
                let h₀ := Iff.mp (composition_pair_prop (f IndFun A To B Of R) (R ProjFun A) x y) hcoxy
                Exists.elim h₀ (
                  fun (z) =>
                    fun (hz) =>
                      let h₂ := Iff.mp (function_equal_value_prop (R ProjFun A) A (A ./ R) h₁ x z hx) (And.left hz)
                      let h₃ := natproj_prop A R x hx
                      let h₄ := Eq.trans h₂ h₃
                      let h₅ := Iff.mp (induced_crit A B R f hf z y) (And.right hz)
                      Exists.elim h₅ (
                        fun (s) =>
                          fun (hs) =>
                            let h₆ := And.left (And.right hs)
                            let h₇ := And.right (And.right hs)
                            let h₈ := Eq.trans (Eq.symm h₆) (h₄)
                            let h₉ := Iff.mpr (And.right (And.right (equiv_class_internemp A R x hx s (And.left hs) hRA))) (
                              Eq.symm h₈)
                            let h₁₀ := u₀ x hx s (And.left hs) h₉

                            eq_subst (fun (t) => y = t) (f⦅s⦆) (f⦅x⦆) (Eq.symm (h₁₀)) (h₇)
                      )
                )
              )
          )
      )

    ))


theorem kernat_anyind_val : ∀ A B R g f, (g Fun (A ./ R) To B) ∧ (f = g ∘ (R ProjFun A)) → (∀ x ∈ A; g⦅[x] Of R On A⦆ = f⦅x⦆) :=
  fun (A B R g f hg x hx) =>
    let u₁ := hg
    let u₂ := eq_congr_func_arg (fun (t : Set) => t⦅x⦆) f ((g) ∘ (R ProjFun A)) (And.right u₁)
    let u₂₀ := natproj_fun A R
    let u₃ := And.right (function_composition (R ProjFun A) (g) A (A ./ R) B (u₂₀) (And.left u₁)) x (
      eq_subst (fun (t) => x ∈ t) (A) (dom (R ProjFun A)) (dom_function (R ProjFun A) A (A ./ R) (u₂₀)) (hx)
    )
    let u₄ := Eq.symm (Eq.trans u₂ u₃)
    eq_subst (fun (t) => (g)⦅t⦆ = f⦅x⦆) ((R ProjFun A)⦅x⦆) ([x] Of R On A) (
      natproj_prop A R x hx
    ) (u₄)



theorem kernat_indval : ∀ A B R f, (R EquivRel A) → (f Fun A To B) → (R = (ker f On A)) → ∀ x ∈ A; (f IndFun A To B Of R)⦅[x] Of R On A⦆ = f⦅x⦆ :=
  fun (A B R f hRA hf hker x hx) =>
    let u₁ := kernat_ind A B R f hRA hf hker
    let u₂ := eq_congr_func_arg (fun (t : Set) => t⦅x⦆) f ((f IndFun A To B Of R) ∘ (R ProjFun A)) ( And.right u₁)
    let u₂₀ := natproj_fun A R
    let u₃ := And.right (function_composition (R ProjFun A) (f IndFun A To B Of R) A (A ./ R) B (u₂₀) (And.left u₁)) x (
      eq_subst (fun (t) => x ∈ t) (A) (dom (R ProjFun A)) (dom_function (R ProjFun A) A (A ./ R) (u₂₀)) (hx)
    )
    let u₄ := Eq.symm (Eq.trans u₂ u₃)
    eq_subst (fun (t) => (f IndFun A To B Of R)⦅t⦆ = f⦅x⦆) ((R ProjFun A)⦅x⦆) ([x] Of R On A) (
      natproj_prop A R x hx
    ) (u₄)




theorem kernat_indval₂ : ∀ A B R f, (R EquivRel A) → (f Fun A To B)
 → (∀ x y ∈ A; (x . R . y) → (f⦅x⦆ = f⦅y⦆)) → ∀ x ∈ A; (f IndFun A To B Of R)⦅[x] Of R On A⦆ = f⦅x⦆ :=
  fun (A B R f hRA hf hker x hx) =>
    let u₁ := kernat_ind₂ A B R f hRA hf hker
    let u₂ := eq_congr_func_arg (fun (t : Set) => t⦅x⦆) f ((f IndFun A To B Of R) ∘ (R ProjFun A)) ( And.right u₁)
    let u₂₀ := natproj_fun A R
    let u₃ := And.right (function_composition (R ProjFun A) (f IndFun A To B Of R) A (A ./ R) B (u₂₀) (And.left u₁)) x (
      eq_subst (fun (t) => x ∈ t) (A) (dom (R ProjFun A)) (dom_function (R ProjFun A) A (A ./ R) (u₂₀)) (hx)
    )
    let u₄ := Eq.symm (Eq.trans u₂ u₃)
    eq_subst (fun (t) => (f IndFun A To B Of R)⦅t⦆ = f⦅x⦆) ((R ProjFun A)⦅x⦆) ([x] Of R On A) (
      natproj_prop A R x hx
    ) (u₄)






theorem kernatind_uni : ∀ A B R f, (R EquivRel A) → (f Fun A To B) → (R = (ker f On A)) → (∃! g, (g Fun (A ./ R) To B) ∧ (f = g ∘ (R ProjFun A))) :=
  fun (A B R f hRA hf hker) =>
    let P := fun (g) => (g Fun (A ./ R) To B) ∧ (f = g ∘ (R ProjFun A))
    Iff.mpr (exists_unique_expansion_curry P) (
      And.intro (Exists.intro (f IndFun A To B Of R) (kernat_ind A B R f hRA hf hker)) (
        fun (f₁ f₂ hf₁ hf₂) =>
          Iff.mpr (equal_functions_abc_A f₁ f₂ (A ./ R) B B (And.left hf₁) (And.left hf₂)) (
            fun (S) =>
              fun (hS) =>
                let facprop := Iff.mp (factorset_prop A R S) hS
                Exists.elim facprop (
                  fun (x) =>
                    fun (hx) =>
                      eq_subst (fun (t) => f₁⦅t⦆ = f₂⦅t⦆) ([x] Of R On A) (S) (Eq.symm (And.right hx)) (
                        let hf₁₁ := kernat_anyind_val A B R f₁ f (hf₁) x (And.left hx)
                        let hf₂₁ := kernat_anyind_val A B R f₂ f (hf₂) x (And.left hx)
                        Eq.trans (hf₁₁) (Eq.symm (hf₂₁))
                      )
                )
          )

      )
    )


theorem factor_kernel_equin : ∀ A B f, (f Fun A To B) → (A ./ (ker f On A)) ~ (rng f) :=
  fun (A B f hf) =>
    let hf₁ := function_rng_def f A B hf
    let g := f IndFun A To (rng f) Of (ker f On A)
    let M := (A ./ (ker f On A))
    let N := rng f
    let hg := kernat_ind A (rng f) (ker f On A) f (kernel_equivrel A f) hf₁ (Eq.refl (ker f On A))
    Exists.intro g (And.intro (And.left hg) (
      And.intro
      (And.right (Iff.mpr (func_inj_prop M N g (And.left hg)) (
        fun (s₁ hs₁ s₂ hs₂) =>
          let u₁ := Iff.mp (factorset_prop A (ker f On A) s₁) hs₁
          let u₂ := Iff.mp (factorset_prop A (ker f On A) s₂) hs₂

          Exists.elim u₁ (
            fun (x) =>
              fun (hx) =>
                Exists.elim u₂ (
                  fun (y) =>
                    fun (hy) =>
                      fun (hgs₁s₂) =>
                        let u₃ := kernat_indval A (rng f) (ker f On A) f (kernel_equivrel A f) hf₁ (Eq.refl (ker f On A)) x (And.left hx)
                        let u₄ := eq_subst (fun (t) => g⦅t⦆ = f⦅x⦆) ([x] Of (ker f On A) On (A)) s₁ (Eq.symm (And.right hx)) (u₃)
                        let u₅ := kernat_indval A (rng f) (ker f On A) f (kernel_equivrel A f) hf₁ (Eq.refl (ker f On A)) y (And.left hy)
                        let u₆ := eq_subst (fun (t) => g⦅t⦆ = f⦅y⦆) ([y] Of (ker f On A) On (A)) s₂ (Eq.symm (And.right hy)) (u₅)
                        let u₇ := Eq.trans (Eq.symm u₄) (Eq.trans hgs₁s₂ (u₆))
                        let u₈ := Iff.mpr (Iff.mp (kerneleq_cond A (ker f On A) f (kernel_equivrel A f)) (Eq.refl (ker f On A)) x (And.left hx) y (And.left hy)) u₇
                        let u₉ := Iff.mp (And.right (And.right (equiv_class_internemp A (ker f On A) x (And.left hx) y (And.left hy) (kernel_equivrel A f)))) u₈
                        Eq.trans (And.right hx) (Eq.trans (u₉) (Eq.symm (And.right hy)))
                )
          )
      )))
      (

        And.right (Iff.mpr (func_surj_prop (A ./ (ker f On A)) (rng f) g (And.left hg)) (

          fun (y) =>
            fun (hy) =>
              let u₁ := Iff.mp (rng_prop f y) hy
              Exists.elim u₁ (
                fun (x) =>
                  fun (hx) =>
                    let u₂₀ := dom_function f A (rng f) hf₁
                    let u₂₁ := Iff.mpr (dom_prop f x) (Exists.intro y hx)
                    let u₂₂ := eq_subst (fun (t) => x ∈ t) (dom f) (A) (Eq.symm u₂₀) (u₂₁)
                    let u₂ := Iff.mp (function_equal_value_prop f A (rng f) hf₁ x y u₂₂) hx

                    Exists.intro ([x] Of (ker f On A) On A) (
                      let u₃ : g⦅[x] Of (ker f On A) On A⦆ = f⦅x⦆ := kernat_indval A (rng f) (ker f On A) f (kernel_equivrel A f) hf₁ (Eq.refl (ker f On A)) x u₂₂
                      And.intro (factor_set_in A (ker f On A) x u₂₂) (Eq.trans u₂ (Eq.symm (u₃)))
                    )
              )
        ))
      )
    ))


def fac_rel_compat (A R S) := (∀ r₁ r₂ ∈ (A ./ R); (r₁ . (S) . r₂) ↔ (∃ x₁ ∈ r₁; ∃ x₂ ∈ r₂; (x₁ . (R) . x₂)))
syntax term "FacCompRelWith" term "On" term : term
macro_rules
| `($S FacCompRelWith $R On $A) => `(fac_rel_compat $A $R $S)

theorem facrelcompcond :
∀ A R S,
(R EquivRel A) →
((S FacCompRelWith R On A) ↔ (∀ x₁ x₂ ∈ A; (([x₁] Of R On A) . S . ([x₂] Of R On A)) ↔ (x₁ . R . x₂))) :=
  fun (A R S hRA) =>
    Iff.intro
    (
      fun (hS x₁ hx₁ x₂ hx₂) =>
        Iff.intro
        (
          fun (heq) =>
            let Eq₁ := [x₁] Of R On A
            let Eq₂ := [x₂] Of R On A
            let u₁ := Iff.mp (hS Eq₁ (factor_set_in A R x₁ hx₁) Eq₂ (factor_set_in A R x₂ hx₂)) heq
            Exists.elim u₁ (
              fun (x₃) =>
                fun (hx₃) =>
                  Exists.elim (And.right hx₃) (
                    fun (x₄) =>
                      fun (hx₄) =>
                        let u₂ := And.right hx₄
                        let u₃ := And.left hx₃
                        let u₄ := And.left hx₄
                        let u₅ := Iff.mp (in_euiv_class₂ A R x₁ x₃) u₃
                        let u₆ := Iff.mp (in_euiv_class₂ A R x₂ x₄) u₄
                        let u₇ := equivrel_trans A R hRA x₁ x₃ x₄ (
                          And.intro (And.right u₅) (u₂)
                        )
                        equivrel_trans A R hRA x₁ x₄ x₂ (
                          And.intro (u₇) (equivrel_symm A R hRA x₂ x₄ (And.right u₆))
                        )
                  )
            )
        )
        (
          fun (hx₁₂) =>
            let Eq₁ := [x₁] Of R On A
            let Eq₂ := [x₂] Of R On A
            Iff.mpr (hS Eq₁ (factor_set_in A R x₁ hx₁) Eq₂ (factor_set_in A R x₂ hx₂)) (
              Exists.intro x₁ (
                And.intro (equiv_class_x_in A R x₁ hx₁ hRA) (
                  Exists.intro x₂ (
                    And.intro (equiv_class_x_in A R x₂ hx₂ hRA) (hx₁₂)
                  )
                )
              )
            )
        )
    )
    (
      fun (hx₁x₂ r₁ hr₁ r₂ hr₂) =>
        let u₁ := Iff.mp (factorset_prop A R r₁) hr₁
        let u₂ := Iff.mp (factorset_prop A R r₂) hr₂
        Exists.elim u₁ (
          fun (x₁) =>
            fun (hx₁) =>
              Exists.elim (u₂) (
                fun (x₂) =>
                  fun (hx₂) =>
                    Iff.intro
                    (
                      fun (hr₁r₂) =>

                        Exists.intro x₁ (
                          And.intro (
                            eq_subst (fun (t) => x₁ ∈ t) ([x₁] Of R On A) r₁ (Eq.symm (And.right hx₁)) (
                              equiv_class_x_in A R x₁ (And.left hx₁) (hRA)
                            )
                          ) (
                            Exists.intro x₂ (
                              And.intro (
                                eq_subst (fun (t) => x₂ ∈ t) ([x₂] Of R On A) r₂ (Eq.symm (And.right hx₂)) (
                                  equiv_class_x_in A R x₂ (And.left hx₂) (hRA)
                                )
                              ) (
                                Iff.mp (hx₁x₂ x₁ (And.left hx₁) x₂ (And.left hx₂)) (
                                  eq_subst (fun (t) => (t, [x₂] Of R On A) ∈ S) r₁ ([x₁] Of R On A) (And.right hx₁) (
                                    eq_subst (fun (t) => (r₁, t) ∈ S) r₂ ([x₂] Of R On A) (And.right hx₂) (
                                      hr₁r₂
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                    )
                    (
                      fun (hexi) =>
                        Exists.elim hexi (
                          fun (x₁) =>
                            fun (hx₁) =>
                              Exists.elim (And.right hx₁) (
                                fun (x₂) =>
                                  fun (hx₂) =>
                                    let v₁ := And.right hx₂
                                    Exists.elim u₁ (
                                      fun (x₃) =>
                                        fun (hx₃) =>
                                          Exists.elim u₂ (
                                            fun (x₄) =>
                                              fun (hx₄) =>
                                                let v₃ := And.right hx₃
                                                let v₄ := And.right hx₄
                                                let v₅ := And.left (hx₁)
                                                let v₆ := And.left (hx₂)
                                                let v₇ := eq_subst (fun (t) => x₁ ∈ t) (r₁) ([x₃] Of R On A) (v₃) (v₅)
                                                let v₈ := eq_subst (fun (t) => x₂ ∈ t) (r₂) ([x₄] Of R On A) (v₄) (v₆)
                                                let v₉ := Iff.mp (in_euiv_class₂ A R x₃ x₁) v₇
                                                let v₁₀ := Iff.mp (in_euiv_class₂ A R x₄ x₂) v₈
                                                let v₁₁ := equivrel_trans A R hRA x₃ x₁ x₄ (
                                                  And.intro (And.right v₉) (
                                                    equivrel_trans A R hRA x₁ x₂ x₄ (
                                                      And.intro (v₁) (equivrel_symm A R hRA x₄ x₂ (And.right v₁₀))
                                                    )
                                                  )
                                                )
                                                eq_subst (fun (t) => (r₁, t) ∈ S) ([x₄] Of R On A) (r₂) (Eq.symm v₄) (
                                                  eq_subst (fun (t) => (t, [x₄] Of R On A) ∈ S) ([x₃] Of R On A) (r₁) (Eq.symm v₃) (
                                                    Iff.mpr (hx₁x₂ x₃ (And.left hx₃) x₄ (And.left hx₄)) (
                                                      v₁₁
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



theorem facsub_cov : ∀ A R S, (R EquivRel A) → (S EquivRel A) → (R ⊆ S) → (A ./ R) ≿ (A ./ S) :=
  fun (A R S hRA hSA hRS) =>
    let P := (fun (x) => [x] Of S On A)
    let f := lam_fun A (A ./ S) P
    let g := f IndFun A To (A ./ S) Of R
    let fprop := lam_then_fun_prop P A (A ./ S) (
      fun (x hx) =>
        factor_set_in A S x hx
    )
    let Rprop := fun (x hx y hy hxy) =>
        let u₁ := hRS (x, y) hxy
        let u₂ := Iff.mp (And.right (And.right (equiv_class_internemp A S x hx y hy hSA))) u₁
        Eq.trans (And.right fprop x hx) (Eq.trans (u₂) (Eq.symm (And.right fprop y hy)))

    let gprop := kernat_ind₂ A (A ./ S) R f hRA (And.left fprop) (
        Rprop
    )
    Exists.intro g (
      And.intro (And.left gprop) (
        fun (s hs) =>
          let u₃ := Iff.mp (factorset_prop A S s) hs
          Exists.elim u₃ (
            fun (x) =>
              fun (hx) =>
                let xclass := [x] Of R On A
                Exists.intro (xclass) (
                  Iff.mpr (function_equal_value_prop g (A ./ R) (A ./ S) (And.left gprop) xclass s (
                    factor_set_in A R x (And.left hx)
                  )) (Eq.trans (And.right hx) (Eq.symm (

                    let u₄ : (g)⦅xclass⦆ =f⦅x⦆ := kernat_indval₂ A (A ./ S) R f hRA (And.left fprop) Rprop x (And.left hx)
                    let u₅ : f⦅x⦆ = [x] Of S On A := And.right fprop x (And.left hx)
                    Eq.trans u₄ u₅
                  )))
                )
          )
      )
    )



theorem facsub_incl_ax : choice_ax → ∀ A R S, (R EquivRel A) → (S EquivRel A) → (R ⊆ S) → (A ./ S) ≾ (A ./ R) :=
  fun (ch A R S hRA hSA hRS) =>
    let u₁ := facsub_cov A R S hRA hSA hRS
    Iff.mpr (incl_cov_prop_AC ch (A ./ S) (A ./ R)) (
      Or.inl (u₁)
    )
