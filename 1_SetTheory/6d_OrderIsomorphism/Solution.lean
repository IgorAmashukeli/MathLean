import «Header»

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



theorem poiso_minum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_lowest 𝓐 X x) ↔ (is_lowest 𝓑 (f.[X]) (f⦅x⦆))) :=
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


theorem poiso_maxum : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_greatest 𝓐 X x) ↔ (is_greatest 𝓑 (f.[X]) (f⦅x⦆))) :=
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


theorem minexi_constr : ∀ 𝓐 X, (X ⊆ setPO(𝓐)) → ((𝓐 LowExi X) ↔ (∃ x ∈ setPO(𝓐); is_lowest 𝓐 X x)) :=
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


theorem maxexi_constr : ∀ 𝓐 X, (X ⊆ setPO(𝓐)) → ((𝓐 GrtExi X) ↔ (∃ x ∈ setPO(𝓐); is_greatest 𝓐 X x)) :=
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


theorem poiso_minexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 LowExi X) ↔ (𝓑 LowExi f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let hpoiso := And.right (And.right hf)
          let hbij := And.left hpoiso
          let hfunc := And.left hbij
          let hpfunc := And.left hfunc
          let φ₁ := fun (x) => is_lowest 𝓐 X x
          let φ₂ := fun (x) => is_lowest 𝓑 (f.[X]) (x)
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




theorem poiso_maxexi : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((𝓐 GrtExi X) ↔ (𝓑 GrtExi f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let hpoiso := And.right (And.right hf)
          let hbij := And.left hpoiso
          let hfunc := And.left hbij
          let hpfunc := And.left hfunc
          let φ₁ := fun (x) => is_greatest 𝓐 X x
          let φ₂ := fun (x) => is_greatest 𝓑 (f.[X]) (x)
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
          eq_subst (fun (t) => (is_lowest (𝓐) (𝓐 ▴ X) x) ↔ (is_lowest 𝓑 (t) (f⦅x⦆))) (f.[𝓐 ▴ X]) (𝓑 ▴ (f.[X])) (u₁) (u)


theorem poiso_inf : ∀ 𝓐 𝓑 f X x, (X ⊆ setPO(𝓐)) → (x ∈ setPO(𝓐)) → (f PO_ISO_PO 𝓐 To 𝓑) → ((is_infimum 𝓐 X x) ↔ (is_infimum 𝓑 (f.[X]) (f⦅x⦆))) :=
  fun (𝓐 𝓑 f X x) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hx : (x ∈ setPO(𝓐))) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let u₀ := specification_set_subset (fun (t) => is_lower_bound 𝓐 X t) (setPO(𝓐))
          let u := poiso_maxum 𝓐 𝓑 f (𝓐 ▾ X) x (u₀) hx hf
          let u₁ := poiso_lowset 𝓐 𝓑 f X hX hf
          eq_subst (fun (t) => (is_greatest (𝓐) (𝓐 ▾ X) x) ↔ (is_greatest 𝓑 (t) (f⦅x⦆))) (f.[𝓐 ▾ X]) (𝓑 ▾ (f.[X])) (u₁) (u)


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


theorem poiso_minumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 LowExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Low X⦆ = 𝓑 Low (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hXexi : (𝓐 LowExi X)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ := fun (𝓐) => fun (X) => fun(x) => is_lowest 𝓐 X x
          let ψ := fun (𝓐) => fun (X) => 𝓐 Low X
          let cond := fun (𝓐) => fun (X) => 𝓐 LowExi X
          let u := fun (𝓧) =>
                      fun (Y) =>
                        fun (hY : Y ⊆ setPO(𝓧)) =>
                          fun (h𝓧 : PartOrd 𝓧) =>
                            fun (hYexi : 𝓧 LowExi Y) =>
                              let v₁ := And.left (min_po_prop 𝓧 Y h𝓧 hYexi)
                              let v := hY (ψ 𝓧 Y) v₁
                              v
          let hfXexi := Iff.mp (poiso_minexi 𝓐 𝓑 f X hX hf) hXexi
          poiso_elconstr φ ψ cond 𝓐 𝓑 f X hX hXexi hfXexi hf (u) (min_po_crit) (poiso_minum 𝓐 𝓑 f)



theorem poiso_maxumel : ∀ 𝓐 𝓑 f X, (X ⊆ setPO(𝓐)) → (𝓐 GrtExi X) → (f PO_ISO_PO 𝓐 To 𝓑) → (f⦅𝓐 Grt X⦆ = 𝓑 Grt (f.[X])) :=
  fun (𝓐 𝓑 f X) =>
    fun (hX : (X ⊆ setPO(𝓐))) =>
      fun (hXexi : (𝓐 GrtExi X)) =>
        fun (hf : (f PO_ISO_PO 𝓐 To 𝓑)) =>
          let φ := fun (𝓐) => fun (X) => fun(x) => is_greatest 𝓐 X x
          let ψ := fun (𝓐) => fun (X) => 𝓐 Grt X
          let cond := fun (𝓐) => fun (X) => 𝓐 GrtExi X
          let u := fun (𝓧) =>
                      fun (Y) =>
                        fun (hY : Y ⊆ setPO(𝓧)) =>
                          fun (h𝓧 : PartOrd 𝓧) =>
                            fun (hYexi : 𝓧 GrtExi Y) =>
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


theorem poiso_semilatt : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((SemiLatt 𝓐) ↔ (SemiLatt 𝓑)) :=
  fun (𝓐 𝓑) =>
    fun (h𝓐𝓑 : 𝓐 P≃O 𝓑) =>
      let po𝓐 := And.left h𝓐𝓑
      let po𝓑 := And.left (And.right h𝓐𝓑)
      let iso := And.right (And.right h𝓐𝓑)

      Exists.elim iso (
        fun (f) =>
          fun (hf) =>
            let hfunc := And.left (And.left hf)
            let φ₃ := (∀ x y ∈ (setPO(𝓐)); (𝓐 InfmExi ({x, y})))
            let φ₄ := (∀ x y ∈ (setPO(𝓑)); (𝓑 InfmExi ({x, y})))
            let φ₅ := fun (x) => (∀ y ∈ (setPO(𝓐)); (𝓐 InfmExi ({x, y})))
            let φ₆ := fun (x) => (∀ y ∈ (setPO(𝓑)); (𝓑 InfmExi ({x, y})))
            let u : φ₃ ↔ φ₄ := poiso_allin_equiv φ₅ φ₆ 𝓐 𝓑 f hf (
              fun (x) =>
                fun (hx : x ∈ setPO(𝓐)) =>
                  let φ₇ := fun (y) => 𝓐 InfmExi ({x, y})
                  let φ₈ := fun (y) => 𝓑 InfmExi ({(f⦅x⦆), y})

                  poiso_allin_equiv φ₇ φ₈ 𝓐 𝓑 f hf (
                    fun (y) =>
                      fun (hy : y ∈ setPO(𝓐)) =>


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


                        let u₂ := poiso_infexi 𝓐 𝓑 f {x, y} (u₀) (And.intro (po𝓐) (And.intro po𝓑 hf))

                        eq_subst (fun (t) => (𝓐 InfmExi {x, y}) ↔ (𝓑 InfmExi t)) (f.[{x, y}]) ({(f⦅x⦆), (f⦅y⦆)}) (u₁) (u₂)

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


theorem poiso_wellfo : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((WellFoundOrd 𝓐) ↔ (WellFoundOrd 𝓑)) :=
  fun (𝓐 𝓑 hPO) =>
    let φ := fun (𝓐) => fun (X) => (X ≠ ∅) → 𝓐 LowExi X

    let u₀ := fun (𝓐 𝓑 f X) =>
                fun (hX : X ⊆ setPO(𝓐)) =>
                    fun (hf : f PO_ISO_PO 𝓐 To 𝓑) =>
                      let hiso := And.right (And.right hf)
                      let hbij := And.left hiso
                      let hfunc := And.left hbij
                      Iff.intro
                      (
                        fun (h𝓐 : (X ≠ ∅) → (𝓐 LowExi X)) =>
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
                        fun (h𝓑 : (f.[X] ≠ ∅) → (𝓑 LowExi (f.[X]))) =>
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
        And.intro (And.left (And.right hPO)) (
          Iff.mp (u₁) (And.right hWell𝓐)
        )
    )
    (
      fun (hWell𝓑) =>
        And.intro (And.left hPO) (
          Iff.mpr (u₁) (And.right hWell𝓑)
        )
    )




theorem poiso_welord : ∀ 𝓐 𝓑, (𝓐 P≃O 𝓑) → ((WellOrd 𝓐) ↔ (WellOrd 𝓑)) :=
  fun (𝓐 𝓑 hPO) =>
    let φ := fun (𝓐) => fun (X) => (X ≠ ∅) → 𝓐 LowExi X

    let u₀ := fun (𝓐 𝓑 f X) =>
                fun (hX : X ⊆ setPO(𝓐)) =>
                    fun (hf : f PO_ISO_PO 𝓐 To 𝓑) =>
                      let hiso := And.right (And.right hf)
                      let hbij := And.left hiso
                      let hfunc := And.left hbij
                      Iff.intro
                      (
                        fun (h𝓐 : (X ≠ ∅) → (𝓐 LowExi X)) =>
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
                        fun (h𝓑 : (f.[X] ≠ ∅) → (𝓑 LowExi (f.[X]))) =>
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



-- finish later
theorem poiso_inter : ∀ 𝓐 𝓑 𝓒 𝓓 f, (setPO(𝓐) ∩ setPO(𝓒) ≠ ∅) →
(setPO(𝓑) ∩ setPO(𝓓) ≠ ∅) → (f PO_ISO_PO 𝓐 To 𝓑) → (f PO_ISO_PO 𝓒 To 𝓓) → (f PO_ISO_PO (𝓐 InterPO 𝓒) To (𝓑 InterPO 𝓓)) := sorry




theorem poiso_cart : ∀ 𝓐 𝓑 𝓒 𝓓, (𝓐 P≃O 𝓑) → (𝓒 P≃O 𝓓) → ((𝓐 Cart2CordPO 𝓒) P≃O (𝓑 Cart2CordPO 𝓓)) :=
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
                      eq_subst (fun (t) => h Bij t To (setPO(𝓑 Cart2CordPO 𝓓))) (A × C) (setPO(𝓐 Cart2CordPO 𝓒)) (Eq.symm u₁) (
                        eq_subst (fun (t) => h Bij (A × C) To t) (B × D) (setPO(𝓑 Cart2CordPO 𝓓)) (Eq.symm u₂) (
                          And.intro (func_prop) (And.intro (injv_prop) (surjv_prop))
                        )
                      )
                    ) (


                      fun (x hx y hy) =>

                        let hx₁ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 Cart2CordPO 𝓒)) (A × C) (u₁) hx
                        let hx₁₁ := fst_coor_set A C x hx₁
                        let hx₁₂ := snd_coor_set A C x hx₁
                        let hy₁ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 Cart2CordPO 𝓒)) (A × C) (u₁) hy
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
                            let v₀₀ := eq_subst (fun (t) => (x, y) ∈ t) (≼(𝓐 Cart2CordPO 𝓒)) (leq_cart 𝓐 𝓒) (u₁₁) (hxy)
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

                            eq_subst (fun (t) => ((h⦅x⦆), (h⦅y⦆)) ∈ t) (leq_cart 𝓑 𝓓) (≼(𝓑 Cart2CordPO 𝓓)) (Eq.symm u₂₁) (v)
                        )
                        (
                          fun (hfxy) =>
                            let v₀₀ := eq_subst (fun (t) => ((h⦅x⦆), (h⦅y⦆)) ∈ t) (≼(𝓑 Cart2CordPO 𝓓)) (leq_cart 𝓑 𝓓) (u₂₁) (hfxy)
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

                            eq_subst (fun (t) => (x, y) ∈ t) (leq_cart 𝓐 𝓒) (≼(𝓐 Cart2CordPO 𝓒)) (Eq.symm u₁₁) (v₃)
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
