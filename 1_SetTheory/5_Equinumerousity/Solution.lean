import «Header»


def equinumerous (A B : Set) : Prop := ∃ f, f Bij A To B

syntax term "~" term : term
syntax term "≁" term : term

macro_rules
  | `($A:term ~ $B:term) => `(equinumerous $A $B)
  | `($A:term ≁ $B:term) => `(¬($A ~ $B))


theorem equinum_refl : ∀ A, A ~ A :=
  fun (A) =>
    Exists.intro (id_ A) (id_is_bij A)


theorem equinum_symm : ∀ A B, (A ~ B) → B ~ A :=
  fun (A B) => fun (h : A ~ B) =>
    Exists.elim h
    (
      fun (f) =>
        fun (hf : f Bij A To B) =>
          Exists.intro (f⁻¹) (bijection_inv_mp f A B hf)
    )


theorem equinum_trans : ∀ A B C, (A ~ B) → (B ~ C) → (A ~ C) :=
  fun (A B C) => fun (h₁ : A ~ B) => fun (h₂ : B ~ C) =>
    Exists.elim h₁
    (
      fun (f) =>
        fun (hf : f Bij A To B) =>
          Exists.elim h₂
          (
            fun (g) =>
              fun (hg : g Bij B To C) =>
                Exists.intro (g ∘ f) (bijection_composition f g A B C hf hg)
          )
    )


theorem equinum_image : ∀ A B X f, X ⊆ A → (f Inj A To B) → X ~ f.[X] :=
  fun (A B X f) => fun (h : X ⊆ A) => fun (h₁ : (f Inj A To B)) =>

    let g₁ := spec_is_spec (fun (t) => ∃ a ∈ X; (a . f . t)) (rng f)

    Exists.intro (f ⨡ X) (
      And.intro (
        let u := fun_restriction_prop A B X f (And.left h₁)
        let v := Iff.mp (And.left (subset_using_equality X A)) h
        let r := intersec2_comm A X
        let s := Eq.trans (r) (v)
        let m := eq_subst (fun (m) => function (f ⨡ X) m B) (A ∩ X) X (s) (u)
        let n₁:= And.right (And.left m)
        let n₂ := And.right m
        And.intro (And.intro (

          let h₆ := interset2sets_subset_prop f (X × rng f)
          let h₂ : (f ⨡ X) ⊆ (X × rng f) := And.right (h₆)

          fun (s) => fun (h₃ : s ∈ (f ⨡ X)) =>
            let h₄ := h₂ s h₃
            let h₅ := Iff.mp (cartesian_product_is_cartesian X (rng f) s) h₄
            Exists.elim h₅
            (
              fun (w) =>
                fun (hw : w ∈ X ∧ ∃ u ∈ (rng f); s = (w, u)) =>
                  Exists.elim (And.right hw)
                  (
                    fun (u) =>
                      fun (hu : u ∈ rng f ∧ s = (w, u)) =>
                        eq_subst (fun (m) => m ∈ (X × f.[X])) (w, u) s (Eq.symm (And.right hu)) (
                          Iff.mpr (cartesian_product_pair_prop X (f.[X]) w u) (
                            And.intro (And.left hw) (
                              Iff.mpr (g₁ u) (
                                And.intro (And.left hu) (Exists.intro w (And.intro (And.left hw) (
                                  eq_subst (fun (t) => t ∈ f) s (w, u) (And.right hu) (
                                    And.left h₆ s h₃

                                  )
                                )))
                              )
                            )
                          )
                        )
                  )
            )

        ) (n₁)) (n₂)
      ) (And.intro (inj_restriction_prop X f (And.right (h₁))) (
          fun (y) => fun (hy : y ∈ f.[X]) =>
            let g₂ := And.right (Iff.mp (g₁ y) hy)
            Exists.elim g₂
            (
              fun (w) =>
                fun (hw : w ∈ X ∧ (w . f . y)) =>
                  Exists.intro w (
                    Iff.mpr (intersect_2sets_prop f (X × (rng f)) (w, y))
                    (And.intro (And.right hw) (
                        Iff.mpr ((cartesian_product_pair_prop X (rng f)) w y) (
                          And.intro (And.left hw) (
                            And.left (Iff.mp (g₁ y) (hy))
                          )
                        )
                    ))

                  )
            )
      ))
    )


open Classical

theorem equinum_partition : ∀ A B X Y, (X ⊆ A) → (Y ⊆ B) → (X ~ Y) → ((A \ X) ~ (B \ Y)) → (A ~ B) :=
  fun (A B X Y) =>
    fun (h₁ : X ⊆ A) => fun (h₂ : Y ⊆ B) =>
      fun (h₃ : X ~ Y) =>
        fun (h₄ : ((A \ X) ~ (B \ Y))) =>
          Exists.elim h₃
          (
            fun (f) =>
              fun (hf : f Bij X To Y) =>
                Exists.elim h₄
                (
                  fun (g) =>
                    fun (hg : g Bij (A \ X) To (B \ Y)) =>
                      Exists.intro (f ∪ g) (And.intro (And.intro (And.intro (
                        fun (s) => fun (g₁ : s ∈ (f ∪ g)) =>
                          let h₅ := Iff.mp (union2sets_prop f g s) g₁
                          Or.elim h₅
                          (fun (h₆ : s ∈ f) =>
                            let h₇ := And.left (And.left (And.left hf)) s h₆
                            cartesian_product_subset X Y A B h₁ h₂ s h₇
                          )
                          (fun (h₆ : s ∈ g) =>
                            let h₇ := And.left (And.left (And.left hg)) s h₆
                            cartesian_product_subset (A \ X) (B \ Y) A B (difference_subset_prop A X) (difference_subset_prop B Y) s (h₇)
                          )
                      ) (
                        fun (x y z) =>
                          fun (g₀ : (x . (f ∪ g) . y)) =>
                            fun (g₂ : (x . (f ∪ g) . z)) =>
                              let s₀ := Iff.mp (union2sets_prop f g (x, y)) g₀
                              let s₁ := Iff.mp (union2sets_prop f g (x, z)) g₂
                              Or.elim s₀
                              (fun (hf₁ : (x . f . y)) =>
                                Or.elim s₁
                                (
                                  fun (hf₂ : (x . f . z)) =>
                                    And.right (And.left (And.left hf)) x y z hf₁ hf₂

                                )
                                (fun (hg₂ : (x . g . z)) =>
                                    let res₁ := Iff.mpr (dom_prop f x) (Exists.intro y hf₁)
                                    let res₂ := dom_function f X Y (And.left hf)
                                    let res₃ := eq_subst (fun (t) => x ∈ t) (dom f) X (Eq.symm res₂) (res₁)
                                    let res₄ := Iff.mpr (dom_prop g x) (Exists.intro z hg₂)
                                    let res₅ := dom_function g (A \ X) (B \ Y) (And.left hg)
                                    let res₆ := eq_subst (fun (t) => x ∈ t) (dom g) (A \ X) (Eq.symm res₅) (res₄)
                                    let res₇ := Iff.mp (difference_prop A X x) res₆
                                    let res₈ := And.right res₇ res₃
                                    (False.elim : False → (y = z)) res₈
                                )

                              )
                              (fun (hg₁ : (x . g . y)) =>
                                Or.elim s₁
                                (fun (hf₂ : (x . f . z)) =>
                                  let res₁ := Iff.mpr (dom_prop f x) (Exists.intro z hf₂)
                                  let res₂ := dom_function f X Y (And.left hf)
                                  let res₃ := eq_subst (fun (t) => x ∈ t) (dom f) X (Eq.symm res₂) (res₁)
                                  let res₄ := Iff.mpr (dom_prop g x) (Exists.intro y hg₁)
                                  let res₅ := dom_function g (A \ X) (B \ Y) (And.left hg)
                                  let res₆ := eq_subst (fun (t) => x ∈ t) (dom g) (A \ X) (Eq.symm res₅) (res₄)
                                  let res₇ := Iff.mp (difference_prop A X x) res₆
                                  let res₈ := And.right res₇ res₃
                                  (False.elim : False → (y = z)) res₈
                                )
                                (fun (hg₂ : (x . g . z)) =>
                                 And.right ( And.left (And.left hg)) x y z hg₁ hg₂
                                )
                              )
                      )) (
                        fun (s) => fun (h₁ : s ∈ A) =>
                          Or.elim (em (s ∈ X))
                          (fun (hf₂ : s ∈ X) =>
                            Exists.intro (f⦅s⦆) (
                              let prop₁ := function_value_pick_property f X Y s hf₂ (And.left hf)
                              Iff.mpr (union2sets_prop f g (s, f⦅s⦆)) (Or.inl (prop₁))

                            )
                          )
                          (fun (hg₂ : s ∉ X) =>
                            let a_comp_x := Iff.mpr (difference_prop A X s) (And.intro (h₁) (hg₂))
                            let prop₁ := function_value_pick_property g (A \ X) (B \ Y) s a_comp_x (And.left hg)
                            Exists.intro (g⦅s⦆) (
                              Iff.mpr (union2sets_prop f g (s, g⦅s⦆))  (Or.inr (prop₁))
                            )
                          )
                      ))
                      (And.intro (
                          fun (x y z) =>
                          fun (g₀ : (x . (f ∪ g) . z)) =>
                            fun (g₂ : (y . (f ∪ g) . z)) =>
                              let s₀ := Iff.mp (union2sets_prop f g (x, z)) g₀
                              let s₁ := Iff.mp (union2sets_prop f g (y, z)) g₂
                              Or.elim s₀
                              (fun (hf₁ : (x . f . z)) =>
                                Or.elim s₁
                                (
                                  fun (hf₂ : (y . f . z)) =>
                                    And.left (And.right hf) x y z hf₁ hf₂

                                )
                                (fun (hg₂ : (y . g . z)) =>
                                    let res₁ := And.left (And.left (And.left hf)) (x, z) hf₁
                                    let res₂ := And.right (Iff.mp (cartesian_product_pair_prop X Y x z) res₁)
                                    let res₃ := And.left (And.left (And.left hg)) (y, z) hg₂
                                    let res₄ := And.right (Iff.mp (cartesian_product_pair_prop (A \ X) (B \ Y) y z) res₃)
                                    let res₅ := And.right (Iff.mp (difference_prop B Y z) res₄)
                                    (False.elim : False → (x = y)) (res₅ res₂)
                                )

                              )
                              (fun (hg₁ : (x . g . z)) =>
                                Or.elim s₁
                                (fun (hf₂ : (y . f . z)) =>
                                    let res₁ := And.left (And.left (And.left hf)) (y, z) hf₂
                                    let res₂ := And.right (Iff.mp (cartesian_product_pair_prop X Y y z) res₁)
                                    let res₃ := And.left (And.left (And.left hg)) (x, z) hg₁
                                    let res₄ := And.right (Iff.mp (cartesian_product_pair_prop (A \ X) (B \ Y) x z) res₃)
                                    let res₅ := And.right (Iff.mp (difference_prop B Y z) res₄)
                                    (False.elim : False → (x = y)) (res₅ res₂)
                                )
                                (fun (hg₂ : (y . g . z)) =>
                                  And.left (And.right hg) x y z hg₁ hg₂
                                )
                              )


                      ) (
                          fun (s) => fun (h₁ : s ∈ B) =>
                          Or.elim (em (s ∈ Y))
                          (fun (hf₂ : s ∈ Y) =>
                            let res₁ := And.right (And.right hf) s hf₂
                            Exists.elim res₁
                            (
                              fun (w) =>
                                fun (hw : (w, s) ∈ f) =>
                                  Exists.intro w (
                                      Iff.mpr (union2sets_prop f g (w, s)) (Or.inl hw)
                                  )
                            )
                          )
                          (fun (hg₂ : s ∉ Y) =>
                            let res₁ := And.right (And.right hg) s (Iff.mpr (difference_prop B Y s) (And.intro (h₁) (hg₂)))
                            Exists.elim res₁
                            (
                              fun (w) =>
                                fun (hw : (w, s) ∈ g) =>
                                  Exists.intro w
                                  (
                                    Iff.mpr (union2sets_prop f g (w, s)) (Or.inr hw)
                                  )
                            )
                          )
                      )))
                )
          )







theorem equinum_cartesian_congr_right : ∀ A B C, (A ~ B) → (A × C) ~ (B × C) :=
  fun (A B C) => fun (h₁ : A ~ B) =>
    Exists.elim h₁
    (
      fun (f) =>
        fun (hf : f Bij A To B) =>

          let g := lam_fun (A × C) (B × C) (
            fun (pr) => (f⦅fst_coor pr⦆, snd_coor pr)
          )

          Exists.intro g (

              let func_prop := lam_then_fun_prop (fun (pr) => (f⦅fst_coor pr⦆, snd_coor pr)) (A × C) (B × C) (
                  fun (elem) => fun (h₂ : elem ∈ (A × C)) =>
                    let h₅ := fst_coor_set A C elem h₂
                    let h₇ := val_in_B f A B (And.left hf) (fst_coor elem) (h₅)
                    let h₀ := snd_coor_set A C elem h₂
                    let s := Iff.mpr (cartesian_product_pair_prop B C (f⦅fst_coor elem⦆) (snd_coor elem)) (
                      And.intro (h₇) (h₀)
                    )
                    s
              )

            And.intro (And.left func_prop) (And.intro (

              let h₂ := Iff.mpr (func_inj_prop (A × C) (B × C) g (And.left func_prop)) (
                fun (pr_x) => fun (h₃ : pr_x ∈ (A × C)) =>
                  fun (pr_y) => fun (h₄ : pr_y ∈ (A × C)) =>
                    fun (h₅ : g⦅pr_x⦆ = g⦅pr_y⦆) =>
                      let h₆ : g⦅pr_x⦆ = (f⦅fst_coor pr_x⦆, snd_coor pr_x) := And.right func_prop pr_x h₃
                      let h₇ : g⦅pr_y⦆ = (f⦅fst_coor pr_y⦆, snd_coor pr_y) := And.right func_prop pr_y h₄
                      let h₈ := Eq.trans (Eq.symm h₆) (h₅)
                      let h₉ := Eq.trans (h₈) (h₇)
                      let h₀ := Iff.mp (ordered_pair_set_prop (f⦅fst_coor pr_x⦆) (snd_coor pr_x) (f⦅fst_coor pr_y⦆) (snd_coor pr_y)) h₉
                      let s₁ := And.left h₀
                      let s₂ := And.right h₀
                      let s₃ := bij_is_inj A B f hf
                      let s₄ := Iff.mp (func_inj_prop A B f (And.left hf)) (s₃) (fst_coor pr_x) (fst_coor_set A C pr_x h₃) (fst_coor pr_y) (fst_coor_set A C pr_y h₄) s₁
                      let s₅ := Iff.mpr (ordered_pair_set_prop (fst_coor pr_x) (snd_coor pr_x) (fst_coor pr_y) (snd_coor pr_y)) (And.intro (s₄) (s₂))
                      let s₆ := fst_snd_then_unique A C pr_x h₃
                      let s₇ := fst_snd_then_unique A C pr_y h₄
                      Eq.trans (s₆) (Eq.trans (s₅) (Eq.symm (s₇)))
              )
              And.right h₂


            ) (
              let h₂ := Iff.mpr (func_surj_prop (A × C) (B × C) g (And.left func_prop)) (
                fun (pr_y) => fun (h₃ : pr_y ∈ B × C) =>
                  let h₄ := And.right (And.right hf)
                  let h₅ := Iff.mp (cartesian_product_is_cartesian B C pr_y) h₃
                  Exists.elim h₅
                  (
                    fun (w) => fun (hw : w ∈ B ∧ ∃ u ∈ C; pr_y = (w, u)) =>
                      Exists.elim (And.right hw)
                      (
                        fun (u) => fun (hu : u ∈ C ∧ pr_y = (w, u)) =>
                          let h₆ := h₄ w (And.left hw)
                          Exists.elim h₆
                          (
                            fun (s) =>
                              fun (hs : (s . f . w)) =>
                                let h₇ := Iff.mpr (dom_prop f s) (Exists.intro w hs)
                                let h₈ := dom_function f A B (And.left hf)
                                let h₉ := eq_subst (fun (p) => s ∈ p) (dom f) (A) (Eq.symm h₈) (h₇)
                                let h₀ := Iff.mp (function_equal_value_prop f A B (And.left hf) s w h₉) hs

                                let live_prop := Iff.mpr (cartesian_product_pair_prop A C s u) (And.intro (h₉) (And.left hu))

                                Exists.intro (s, u) (And.intro (
                                  live_prop
                                )
                                (
                                  let t₁ : g⦅(s, u)⦆ = (f⦅fst_coor (s, u)⦆, snd_coor (s, u)) := And.right func_prop (s, u) (live_prop)
                                  let t₂ := eq_subst (fun (p) => g⦅(s, u)⦆ = (f⦅p⦆, snd_coor (s, u))) (fst_coor (s, u)) s (coordinates_fst_coor s u) (t₁)
                                  let t₃ := eq_subst (fun (p) => g⦅(s, u)⦆ = (f⦅s⦆, p)) (snd_coor (s, u)) u (coordinates_snd_coor s u) (t₂)
                                  let t₄ := eq_subst (fun (p) => pr_y = (p, u)) w (f⦅s⦆) (h₀) (And.right hu)
                                  Eq.trans t₄ (Eq.symm (t₃))
                                )
                                )
                          )
                      )
                  )
              )

              And.right h₂
            ))
          )
    )





theorem equinum_power_congr_right : ∀ A B C, (A ~ B) → (A ℙow C) ~ (B ℙow C) :=
  fun (A B C) => fun (h₁ : A ~ B) =>
    Exists.elim h₁
    (
      fun (ϕ) =>
        fun (hϕ : ϕ Bij A To B) =>
          let ψ := lam_fun (A ℙow C) (B ℙow C) (
            fun (f) => ϕ ∘ f
          )

          Exists.intro ψ (

            let func_prop := lam_then_fun_prop (fun (f) => ϕ ∘ f) (A ℙow C) (B ℙow C) (
              fun (f) => fun (hf : f ∈ (A ℙow C)) =>
                let h₂ := And.right (Iff.mp (spec_is_spec (fun (p) => p Fun C To A) (𝒫 (C × A)) f) hf)
                let h₃ := And.left (function_composition f ϕ C A B h₂ (And.left hϕ))
                Iff.mpr (spec_is_spec (fun (p) => p Fun C To B) (𝒫 (C × B)) (ϕ ∘ f)) (And.intro (
                  Iff.mpr (boolean_set_is_boolean (C × B) (ϕ ∘ f)) (And.left (And.left h₃))) (h₃))
            )

            And.intro (And.left func_prop) (And.intro (
              let h₂ := Iff.mpr (func_inj_prop (A ℙow C) (B ℙow C) ψ (And.left func_prop)) (
                fun (f) => fun (h₃ : f ∈ A ℙow C) =>
                  fun (g) => fun (h₄ : g ∈ A ℙow C) =>
                    fun (h₅ : ψ⦅f⦆ = ψ⦅g⦆) =>
                      let f_is_func := And.right (Iff.mp (spec_is_spec (fun (p) => p Fun C To A) (𝒫 (C × A)) f) h₃)
                      let g_is_func := And.right (Iff.mp (spec_is_spec (fun (p) => p Fun C To A) (𝒫 (C × A)) g) h₄)
                      let h₆ : ψ⦅f⦆ = ϕ ∘ f := And.right func_prop f h₃
                      let h₇ : ψ⦅g⦆ = ϕ ∘ g := And.right func_prop g h₄
                      let h₈ := Eq.trans (Eq.symm h₆) (Eq.trans (h₅) (h₇))
                      let h₉ : ϕ⁻¹ ∘ (ϕ ∘ f) = ϕ⁻¹ ∘ (ϕ ∘ g) :=
                        eq_subst (fun (p) => ϕ⁻¹ ∘ (ϕ ∘ f) = ϕ⁻¹ ∘ p) (ϕ ∘ f) (ϕ ∘ g) (h₈) (Eq.refl (ϕ⁻¹ ∘ (ϕ ∘ f)))
                      let h₀ : (ϕ⁻¹ ∘ ϕ) ∘ f = ϕ⁻¹ ∘ (ϕ ∘ f) := composition_assoc (ϕ⁻¹) (ϕ) f
                      let s₁ : (ϕ⁻¹ ∘ ϕ) ∘ g = ϕ⁻¹ ∘ (ϕ ∘ g) := composition_assoc (ϕ⁻¹) (ϕ) g
                      let s₂ : (ϕ⁻¹ ∘ ϕ) ∘ f = id_ A ∘ f := eq_subst (fun (p) => p ∘ f = id_ A ∘ f) (id_ A) (ϕ⁻¹ ∘ ϕ) (Eq.symm (And.left (Iff.mp (id_bijection_criterion ϕ A B (And.left (And.left (And.left (hϕ))))) (hϕ)))) (Eq.refl (id_ A ∘ f))
                      let s₃ : (ϕ⁻¹ ∘ ϕ) ∘ f = f := eq_subst (fun (p) => (ϕ⁻¹ ∘ ϕ) ∘ f = p) (id_ A ∘ f) f (id_rel_composition_left C A f (And.left (And.left f_is_func))) (s₂)
                      let s₄ : (ϕ⁻¹ ∘ ϕ) ∘ g = id_ A ∘ g := eq_subst (fun (p) => p ∘ g = id_ A ∘ g) (id_ A) (ϕ⁻¹ ∘ ϕ) (Eq.symm (And.left (Iff.mp (id_bijection_criterion ϕ A B (And.left (And.left (And.left (hϕ))))) (hϕ)))) (Eq.refl (id_ A ∘ g))
                      let s₅ : (ϕ⁻¹ ∘ ϕ) ∘ g = g := eq_subst (fun (p) => (ϕ⁻¹ ∘ ϕ) ∘ g = p) (id_ A ∘ g) g (id_rel_composition_left C A g (And.left (And.left g_is_func))) (s₄)
                      Eq.trans (Eq.symm s₃) (Eq.trans (h₀) (Eq.trans (h₉) (Eq.trans (Eq.symm (s₁)) (s₅))))



              )
              And.right h₂
            ) (
              let h₂ := Iff.mpr (func_surj_prop (A ℙow C) (B ℙow C) ψ (And.left func_prop)) (
                fun (g) => fun (h₃ : g ∈ B ℙow C) =>
                  let h₄ := And.left (bijection_inv_mp ϕ A B hϕ)
                  let h₅ := And.right (Iff.mp (spec_is_spec (fun (p) => p Fun C To B) (𝒫 (C × B)) g) h₃)
                  let h₆ := function_composition g (ϕ⁻¹) C B A (h₅) (h₄)
                  let h₇ := Iff.mpr (spec_is_spec (fun (p) => p Fun C To A) (𝒫 (C × A)) (ϕ⁻¹ ∘ g)) (
                      And.intro (Iff.mpr (boolean_set_is_boolean (C × A) (ϕ⁻¹ ∘ g)) (And.left (And.left (And.left h₆)))) (And.left h₆)
                    )
                  Exists.intro (ϕ⁻¹ ∘ g) (And.intro (
                    h₇



                  ) (
                    let h₈ : ψ⦅ϕ⁻¹ ∘ g⦆ = ϕ ∘ (ϕ⁻¹ ∘ g)  := And.right func_prop ((ϕ⁻¹ ∘ g)) (h₇)
                    let h₉ : ψ⦅ϕ⁻¹ ∘ g⦆ = (ϕ ∘ ϕ⁻¹) ∘ g :=
                      eq_subst (fun (p) => ψ⦅ϕ⁻¹ ∘ g⦆ = p) (ϕ ∘ (ϕ⁻¹ ∘ g)) ((ϕ ∘ ϕ⁻¹) ∘ g) (Eq.symm (composition_assoc ϕ (ϕ⁻¹) g)) (h₈)
                    let h₀ : ψ⦅ϕ⁻¹ ∘ g⦆ = (id_ B) ∘ g :=  eq_subst (fun (p) => ψ⦅ϕ⁻¹ ∘ g⦆ = p ∘ g) (ϕ ∘ ϕ⁻¹) (id_ B) (And.right (Iff.mp (id_bijection_criterion ϕ A B (And.left (And.left (And.left hϕ)))) (hϕ))) (h₉)
                    let res : ψ⦅ϕ⁻¹ ∘ g⦆ = g := eq_subst (fun(p) => ψ⦅ϕ⁻¹ ∘ g⦆ = p) ((id_ B) ∘ g) (g) (id_rel_composition_left C B g (And.left (And.left (h₅)))) (h₀)
                    Eq.symm res
                  ))
              )

              And.right h₂
            ))
          )
    )



theorem equinum_power_congr_left : ∀ A B C, (A ~ B) → (C ℙow A) ~ (C ℙow B) :=
  fun (A B C) => fun (h₁ : A ~ B) =>
    Exists.elim h₁
    (
      fun (ϕ) =>
        fun (hϕ : ϕ Bij A To B) =>
          let ψ := lam_fun (C ℙow A) (C ℙow B) (
            fun (f) => f ∘ ϕ⁻¹
          )

          Exists.intro ψ (

            let func_prop := lam_then_fun_prop (fun (t) => t∘ ϕ⁻¹) (C ℙow A) (C ℙow B) (
              fun (s) => fun (h₁ : s ∈ (C ℙow A)) =>
                let res₁ := bijection_inv_mp ϕ A B hϕ
                let res₂ := And.left (function_composition (ϕ⁻¹) s B A C (And.left res₁) (Iff.mp (power_set_prop A C s) h₁))
                Iff.mpr (power_set_prop B C (s ∘ ϕ⁻¹)) (res₂)
            )

            let inj_prop := And.right (Iff.mpr (func_inj_prop (C ℙow A) (C ℙow B) ψ (And.left func_prop)) (
              fun (f) => fun (hf : f ∈ (C ℙow A)) => fun (g) => fun (hg : g ∈ (C ℙow A)) =>
                fun (heq: ψ⦅f⦆ = ψ⦅g⦆) =>
                  let func_prop₂ : ψ⦅f⦆ = f ∘ ϕ⁻¹ := And.right func_prop f hf
                  let func_prop₃ : ψ⦅g⦆ = g ∘ ϕ⁻¹ := And.right func_prop g hg
                  let eq_prop := Eq.trans (Eq.symm func_prop₂) (Eq.trans (heq) (func_prop₃))
                  let eq_prop₂ : (f ∘ ϕ⁻¹) ∘ ϕ = (g ∘ ϕ⁻¹) ∘ ϕ :=
                  eq_subst (fun (t) => t ∘ ϕ = (g ∘ ϕ⁻¹) ∘ ϕ) (g ∘ ϕ⁻¹) (f ∘ ϕ⁻¹) (Eq.symm (eq_prop)) (Eq.refl ((g ∘ inv ϕ) ∘ ϕ))
                  let eq_prop₃ := composition_assoc f (ϕ⁻¹) ϕ
                  let eq_prop₄ := composition_assoc g (ϕ⁻¹) ϕ
                  let eq_prop₅ := Eq.trans (Eq.symm eq_prop₃) (Eq.trans (eq_prop₂) (eq_prop₄))
                  let eq_prop₆ := And.left (Iff.mp (id_bijection_criterion ϕ A B (And.left (And.left (And.left hϕ)))) hϕ)
                  let eq_prop₇ := eq_subst (fun (t) => f ∘ t = g ∘ t) (ϕ⁻¹ ∘ ϕ) (id_ A) (eq_prop₆) (eq_prop₅)
                  let eq_prop₈ := id_rel_composition_right A C f (And.left (And.left (Iff.mp (power_set_prop A C f) (hf))))
                  let eq_prop₉ := id_rel_composition_right A C g (And.left (And.left (Iff.mp (power_set_prop A C g) (hg))))
                  let eq_prop₀ := eq_subst (fun (t) => t = g ∘ (id_ A)) (f ∘ (id_ A)) (f) (eq_prop₈) (eq_prop₇)
                  eq_subst (fun (t) => f = t) (g ∘ (id_ A)) g (eq_prop₉) (eq_prop₀)
            ))

            let surj_prop := And.right (Iff.mpr (func_surj_prop (C ℙow A) (C ℙow B) ψ (And.left func_prop)) (
              fun (g) => fun (hg : g ∈ (C ℙow B)) =>
                Exists.intro (g ∘ ϕ) (

                  let res₁ := Iff.mpr (power_set_prop A C (g ∘ ϕ)) (
                    And.left (function_composition ϕ g A B C (And.left hϕ) (Iff.mp (power_set_prop B C g) (hg)))
                    )

                  And.intro
                  (

                    res₁

                  )
                  (
                    let res₂ : ψ⦅g ∘ ϕ⦆ = (g ∘ ϕ) ∘ ϕ⁻¹ := And.right func_prop (g ∘ ϕ) res₁
                    let res₂ : ψ⦅g ∘ ϕ⦆ = g ∘ (ϕ ∘ ϕ⁻¹) := eq_subst (fun (t) => ψ⦅g ∘ ϕ⦆ = t) ( (g ∘ ϕ) ∘ ϕ⁻¹) (g ∘ (ϕ ∘ ϕ⁻¹)) (composition_assoc g ϕ (ϕ⁻¹)) (res₂)
                    let res₀ := And.right (Iff.mp (id_bijection_criterion ϕ A B (And.left (And.left (And.left hϕ)))) hϕ)
                    let res₃ : ψ⦅g ∘ ϕ⦆ = g ∘ (id_ B) := eq_subst (fun (t) =>ψ⦅g ∘ ϕ⦆ = g ∘ t) (ϕ ∘ ϕ⁻¹) (id_ B) (res₀) (res₂)
                    let rel_prop₂ := And.left (And.left (Iff.mp (power_set_prop B C g) (hg)))
                    Eq.symm (eq_subst (fun (t) => ψ⦅g ∘ ϕ⦆ = t) (g ∘ (id_ B)) g (id_rel_composition_right B C g (rel_prop₂)) (res₃))
                  )
                )
            ))


            And.intro (


            And.left func_prop

          ) (And.intro (inj_prop) (surj_prop)))
    )


theorem equinum_cartesian_comm : ∀ A B, (A × B) ~ (B × A) :=
  fun (A B) =>
    let ψ := lam_fun (A × B) (B × A) (
      fun (pr) => (snd_coor pr, fst_coor pr)
    )

    let func_prop := lam_then_fun_prop (fun (pr) => (snd_coor pr, fst_coor pr)) (A × B) (B × A) (
      fun (pr) => fun (h₁ : pr ∈ (A × B)) =>
        let prop₁ := Iff.mp (cartesian_product_is_cartesian A B pr) h₁
        Exists.elim prop₁
        (
          fun (w) =>
            fun (hw : w ∈ A ∧ ∃ y ∈ B; pr = (w, y)) =>
              Exists.elim (And.right hw)
              (
                fun (u) =>
                  fun (hu : u ∈ B ∧ pr = (w, u)) =>
                    eq_subst (fun (t) => (snd_coor t, fst_coor t) ∈ (B × A)) (w, u) pr (Eq.symm (And.right hu)) (
                      Iff.mpr (cartesian_product_pair_prop B A (snd_coor (w, u)) (fst_coor (w, u))) (And.intro (
                        eq_subst (fun (s) => s ∈ B) (u) (snd_coor (w, u)) (Eq.symm (coordinates_snd_coor w u)) (And.left hu)
                      ) (
                        eq_subst (fun (s) => s ∈ A) (w) (fst_coor (w, u)) (Eq.symm (coordinates_fst_coor w u)) (And.left hw)
                      ))
                    )
              )
        )
    )

    let inj_prop := Iff.mpr ((func_inj_prop (A × B) (B × A) ψ) (And.left func_prop)) (
      fun (pr₁) => fun (h₁ : pr₁ ∈ (A × B)) => fun (pr₂) => fun (h₂ : pr₂ ∈ (A × B)) =>
        fun (h₃ :  ψ⦅pr₁⦆ = ψ⦅pr₂⦆) =>
          let prop₁ : ψ⦅pr₁⦆ = (snd_coor pr₁, fst_coor pr₁) := And.right func_prop pr₁ h₁
          let prop₂ : ψ⦅pr₂⦆ = (snd_coor pr₂, fst_coor pr₂) := And.right func_prop pr₂ h₂
          let prop₃ := Eq.trans (Eq.symm prop₁) (Eq.trans (h₃) (prop₂))
          let prop₄ := Iff.mp (ordered_pair_set_prop (snd_coor pr₁) (fst_coor pr₁) (snd_coor pr₂) (fst_coor pr₂)) prop₃
          let prop₅ := Iff.mpr (ordered_pair_set_prop (fst_coor pr₁) (snd_coor pr₁) (fst_coor pr₂) (snd_coor pr₂)) (And.intro (And.right prop₄) (And.left prop₄))
          Eq.trans (fst_snd_then_unique A B pr₁ h₁) (Eq.trans (prop₅) (Eq.symm (fst_snd_then_unique A B pr₂ h₂)))
    )

    let surj_prop := Iff.mpr (func_surj_prop (A × B) (B × A) ψ (And.left func_prop)) (
      fun (pr) => fun (h : pr ∈ (B × A)) =>
        let where_prop₁ := Iff.mpr (cartesian_product_pair_prop A B (snd_coor pr) (fst_coor pr)) (
          And.intro (snd_coor_set B A pr h) (fst_coor_set B A pr h))
        Exists.intro ((snd_coor pr, fst_coor pr)) (And.intro (where_prop₁) (
          let res₁ : ψ⦅(snd_coor pr, fst_coor pr)⦆ = (snd_coor ((snd_coor pr, fst_coor pr)), fst_coor (snd_coor pr, fst_coor pr))
          := And.right func_prop (snd_coor pr, fst_coor pr) where_prop₁
          let res₂ := coordinates_snd_coor (snd_coor pr) (fst_coor pr)
          let res₃ := coordinates_fst_coor (snd_coor pr) (fst_coor pr)
          let res₄ := eq_subst (fun (t) => ψ⦅(snd_coor pr, fst_coor pr)⦆ = (t, fst_coor (snd_coor pr, fst_coor pr)))
           (snd_coor ((snd_coor pr, fst_coor pr))) (fst_coor pr) (res₂) (res₁)
          let res₅ := eq_subst (fun (t) => ψ⦅(snd_coor pr, fst_coor pr)⦆ = (fst_coor pr, t)) (fst_coor (snd_coor pr, fst_coor pr))
           (snd_coor pr) (res₃) (res₄)
          Eq.symm (eq_subst (fun (t) => ψ⦅(snd_coor pr, fst_coor pr)⦆ = t) (fst_coor pr, snd_coor pr) pr (Eq.symm (fst_snd_then_unique B A pr h)) (res₅))
        ))
    )

    Exists.intro ψ (And.intro (And.left func_prop) (And.intro (And.right inj_prop) (And.right surj_prop)))




theorem equinum_cartesian_congr_left : ∀ A B C, (A ~ B) → (C × A) ~ (C × B) :=
  fun (A B C) =>
    fun (h₁ : (A ~ B)) =>
      let h₂ := equinum_cartesian_congr_right A B C h₁
      let h₃ := equinum_cartesian_comm C A
      let h₄ := equinum_cartesian_comm B C
      equinum_trans (C × A) (A × C) (C × B) (h₃) (equinum_trans (A × C) (B × C) (C × B) (h₂) (h₄))




theorem equinum_cartesian_assoc : ∀ A B C, ((A × B) × C) ~ (A × (B × C)) :=
  fun (A B C) =>
    let ψ := lam_fun ((A × B) × C) (A × (B × C)) (
      fun (pr) => (fst_coor (fst_coor pr), (snd_coor (fst_coor pr), snd_coor pr))
    )


    let func_prop := lam_then_fun_prop (fun (pr) => (fst_coor (fst_coor pr), (snd_coor (fst_coor pr), snd_coor pr))) ((A × B) × C) (A × (B × C)) (
      fun (pr) => fun (h₁ : pr ∈ ((A × B) × C)) =>
        let res₁ := fst_coor_set (A × B) C pr h₁
        let res₂ := snd_coor_set (A × B) C pr h₁
        let res₄ := fst_coor_set A B (fst_coor pr) res₁
        let res₅ := snd_coor_set A B (fst_coor pr) res₁
        let res₆ := Iff.mpr (cartesian_product_pair_prop B C (snd_coor (fst_coor pr)) (snd_coor pr)) (And.intro (res₅) (res₂))
        Iff.mpr (cartesian_product_pair_prop A (B × C) (fst_coor (fst_coor pr)) (snd_coor (fst_coor pr), snd_coor pr)) (
          And.intro (res₄) (res₆)
        )
    )


    let inj_prop := Iff.mpr (func_inj_prop ((A × B) × C) (A × (B × C)) ψ (And.left func_prop)) (
      fun (pr₁) =>
        fun (h₁ : pr₁ ∈ ((A × B) × C)) =>
          fun (pr₂) =>
            fun (h₂ : pr₂ ∈ ((A × B) × C)) =>
              fun (h : ψ⦅pr₁⦆ = ψ⦅pr₂⦆) =>
                let res₁ : ψ⦅pr₁⦆ = (fst_coor (fst_coor pr₁), (snd_coor (fst_coor pr₁), snd_coor pr₁)) := And.right func_prop pr₁ h₁
                let res₂ : ψ⦅pr₂⦆ = (fst_coor (fst_coor pr₂), (snd_coor (fst_coor pr₂), snd_coor pr₂)) := And.right func_prop pr₂ h₂
                let res₃ := Eq.trans (Eq.symm res₁) (Eq.trans h (res₂))
                let res₄ := Iff.mp (ordered_pair_set_prop (fst_coor (fst_coor pr₁)) (snd_coor (fst_coor pr₁), snd_coor pr₁)
                (fst_coor (fst_coor pr₂)) (snd_coor (fst_coor pr₂), snd_coor pr₂)) res₃
                let res₅ := And.left res₄
                let res₆ := Iff.mp (ordered_pair_set_prop (snd_coor (fst_coor pr₁)) (snd_coor pr₁)
                 (snd_coor (fst_coor pr₂)) (snd_coor pr₂)) (And.right res₄)
                let res₇ := And.left res₆
                let res₈ := And.right res₆
                let res₉ := Iff.mpr (ordered_pair_set_prop (fst_coor (fst_coor pr₁)) (snd_coor (fst_coor pr₁)) (fst_coor (fst_coor pr₂)) (snd_coor (fst_coor (pr₂)))) (
                  And.intro (res₅) (res₇)
                )
                let res₀ := fst_coor_set (A × B) C pr₁ h₁
                let ans₀ := fst_snd_then_unique A B (fst_coor pr₁) res₀
                let res₁ := fst_coor_set (A × B) C pr₂ h₂
                let ans₁ := fst_snd_then_unique A B (fst_coor pr₂) res₁
                let ans₂ := Eq.trans (ans₀) (Eq.trans (res₉) (Eq.symm (ans₁)))
                let ans₃ := Iff.mpr (ordered_pair_set_prop (fst_coor pr₁) (snd_coor pr₁) (fst_coor pr₂) (snd_coor pr₂)) (
                  And.intro (ans₂) (res₈)
                )
                let ans₄ := fst_snd_then_unique (A × B) C pr₁ h₁
                let ans₅ := fst_snd_then_unique (A × B) C pr₂ h₂
                Eq.trans (ans₄) (Eq.trans (ans₃) (Eq.symm (ans₅)))
    )

    let surj_prop := Iff.mpr (func_surj_prop ((A × B) × C) (A × (B × C)) ψ (And.left func_prop)) (
      fun (pr) => fun (h₁ : pr ∈ (A × (B × C))) =>
        let pr_x := ((fst_coor pr, fst_coor (snd_coor pr)), snd_coor (snd_coor pr))
        let s₁ := fst_coor_set A (B × C) pr h₁
        let s₂ := snd_coor_set A (B × C) pr h₁
        let s₃ := fst_coor_set B C (snd_coor pr) s₂
        let s₄ := snd_coor_set B C (snd_coor pr) s₂
        let s₅ := Iff.mpr (cartesian_product_pair_prop A B (fst_coor pr) (fst_coor (snd_coor pr))) (
          And.intro (s₁) (s₃)
        )
        let s₆ := Iff.mpr (cartesian_product_pair_prop (A × B) C ((fst_coor pr, fst_coor (snd_coor pr))) (snd_coor (snd_coor pr))) (
          And.intro (s₅) (s₄)
        )
        Exists.intro (pr_x) (
          And.intro
          (
            s₆
          )
          (
            let r := (fst_coor (fst_coor pr_x), (snd_coor (fst_coor pr_x), snd_coor pr_x))

            let s₇ : ψ⦅pr_x⦆ = r := And.right func_prop pr_x s₆

            let t₀ := val_in_B ψ ((A × B) × C) (A × (B × C)) (And.left func_prop) pr_x (s₆)
            let t₁ := eq_subst (fun (u) => u ∈ (A × (B × C))) (ψ⦅pr_x⦆) r (s₇) (t₀)


            let s₈ : snd_coor r = (snd_coor (fst_coor pr_x), snd_coor pr_x) := coordinates_snd_coor (fst_coor (fst_coor pr_x)) (snd_coor (fst_coor pr_x), snd_coor pr_x)
            let s₉ : snd_coor pr_x = snd_coor (snd_coor pr) := coordinates_snd_coor (fst_coor pr, fst_coor (snd_coor pr)) (snd_coor (snd_coor pr))
            let s₀ : fst_coor pr_x = (fst_coor pr, fst_coor (snd_coor pr)) := coordinates_fst_coor (fst_coor pr, fst_coor (snd_coor pr)) (snd_coor (snd_coor pr))
            let u₇ : snd_coor (fst_coor pr, fst_coor (snd_coor pr)) = fst_coor (snd_coor pr) := coordinates_snd_coor (fst_coor pr) (fst_coor (snd_coor pr))
            let u₈ : snd_coor (fst_coor pr_x) = fst_coor (snd_coor pr) := eq_subst (fun (u) => snd_coor u = fst_coor (snd_coor pr)) (fst_coor pr, fst_coor (snd_coor pr)) (fst_coor pr_x) (Eq.symm (s₀)) (u₇)
            let a₁ := Iff.mpr (ordered_pair_set_prop (snd_coor (fst_coor pr_x)) (snd_coor pr_x) (fst_coor (snd_coor pr)) (snd_coor (snd_coor pr))) (
              And.intro (u₈) (s₉)
            )
            let a₂ := Eq.symm (fst_snd_then_unique B C (snd_coor pr) s₂)
            let a₃ := Eq.trans (s₈) (Eq.trans a₁ a₂)


            let a₄ : fst_coor r = fst_coor (fst_coor pr_x) := coordinates_fst_coor (fst_coor (fst_coor pr_x)) (snd_coor (fst_coor pr_x), snd_coor pr_x)
            let a₅ := coordinates_fst_coor (fst_coor pr) (fst_coor (snd_coor pr))
            let a₆ := eq_subst (fun (u) => fst_coor u = fst_coor pr) (fst_coor pr, fst_coor (snd_coor pr)) (fst_coor pr_x) (Eq.symm s₀) (a₅)
            let a₇ := Eq.trans a₄ (a₆)

            let res₁ := fst_snd_then_unique A (B × C) pr h₁
            let res₂ := Iff.mpr (ordered_pair_set_prop (fst_coor pr) (snd_coor pr) (fst_coor r) (snd_coor r)) (
              And.intro (Eq.symm a₇) (Eq.symm a₃)
            )
            let res₃ := fst_snd_then_unique A (B × C) r t₁

            Eq.symm (Eq.trans (s₇) (Eq.trans (res₃) (Eq.trans (Eq.symm (res₂)) (Eq.symm (res₁)))))

          )
        )
    )
    Exists.intro ψ (And.intro (And.left func_prop) (And.intro (And.right inj_prop) (And.right surj_prop)))



theorem equinum_cartesian_power : ∀ A B C, ((A × B) ℙow C) ~ (A ℙow C) × (B ℙow C) :=
  fun (A B C) =>

    let Y := (A × B) ℙow C
    let Z := (A ℙow C) × (B ℙow C)

    let prop := fun (f) => fun (P : Set → Set) => fun (c) => P (f⦅c⦆)

    let left_func := fun (f) => lam_fun C A (
          prop f fst_coor
        )

    let right_func := fun (f) => lam_fun C B (
          prop f snd_coor
        )

    let pred_ψ := fun (f) =>
        (left_func f, right_func f)


    let ψ := lam_fun Y Z (
      pred_ψ
    )

    let u := fun (f) => fun (h₁ : f ∈ Y) => Iff.mp (power_set_prop C (A × B) f) h₁

    let v := fun (f) => fun (h₁ : f ∈ Y) => fun (X) => fun (P : Set → Set) => fun (hx : (∀ x ∈ A × B; P x ∈ X)) =>
        let p := fun (c) => fun (hc : c ∈ C) =>
          let m := val_in_B f C (A × B) (u f h₁) c hc
          hx (f⦅c⦆) m
        let v_func_property := (lam_then_fun_prop (prop f P) C X p)
        let r := And.left v_func_property
        And.intro (Iff.mpr (power_set_prop C X (lam_fun C X (prop f P))) r) (And.right (v_func_property))

    let v_fst := fun (f) => fun (h₁ : f ∈ Y) => v f h₁ A (fst_coor) (fst_coor_set A B)
    let v_snd := fun (f) => fun (h₁ : f ∈ Y) => v f h₁ B (snd_coor) (snd_coor_set A B)


    let func_prop := lam_then_fun_prop pred_ψ Y Z (
      fun (f) => fun (h₁ : f ∈ Y) =>
        Iff.mpr (cartesian_product_pair_prop (A ℙow C) (B ℙow C) (lam_fun C A (
          prop f fst_coor
        )) (lam_fun C B (
          prop f snd_coor
        ))) (



          And.intro (And.left (v_fst f h₁)) (And.left (v_snd f h₁))
          )
    )

    Exists.intro ψ (And.intro (And.left func_prop) (And.intro (
      And.right (Iff.mpr (func_inj_prop Y Z ψ (And.left func_prop)) (
        fun (f) => fun (hf : f ∈ Y) => fun (g) => fun (hg : g ∈ Y) =>
          fun (hψ : ψ⦅f⦆ = ψ⦅g⦆) =>
            let hψf := val_in_B ψ Y Z (And.left func_prop) f hf
            let hψg := val_in_B ψ Y Z (And.left func_prop) g hg
            let hψfc := Iff.mp (cartesian_product_is_cartesian (A ℙow C) (B ℙow C) (ψ⦅f⦆)) hψf
            let hψgc := Iff.mp (cartesian_product_is_cartesian (A ℙow C) (B ℙow C) (ψ⦅g⦆)) hψg
            Exists.elim hψfc
            (
              fun (ψf₁) =>
                fun (hψf₁ : ψf₁ ∈ (A ℙow C) ∧ ∃ r ∈ (B ℙow C); ψ⦅f⦆ = (ψf₁, r)) =>
                  Exists.elim (And.right hψf₁)
                  (
                    fun (ψf₂) =>
                      fun (hψf₂ : ψf₂ ∈ (B ℙow C) ∧ ψ⦅f⦆ = (ψf₁, ψf₂)) =>
                        Exists.elim hψgc
                        (
                          fun (ψg₁) =>
                            fun (hψg₁ : ψg₁ ∈ (A ℙow C) ∧ ∃ r ∈ (B ℙow C); ψ⦅g⦆ = (ψg₁, r)) =>
                              Exists.elim (And.right hψg₁)
                              (
                                fun (ψg₂) =>
                                  fun (hψg₂ : ψg₂ ∈ (B ℙow C) ∧ ψ⦅g⦆ = (ψg₁, ψg₂)) =>
                                    let u := Iff.mp (ordered_pair_set_prop ψf₁ ψf₂ ψg₁ ψg₂) (
                                      Eq.trans (Eq.symm (And.right hψf₂)) (
                                        Eq.trans (hψ) (And.right hψg₂)
                                      )
                                    )
                                    let vf : ψ⦅f⦆ = pred_ψ f := And.right func_prop f hf
                                    let vf₂ := Iff.mp (ordered_pair_set_prop ψf₁ ψf₂ (left_func f) (right_func f)) (
                                      Eq.trans (Eq.symm (And.right hψf₂)) (vf)
                                    )
                                    let vg : ψ⦅g⦆ = pred_ψ g := And.right func_prop g hg
                                    let vg₂ := Iff.mp (ordered_pair_set_prop ψg₁ ψg₂ (left_func g) (right_func g)) (
                                      Eq.trans (Eq.symm (And.right hψg₂)) (vg)
                                    )
                                    let vgf₁ := Eq.trans (Eq.trans (Eq.symm (And.left vf₂)) (And.left u)) (And.left vg₂)
                                    let vgf₂ := Eq.trans (Eq.trans (Eq.symm (And.right vf₂)) (And.right u)) (And.right vg₂)

                                    let ffunc := Iff.mp (power_set_prop C (A × B) f) hf
                                    let gfunc := Iff.mp (power_set_prop C (A × B) g) hg

                                    Iff.mpr (equal_functions_abc_A f g C (A × B) (A × B) ffunc gfunc) (
                                      fun (c) => fun (hc : c ∈ C) =>

                                        let left_fgc := Iff.mp (equal_functions_abc_A (left_func f) (left_func g ) C A A (
                                          Iff.mp (power_set_prop C A (left_func f)) (And.left (v_fst f hf))
                                        ) (Iff.mp (power_set_prop C A (left_func g)) (And.left (v_fst g hg)))) vgf₁ c hc

                                        let v_fst_f₁ : (left_func f)⦅c⦆ = fst_coor (f⦅c⦆) := And.right (v_fst f hf) c hc
                                        let v_fst_g₁ : (left_func g)⦅c⦆ = fst_coor (g⦅c⦆) := And.right (v_fst g hg) c hc
                                        let fst_fg := Eq.trans (Eq.trans (Eq.symm (v_fst_f₁)) (left_fgc)) (v_fst_g₁)

                                        let right_fgc := Iff.mp (equal_functions_abc_A (right_func f) (right_func g ) C B B (
                                          Iff.mp (power_set_prop C B (right_func f)) (And.left (v_snd f hf))
                                        ) (Iff.mp (power_set_prop C B (right_func g)) (And.left (v_snd g hg)))) vgf₂ c hc

                                        let v_snd_f₁ : (right_func f)⦅c⦆ = snd_coor (f⦅c⦆) := And.right (v_snd f hf) c hc
                                        let v_snd_g₁ : (right_func g)⦅c⦆ = snd_coor (g⦅c⦆) := And.right (v_snd g hg) c hc
                                        let snd_fg := Eq.trans (Eq.trans (Eq.symm (v_snd_f₁)) (right_fgc)) (v_snd_g₁)

                                        let f_val := val_in_B f C (A × B) (ffunc) c hc
                                        let g_val := val_in_B g C (A × B) (gfunc) c hc

                                        equal_fst_snd A B (f⦅c⦆) (g⦅c⦆) f_val g_val (fst_fg) (snd_fg)
                                    )
                              )
                        )
                  )
            )
      ))
    ) (

      And.right (Iff.mpr (func_surj_prop Y Z ψ (And.left func_prop)) (
        fun (pr) => fun (hpr : pr ∈ Z) =>
          let P := fun (c) => ((fst_coor pr)⦅c⦆, (snd_coor pr)⦅c⦆)
          let f := lam_fun C (A × B) P

          Exists.intro f (
            let fst_pr := val_in_B (fst_coor pr) C A
              (Iff.mp (power_set_prop C A (fst_coor pr)) (fst_coor_set (A ℙow C) (B ℙow C) pr hpr))
            let snd_pr := val_in_B (snd_coor pr) C B
              (Iff.mp (power_set_prop C B (snd_coor pr)) (snd_coor_set (A ℙow C) (B ℙow C) pr hpr))
            let pr_prop := fun (c) => fun (hc : c ∈ C) =>
              Iff.mpr (cartesian_product_pair_prop A B ((fst_coor pr)⦅c⦆) ((snd_coor pr)⦅c⦆)) (
                And.intro (fst_pr c hc) (snd_pr c hc)
              )
            let f_func_prop := lam_then_fun_prop P C (A × B) (pr_prop)

            let fY := Iff.mpr (power_set_prop C (A × B) f) (And.left f_func_prop)

            And.intro (
              fY
            ) (
              let hψf := val_in_B ψ Y Z (And.left func_prop) f fY


              let vf : ψ⦅f⦆ = pred_ψ f := And.right func_prop f fY

              let vf₁ : fst_coor (ψ⦅f⦆) = left_func f := eq_subst (fun (t) => fst_coor t = left_func f) (pred_ψ f) (ψ⦅f⦆) (Eq.symm vf) (
                coordinates_fst_coor (left_func f) (right_func f))

              let vf₂ : snd_coor (ψ⦅f⦆) = right_func f := eq_subst (fun (t) => snd_coor t = right_func f) (pred_ψ f) (ψ⦅f⦆) (Eq.symm vf) (
                coordinates_snd_coor (left_func f) (right_func f))

              let first := fst_coor_set (A ℙow C) (B ℙow C) pr hpr
              let first₂ := Iff.mp (power_set_prop C A (fst_coor pr)) first
              let second := snd_coor_set (A ℙow C) (B ℙow C) pr hpr
              let second₂ := Iff.mp (power_set_prop C B (snd_coor pr)) second
              let third := Iff.mp (power_set_prop C A (left_func f)) (And.left (v_fst f fY))
              let fourth := Iff.mp (power_set_prop C B (right_func f)) (And.left (v_snd f fY))
              let ffunc_prop := And.right f_func_prop


              equal_fst_snd (A ℙow C) (B ℙow C) pr (ψ⦅f⦆) hpr hψf (

                Eq.trans (
                  Iff.mpr (equal_functions_abc_A (fst_coor pr) (left_func f) C A A (first₂) (third)) (
                    fun (c) => fun (hc : c ∈ C) =>
                      let u := And.right (v_fst f fY) c hc

                      Eq.trans (Eq.symm (

                        let v : fst_coor (P c) = (fst_coor pr)⦅c⦆ := coordinates_fst_coor ((fst_coor pr)⦅c⦆) ((snd_coor pr)⦅c⦆)
                        eq_subst (fun (t) => fst_coor t = (fst_coor pr)⦅c⦆) (P c) (f⦅c⦆) (Eq.symm (ffunc_prop c hc)) (v)

                      )) (Eq.symm (u))
                  )
                ) (Eq.symm vf₁)

              ) (
                Eq.trans (
                  Iff.mpr (equal_functions_abc_A (snd_coor pr) (right_func f) C B B (second₂) fourth) (
                    fun (c) => fun (hc : c ∈ C) =>
                      let u := And.right (v_snd f fY) c hc
                      Eq.trans (Eq.symm (

                        let v : snd_coor (P c) = (snd_coor pr)⦅c⦆ := coordinates_snd_coor ((fst_coor pr)⦅c⦆) ((snd_coor pr)⦅c⦆)
                        eq_subst (fun (t) => snd_coor t = (snd_coor pr)⦅c⦆) (P c) (f⦅c⦆) (Eq.symm (ffunc_prop c hc)) (v)
                      )) (Eq.symm (u))
                  )
                ) (Eq.symm vf₂)
              )
            )
          )
      ))
    )))


theorem equinum_power_cartesian : ∀ A B C, ((A ℙow B) ℙow C) ~ (A ℙow (B × C)) :=
  fun (A B C) =>
    let first := equinum_cartesian_comm C B
    let second := equinum_power_congr_left (C × B) (B × C) A first
    equinum_trans ((A ℙow B) ℙow C) (A ℙow (C × B)) (A ℙow (B × C)) (

      let X := (A ℙow B) ℙow C
      let Y := A ℙow (C × B)
      let Q := fun (f) => (fun (pr) => (f⦅fst_coor pr⦆)⦅snd_coor pr⦆)
      let P := fun (f) =>
        lam_fun (C × B) A (Q f)
      let ψ := lam_fun X Y P



      let P_prop := fun (f) => fun (hf : f ∈ X) =>
        let Q_prop := fun (pr) => fun (hpr : pr ∈ C × B) =>
          let fst_coor_pr := fst_coor_set C B pr hpr
          let snd_coor_pr := snd_coor_set C B pr hpr
          let f_func := Iff.mp (power_set_prop C (A ℙow B) f) hf
          let f_func_fst := val_in_B f C (A ℙow B) f_func (fst_coor pr) fst_coor_pr
          let f_func_fst_func := Iff.mp (power_set_prop B A (f⦅fst_coor pr⦆)) f_func_fst
          val_in_B (f⦅fst_coor pr⦆) B A f_func_fst_func (snd_coor pr) snd_coor_pr
        let lam_fun_P := (lam_then_fun_prop (Q f) (C × B) A Q_prop)
        let g := lam_fun (C × B) A (Q f)
        And.intro (Iff.mpr (power_set_prop (C × B) A g) (And.left lam_fun_P)) (And.right lam_fun_P)


      let func_prop := lam_then_fun_prop P X Y (fun (f) => fun (hf : f ∈ X) => (And.left (P_prop f hf)))



      Exists.intro ψ (And.intro (And.left func_prop) (And.intro (

        And.right (Iff.mpr (func_inj_prop X Y ψ (And.left func_prop)) (

          fun (f) => fun (hf : f ∈ X) => fun (g) => fun (hg : g ∈ X) =>
            fun (hψ : ψ⦅f⦆ = ψ⦅g⦆) =>
              let power_func_f := Iff.mp (power_set_prop C (A ℙow B) f) hf
              let power_func_g := Iff.mp (power_set_prop C (A ℙow B) g) hg

              Iff.mpr (equal_functions_abc_A f g (C) (A ℙow B) (A ℙow B) power_func_f power_func_g) (
                fun (c) => fun (hc : c ∈ C) =>
                  let fc_func_set := val_in_B f C (A ℙow B) power_func_f c hc
                  let fc_func := Iff.mp (power_set_prop B A (f⦅c⦆)) fc_func_set
                  let gc_func_set := val_in_B g C (A ℙow B) power_func_g c hc
                  let gc_func := Iff.mp (power_set_prop B A (g⦅c⦆)) gc_func_set

                  Iff.mpr (equal_functions_abc_A (f⦅c⦆) (g⦅c⦆) B A A fc_func gc_func) (
                    fun (b) => fun (hb : b ∈ B) =>
                      let hψcb : ψ⦅f⦆⦅c; b⦆ = ψ⦅g⦆⦅c; b⦆ :=
                        eq_subst (fun (t) => ψ⦅f⦆⦅c; b⦆ = t⦅c; b⦆) (ψ⦅f⦆) (ψ⦅g⦆) (hψ) (Eq.refl (ψ⦅f⦆⦅c; b⦆))

                      let cb_prop := Iff.mpr (cartesian_product_pair_prop C B c b) (And.intro (hc) (hb))

                      let ψf_prop : ψ⦅f⦆ = P f := And.right func_prop f hf
                      let pf_prop : P f ⦅c ; b⦆ = Q f (c , b) := And.right (P_prop f hf) (c, b) cb_prop
                      let ψf_prop₂ : ψ⦅f⦆⦅c ; b⦆ = Q f (c , b) := Eq.trans (
                        eq_subst (fun (t) => ψ⦅f⦆⦅c ; b⦆ = t⦅c ; b⦆) (ψ⦅f⦆) (P f) (ψf_prop) (Eq.refl (ψ⦅f⦆⦅c ; b⦆))
                      ) (pf_prop)

                      let ψg_prop : ψ⦅g⦆ = P g := And.right func_prop g hg
                      let pg_prop : P g ⦅c ; b⦆ = Q g (c , b) := And.right (P_prop g hg) (c, b) cb_prop
                      let ψg_prop₂ : ψ⦅g⦆⦅c ; b⦆ = Q g (c , b) := Eq.trans (
                        eq_subst (fun (t) => ψ⦅g⦆⦅c ; b⦆ = t⦅c ; b⦆) (ψ⦅g⦆) (P g) (ψg_prop) (Eq.refl (ψ⦅g⦆⦅c ; b⦆))
                      ) (pg_prop)

                      let cb_fst_prop := coordinates_fst_coor c b
                      let cb_snd_prop := coordinates_snd_coor c b

                      let Qf_prop :  Q f (c , b) = f⦅c⦆⦅b⦆ := eq_subst (fun (t) => f⦅fst_coor (c, b)⦆⦅snd_coor (c, b)⦆ = f⦅c⦆⦅t⦆) (
                        snd_coor (c, b)) (b) (cb_snd_prop) (
                        eq_subst (fun (t) => f⦅fst_coor (c, b)⦆⦅snd_coor (c, b)⦆ = f⦅t⦆⦅snd_coor (c, b)⦆) (fst_coor (c, b)) (c) (
                          cb_fst_prop) (
                          Eq.refl (f⦅fst_coor (c, b)⦆⦅snd_coor (c, b)⦆))
                      )

                      let Qg_prop :  Q g (c , b) = g⦅c⦆⦅b⦆ := eq_subst (fun (t) => g⦅fst_coor (c, b)⦆⦅snd_coor (c, b)⦆ = g⦅c⦆⦅t⦆) (
                        snd_coor (c, b)) (b) (cb_snd_prop) (
                        eq_subst (fun (t) => g⦅fst_coor (c, b)⦆⦅snd_coor (c, b)⦆ = g⦅t⦆⦅snd_coor (c, b)⦆) (fst_coor (c, b)) (c) (
                          cb_fst_prop) (
                          Eq.refl (g⦅fst_coor (c, b)⦆⦅snd_coor (c, b)⦆))
                      )

                      let f_res := Eq.trans (ψf_prop₂) (Qf_prop)
                      let g_res := Eq.trans (ψg_prop₂) (Qg_prop)

                      Eq.trans (Eq.symm (f_res)) (Eq.trans (hψcb) (g_res))
                  )
              )


        ))


      ) (

        And.right (Iff.mpr (func_surj_prop X Y ψ (And.left func_prop)) (

          fun (g) =>
            fun (hg : g ∈ Y) =>


            let Q₁ := fun (c) => fun (b) => g⦅c ; b⦆
            let P₁ := fun (c) => lam_fun B A (Q₁ c)
            let φ := lam_fun C (A ℙow B) P₁


            let g_func := Iff.mp (power_set_prop (C × B) A g) hg


            let Q₁_prop : ∀ c ∈ C; ∀ b ∈ B; g⦅c ; b⦆ ∈ A := fun (c) =>
              fun (hc : c ∈ C) =>
                fun (b) =>
                  fun (hb : b ∈ B) =>
                    let g_func := Iff.mp (power_set_prop (C × B) A g) hg
                    let cb_prop := Iff.mpr (cartesian_product_pair_prop C B c b) (And.intro (hc) (hb))
                    val_in_B g (C × B) A g_func (c, b) cb_prop

            let P₁_prop := fun (c) => fun (hc : c ∈ C) =>
              let u := And.left (lam_then_fun_prop (Q₁ c) B A (Q₁_prop c hc))
              Iff.mpr (power_set_prop B A (lam_fun B A (Q₁ c))) u


            let func_prop_φ := lam_then_fun_prop (P₁) (C) (A ℙow B) (P₁_prop)

            let func_prop_set := Iff.mpr (power_set_prop (C) (A ℙow B) φ) (And.left func_prop_φ)


            Exists.intro φ (And.intro (func_prop_set) (



              Iff.mpr (equal_functions_abc_A g (ψ⦅φ⦆) (C × B) A A g_func (
                let func_psi_phi := val_in_B ψ X Y (And.left func_prop) (φ) func_prop_set
                Iff.mp (power_set_prop (C × B) A (ψ⦅φ⦆)) (func_psi_phi)
              )) (

                fun (pr) =>
                  fun (hpr : pr ∈ (C × B)) =>

                    let ψφfir : ψ⦅φ⦆ = P φ := And.right func_prop φ func_prop_set
                    let ψφsec : P φ ⦅pr⦆ = φ⦅fst_coor pr⦆⦅snd_coor pr⦆ := And.right (P_prop φ func_prop_set) pr hpr
                    let ψφthir := Eq.trans (
                      eq_subst (fun (t) => ψ⦅φ⦆⦅pr⦆ = t⦅pr⦆) (ψ⦅φ⦆) (P φ) (ψφfir) (Eq.refl (ψ⦅φ⦆⦅pr⦆))

                    ) (ψφsec)

                    Eq.symm (Eq.trans (ψφthir) (

                      let fst_coor_pr := fst_coor_set C B pr hpr
                      let snd_coor_pr := snd_coor_set C B pr hpr

                      let u : (P₁ (fst_coor pr))⦅snd_coor pr⦆ = g⦅fst_coor pr ; snd_coor pr⦆
                       := And.right (lam_then_fun_prop (Q₁ (fst_coor pr)) B A (Q₁_prop (fst_coor pr) (fst_coor_pr))) (snd_coor pr
                      ) (snd_coor_pr)

                      let v : φ⦅fst_coor pr⦆ = (P₁ (fst_coor pr)) := And.right (func_prop_φ) (fst_coor pr) (fst_coor_pr)
                      let v₂ := eq_subst (fun (t) => φ⦅fst_coor pr⦆⦅snd_coor pr⦆ = t⦅snd_coor pr⦆) (φ⦅fst_coor pr⦆) ((P₁ (fst_coor pr))) (
                        v
                      ) (Eq.refl (φ⦅fst_coor pr⦆⦅snd_coor pr⦆))

                      let alm_res := Eq.trans v₂ u

                      eq_subst (fun (t) => φ⦅fst_coor pr⦆⦅snd_coor pr⦆ = g⦅t⦆) ((fst_coor pr, snd_coor pr)) (pr) (
                        Eq.symm (fst_snd_then_unique C B pr (hpr))
                      ) (alm_res)

                    ))
              )
            ))
        ))
      )))


    ) (second)


theorem equinum_boolean_congr : ∀ A B, (A ~ B) → (𝒫 A ~ 𝒫 B) :=
  fun (A B) =>
    fun (hAB : (A ~ B)) =>
      Exists.elim hAB
      (
        fun (f) =>
          fun (hf : f Bij A To B) =>

            let P := fun (X) => { z ∈ B | ∃ x ∈ X; z = f⦅x⦆ }

            let φ := lam_fun (𝒫 A) (𝒫 B) P


            let P_prop := fun (X) =>
              let Q := fun (s) => ∃ x ∈ X; s = f⦅x⦆
              let u : P X ⊆ B := specification_set_subset Q B
              Iff.mpr (boolean_set_is_boolean B (P X)) u

            let func_prop := lam_then_fun_prop P (𝒫 A) (𝒫 B) (fun (x) => fun (_ :x ∈ 𝒫 A) => P_prop x)

            Exists.intro φ (And.intro (And.left func_prop) (

              And.intro (

                And.right (Iff.mpr (func_inj_prop (𝒫 A) (𝒫 B) φ (And.left func_prop)) (
                  fun (X) =>
                    fun (hX : X ∈ 𝒫 A) =>
                      fun (Y) =>
                        fun (hY : Y ∈ 𝒫 A) =>
                          fun (hφ : φ⦅X⦆ = φ⦅Y⦆) =>
                            let φx : φ⦅X⦆ = P X  := And.right func_prop X hX
                            let φy : φ⦅Y⦆ = P Y  := And.right func_prop Y hY
                            let pxy := Eq.trans (Eq.symm φx) (Eq.trans (hφ) (φy))

                            extensionality X Y (
                              fun (x) =>
                              let proofside := fun (T) => fun (K) => fun (hT : T ∈ 𝒫 A) =>
                               fun (hK : K ∈ 𝒫 A) => fun (ptk : P T = P K) =>
                                  fun (hx : x ∈ T) =>
                                    let xA := Iff.mp (boolean_set_is_boolean A T) hT x hx
                                    let u := val_in_B f A B (And.left hf) x xA
                                    let Q := fun (M) => fun (s) => ∃ t ∈ M; s = f⦅t⦆
                                    let v : f⦅x⦆ ∈ P T := Iff.mpr (spec_is_spec (Q T) B (f⦅x⦆)) (
                                      And.intro (u) (Exists.intro x (And.intro (hx) (Eq.refl (f⦅x⦆))))
                                    )

                                    let v₂ : f⦅x⦆ ∈ P K := eq_subst (fun (t) => f⦅x⦆ ∈ t) (P T) (P K) (ptk) (v)

                                    let v₃ := And.right (Iff.mp (spec_is_spec (Q K) B (f⦅x⦆)) v₂)

                                    Exists.elim v₃ (
                                      fun (y) =>
                                        fun (hy : y ∈ K ∧ f⦅x⦆ = f⦅y⦆) =>
                                          let yA := Iff.mp (boolean_set_is_boolean A K) hK y (And.left hy)
                                          eq_subst (fun (t) => t ∈ K) (y) (x) (Eq.symm (
                                            Iff.mp (func_inj_prop A B f (And.left hf)) (bij_is_inj A B f hf) x xA y yA (And.right hy)

                                          )) (And.left hy)
                                    )
                              Iff.intro
                              (
                                proofside X Y hX hY pxy
                              )
                              (
                                proofside Y X hY hX (Eq.symm (pxy))
                              )
                          )
                ))

              ) (
                  And.right (Iff.mpr (func_surj_prop (𝒫 A) (𝒫 B) φ (And.left func_prop)) (
                    fun (Y) =>
                      fun (hY : Y ∈ (𝒫 B)) =>
                        let hYB := Iff.mp (boolean_set_is_boolean B Y) hY
                        let X := {x ∈ A | ∃ y ∈ Y; y = f⦅x⦆ }

                        Exists.intro X (
                          let Q := fun (x) => ∃ y ∈ Y; y = f⦅x⦆
                            let XA : X ⊆ A := specification_set_subset Q A
                            let XA₂ := Iff.mpr (boolean_set_is_boolean A X) (XA)
                          let R := fun (M) => fun (s) => ∃ t ∈ M; s = f⦅t⦆
                          And.intro (
                            XA₂

                          ) (

                            extensionality Y (φ⦅X⦆) (
                              fun (x) =>
                                Iff.intro
                                (
                                  fun (hx : x ∈ Y) =>
                                    let φx : φ⦅X⦆ = P X  := And.right func_prop X XA₂
                                    eq_subst (fun (t) => x ∈ t) (P X) (φ⦅X⦆) (Eq.symm φx) (
                                      Iff.mpr (spec_is_spec (R X) B x) (
                                        And.intro (hYB x hx) (
                                          let surjf := And.right (And.right hf)
                                          let surjfcr := Iff.mp (func_surj_prop A B f (And.left hf)) (
                                            And.intro (And.left hf) (surjf)
                                          ) x (hYB x hx)
                                          Exists.elim surjfcr (
                                            fun (y) =>
                                              fun (hy : y ∈ A ∧ x = f⦅y⦆) =>
                                                Exists.intro y (
                                                  And.intro (
                                                    Iff.mpr (spec_is_spec Q A y) (
                                                      And.intro (And.left hy) (Exists.intro x (And.intro (hx) (And.right hy)))
                                                    )
                                                  ) (And.right hy)
                                                )
                                          )
                                        )
                                      )
                                    )
                                )
                                (
                                  fun (hx : x ∈ φ⦅X⦆) =>
                                    let φx : φ⦅X⦆ = P X  := And.right func_prop X XA₂
                                    let eqs := eq_subst (fun (t) => x ∈ t) (φ⦅X⦆) (P X) (φx) (hx)
                                    let R := fun (s) => ∃ t ∈ X; s = f⦅t⦆
                                    let xpx := Iff.mp (spec_is_spec R B x) (eqs)
                                    Exists.elim (And.right xpx)
                                    (
                                      fun (y) =>
                                        fun (hy : y ∈ X ∧ x = f⦅y⦆) =>
                                          let ypx := Iff.mp (spec_is_spec Q A y) (And.left hy)
                                          Exists.elim (And.right ypx) (
                                            fun (t) =>
                                              fun (ht : t ∈ Y ∧ t = f⦅y⦆) =>
                                                eq_subst (fun (r) => r ∈ Y) t x (
                                                  Eq.trans (And.right ht) (Eq.symm (And.right hy))
                                                ) (And.left ht)
                                          )
                                    )
                                )
                            )
                          )
                        )

                  ))
              )

            ))
      )



theorem equinum_power_boolean : ∀ A, ({∅, {∅}} ℙow A) ~ 𝒫 A :=
  let X := ∅
  let Y := {∅}
  let YnX : Y ≠ X := fun (YX : Y = X) =>
    empty_set_is_empty ∅ (
      eq_subst (fun (t) => ∅ ∈ t) (Y) (∅) (YX) (elem_in_singl ∅)
    )
  let XnY : X ≠ Y := fun (XY : X = Y) => YnX (Eq.symm XY)

  fun (A) =>

    let S := ({∅, {∅}} ℙow A)
    let T := 𝒫 A


    let P := fun (f) => { z ∈ A | f⦅z⦆ = Y}
    let φ := lam_fun S T P

    let P_prop := fun (f) =>
      let first := specification_set_subset (fun (t) => f⦅t⦆ = Y) A
      Iff.mpr (boolean_set_is_boolean A (P f)) first

    let func_prop := lam_then_fun_prop P S T (fun (x) => fun (_ : x ∈ S) => P_prop x)


    Exists.intro φ (And.intro (And.left func_prop) (
      And.intro (
        And.right (Iff.mpr (func_inj_prop S T φ (And.left func_prop)) (
          fun (f) =>
            fun (hf : f ∈ S) =>
              fun (g) =>
                fun (hg : g ∈ S) =>
                  fun (hfg : φ⦅f⦆ = φ⦅g⦆) =>
                    let f_func := Iff.mp (power_set_prop A {X, Y} f) hf
                    let g_func := Iff.mp (power_set_prop A {X, Y} g) hg
                    let φfP : φ⦅f⦆ = P f := And.right func_prop f hf
                    let ψgP : φ⦅g⦆ = P g := And.right func_prop g hg
                    let ψfg : P f = P g := Eq.trans (Eq.symm φfP) (Eq.trans (hfg) (ψgP))


                    Iff.mpr (equal_functions_abc_A f g A {X, Y} {X, Y} (f_func) (g_func)) (
                      fun (x) =>
                        fun (hx : x ∈ A) =>
                          let u : f⦅x⦆ ∈ {X, Y} := val_in_B f A {X, Y} f_func x hx
                          let v := Iff.mp (unordered_pair_set_is_unordered_pair X Y (f⦅x⦆)) u

                          let proof_side := fun (f₁) => fun (f₂) =>
                            fun (hf₁ : f₁⦅x⦆ = Y) =>
                              fun (ψf₁f₂ : P f₁ = P f₂) =>
                                let Q := fun (k) => fun (r) => k⦅r⦆ = Y
                                let spec_pr : x ∈ P f₁ := Iff.mpr (spec_is_spec (Q f₁) A x) (
                                  And.intro (hx) (hf₁)
                                )
                                let spec_pr₂ : x ∈ P f₂ := eq_subst (fun (t) => x ∈ t) (P f₁) (P f₂) (ψf₁f₂) (spec_pr)
                                let spec_pr₃ := And.right (Iff.mp (spec_is_spec (Q f₂) A x) spec_pr₂)
                                Eq.trans (hf₁) (Eq.symm (spec_pr₃))

                          Or.elim (v)
                          (
                            fun (hX : f⦅x⦆ = X) =>
                              let second : g⦅x⦆ = X :=
                                byContradiction (
                                  fun (gxnX : g⦅x⦆ ≠ X) =>
                                    let m := val_in_B g A {X, Y} g_func  x hx
                                    let n := Iff.mp (unordered_pair_set_is_unordered_pair X Y (g⦅x⦆)) m
                                    Or.elim (n)
                                    (
                                      fun (gxX : g⦅x⦆ = X) =>
                                        gxnX gxX
                                    )
                                    (
                                      fun (gxY : g⦅x⦆ = Y) =>
                                        XnY (Eq.trans (Eq.symm hX) (Eq.trans (Eq.symm (
                                          proof_side g f gxY (Eq.symm (ψfg))
                                        )) (gxY)))
                                    )

                                )

                              Eq.trans hX (Eq.symm (second))


                          )
                          (
                            fun (hY : f⦅x⦆ = Y) =>
                              proof_side f g hY ψfg
                          )
                    )

        ))

      ) (
        And.right (Iff.mpr (func_surj_prop S T φ (And.left func_prop)) (

          fun (M) =>
            fun (hM : M ∈ 𝒫 A) =>

              let MA := Iff.mp (boolean_set_is_boolean A M) hM

              let Q := fun (a) => a ∈ M

              let Q₁ := fun (_ : Set) => Y
              let Q₂ := fun (_ : Set) => X

              let f := lam_cond_fun A {X, Y} Q Q₁ Q₂

              let Q₁_prop : ∀ a, Q a → ((Q₁ a) ∈ {X, Y}) := fun (a) => fun (_ : a ∈ M) =>
                right_unordered_pair X Y

              let Q₂_prop : ∀ a, ¬ Q a → ((Q₂ a) ∈ {X, Y}) := fun (a) => fun (_ : a ∉ M) =>
                left_unordered_pair X Y

              let func_prop_f := lam_cond_fun_prop A {X, Y} Q Q₁ Q₂ (
                fun (a) => fun (_ : a ∈ A) =>
                  And.intro (Q₁_prop a) (Q₂_prop a)
              )

              let func_prop_set : f ∈ S := Iff.mpr (power_set_prop A {X, Y} f) (And.left func_prop_f)

              Exists.intro f (And.intro (func_prop_set) (
                let φfP : φ⦅f⦆ = P f := And.right func_prop f (func_prop_set)

                eq_subst (fun (t) => M = t) (P f) (φ⦅f⦆) (Eq.symm φfP) (
                  extensionality M (P f) (
                    fun (s) =>
                      Iff.intro
                      (
                        fun (hs : s ∈ M) =>
                          let f_pr : f⦅s⦆ = Y := And.left (And.right func_prop_f s (MA s (hs)) ) hs

                          let R := fun (r) => f⦅r⦆ = Y

                          Iff.mpr (spec_is_spec R A s) (
                            And.intro (MA s hs) (f_pr)
                          )
                      )
                      (
                        fun (hs : s ∈ P f) =>
                          let R := fun (r) => f⦅r⦆ = Y
                          let pf_pr := Iff.mp (spec_is_spec R A s) hs
                          Or.elim (em (s ∈ M))
                          (
                            fun (hs : s ∈ M) =>
                              hs
                          )
                          (
                            fun (hs : s ∉ M) =>
                              let u : f⦅s⦆ = X := And.right (And.right func_prop_f s (And.left pf_pr)) hs
                              False.elim (
                                XnY (Eq.trans (Eq.symm u) (And.right pf_pr))
                              )
                          )
                      )
                  )
                )
              ))
        ))
      ))
    )









def includes (A B : Set) := ∃ f, f Inj A To B

syntax term "≾" term : term
syntax term "⋨" term : term
syntax term "⋠" term : term

macro_rules
  | `($A:term ≾ $B:term) => `(includes $A $B)
  | `($A:term ⋠ $B:term) => `(¬($A ≾ $B))
  | `($A:term ⋨ $B:term) => `(($A ≾ $B) ∧ ($A ≁ $B))

theorem incl_refl : ∀ A, A ≾ A :=
  fun (A) =>
    let h₁ := equinum_refl A
    Exists.elim h₁
    (
      fun (f) =>
        fun (hf : f Bij A To A) =>
          Exists.intro f (bij_is_inj A A f (hf))
    )



theorem incl_trans : ∀ A B C, (A ≾ B) → (B ≾ C) → (A ≾ C) :=
  fun (A B C) =>
    fun (h₁ : (A ≾ B)) =>
      fun (h₂ : (B ≾ C)) =>
        Exists.elim h₁
        (
          fun (f) =>
            fun (hf : f Inj A To B) =>
              Exists.elim h₂
              (
                fun (g) =>
                  fun (hg : g Inj B To C) =>
                    Exists.intro (g ∘ f) (
                      injection_composition f g A B C (hf) (hg)
                    )
              )
        )



theorem equinum_then_incl : ∀ A B, (A ~ B) → A ≾ B :=
  fun (A B) => fun (h₁ : A ~ B) =>
    Exists.elim h₁
    (
      fun (f) =>
        fun (hf : f Bij A To B) =>
          Exists.intro f (bij_is_inj A B f (hf))
    )

theorem subs_then_incl : ∀ A B, (A ⊆ B) → (A ≾ B) :=
  fun (A B) =>
    fun (h : A ⊆ B) =>
      Exists.intro (id_ A) (
        let u := id_is_bij A
        let v := bij_is_inj A A (id_ A) u

        And.intro (
          function_change_B (id_ A) A A B (And.left v) (h)
        ) (
          And.right v
        )
      )



theorem incl_iff_subs_equinum : ∀ A B, (A ≾ B) ↔ ∃ C, (C ⊆ B) ∧ A ~ C :=
  fun (A B) =>
    Iff.intro
    (
      fun (hAB : (A ≾ B)) =>
        Exists.elim hAB
        (
          fun (f) =>
            fun (hf : f Inj A To B) =>
              Exists.intro (f.[A]) (And.intro (
                eq_subst (fun (t) => t ⊆ B) (rng f) (f.[A]) (
                  let u := dom_function f A B (And.left hf)
                  eq_subst (fun (m) => rng f = f.[m]) (dom f) (A) (Eq.symm u) (
                    rng_is_rel_image f (And.left (prop_then_binary_relation A B f (
                      And.left (And.left (And.left hf))
                    )))
                  )
                ) (rng_partial_function f A B (And.left (And.left hf)))
              ) (equinum_image A B A f (subset_refl A) (hf)))
        )
    )
    (
      fun (hex : ∃ C, (C ⊆ B) ∧ A ~ C) =>
        Exists.elim hex
        (
          fun (C) =>
            fun (hC : C ⊆ B ∧ A ~ C) =>
              incl_trans A C B (equinum_then_incl A C (And.right hC)) (
                subs_then_incl C B (And.left hC)
              )
        )
    )


def covers (A B : Set) := ∃ f, f Surj A To B

syntax term "≿" term : term
syntax term "⋩" term : term
syntax term "⋡" term : term

macro_rules
| `($A:term ≿ $B:term) => `(covers $A $B)
| `($A:term ⋩ $B:term) => `(¬ ($A ≿ $B))
| `($A:term ⋡ $B:term) => `(($A ≿ $B) ∧ ($A ≁ $B))


theorem cov_refl : ∀ A, A ≿ A :=
  fun (A) =>
    Exists.intro (id_ A) (And.intro (And.left (id_is_bij A)) (And.right (And.right (id_is_bij A))))


theorem cov_trans : ∀ A B C, (A ≿ B) → (B ≿ C) → (A ≿ C) :=
  fun (A B C) =>
    fun (hAB : A ≿ B) =>
      fun (hBC : B ≿ C) =>
        Exists.elim hAB
        (
          fun (f) =>
            fun (hf : f Surj A To B) =>
              Exists.elim hBC
              (
                fun (g) =>
                  fun (hg : g Surj B To C) =>
                    Exists.intro (g ∘ f) (surjection_composition f g A B C (hf) (hg))
              )
        )


theorem equinum_then_cov : ∀ A B, (A ~ B) → A ≿ B :=
  fun (A B) =>
    fun (hAB : (A ~ B)) =>
      Exists.elim hAB (
        fun (f) =>
          fun (hf : f Bij A To B) =>
            Exists.intro f (bij_is_surj A B f (hf))
      )


theorem subs_then_cov : ∀ A B, (A ⊆ B) → ((B ≿ A) ∨ (A = ∅ ∧ B ≠ ∅)) :=
  fun (A B) =>
    fun (hAB : A ⊆ B) =>
      Or.elim (em (A = ∅ ∧ B ≠ ∅))
      (
        fun (hABemp : A = ∅ ∧ B ≠ ∅) =>
          Or.inr hABemp
      )
      (
        fun (hABnemp : ¬ (A = ∅ ∧ B ≠ ∅)) =>
          let u := Iff.mp (morgan_conj (A = ∅) (B ≠ ∅)) hABnemp
          Or.elim u
          (
            fun (Anemp : A ≠ ∅) =>
              let u := non_empty_uni_then_exi (fun (_) => True) A Anemp (fun (t) => fun (_ : t ∈ A) => True.intro)
              Exists.elim u (
                fun (x₀) =>
                  fun (hx₀ : x₀ ∈ A ∧ True) =>
                    Or.inl (

                      let Q := fun (x) => x ∈ A
                      let Q₀ := fun (x) => x
                      let Q₁ := fun (_) => x₀

                      let Q_prop := fun (x) => fun (_ : x ∈ B) =>
                        And.intro
                         (
                          fun (hx : x ∈ A) =>
                            hx
                         )
                         (
                          fun (_ : x ∉ A) =>
                            And.left hx₀
                         )

                      let f := lam_cond_fun B A Q Q₀ Q₁

                      let func_prop := lam_cond_fun_prop B A Q Q₀ Q₁ Q_prop


                      Exists.intro f (And.intro (And.left func_prop) (
                        And.right (Iff.mpr (func_surj_prop B A f (And.left func_prop)) (

                          fun (a) =>
                            fun (ha : a ∈ A) =>
                              Exists.intro a (And.intro (hAB a (ha)) (
                                Eq.symm (And.left (And.right func_prop a (hAB a ha)) ha)
                              ))
                        ))
                      ))
                    )
              )
          )
          (
            fun (Bnnemp : ¬ (B ≠ ∅)) =>
              Or.inl (
                let v := byContradiction Bnnemp
                let r := extensionality A (∅) (fun (x) => Iff.intro (
                  fun (hx : x ∈ A) =>
                    eq_subst (fun (t) => x ∈ t) (B) (∅) (v) (hAB x (hx))
                ) (empty_set_is_subset_any A x))

                Exists.intro ∅ (And.intro (
                  And.intro (
                    And.intro (empty_set_is_subset_any (B × A)) (
                      fun (x y z) =>
                        fun (hxy : (x . ∅ . y)) =>
                          fun (_ : (x . ∅ . z)) =>
                            False.elim (empty_set_is_empty (x, y) (hxy))
                    )
                  )
                  (
                    fun (b) =>
                      fun (hb : b ∈ B) =>
                        False.elim (empty_set_is_empty b (eq_subst (fun (t) => b ∈ t) (B) (∅) (v) (hb)))
                  )
                ) (
                  fun (a) =>
                    fun (ha : a ∈ A) =>
                      False.elim (empty_set_is_empty a (eq_subst (fun (t) => a ∈ t) (A) (∅) (r) (ha)))
                ))
              )
          )

      )


theorem incl_cov_prop_AC : choice_ax → (∀ A B, (A ≾ B) ↔ ((B ≿ A) ∨ (A = ∅ ∧ B ≠ ∅))) :=
  fun (ax : choice_ax) =>
    fun (A B) =>
      Iff.intro
      (
        fun (hAB : (A ≾ B)) =>
          Exists.elim hAB (
            fun (f) =>
              fun (hf : f Inj A To B) =>
                Or.elim (em ((A = ∅ ∧ B ≠ ∅)))
                (
                  fun (habemp : (A = ∅ ∧ B ≠ ∅)) =>
                    Or.inr habemp
                )
                (
                  fun (hanbemp : ¬ (A = ∅ ∧ B ≠ ∅)) =>
                    let u := Iff.mp (morgan_conj (A = ∅) (B ≠ ∅)) hanbemp
                    let v := Iff.mpr (leftrev_criterion f A B) (
                      And.intro (hf) (
                        Or.elim u
                        (Or.inl)
                        (
                          fun (hnnb : ¬ B ≠ ∅) =>
                            Or.inr (byContradiction hnnb)
                        )

                      )
                    )
                    Exists.elim (And.right v) (
                      fun (g) =>
                        fun (hg : (g Fun B To A) ∧ g ∘ f = id_ A) =>
                          Or.inl (
                            Exists.intro g (
                              Iff.mp (Iff.mp (rightrev_criterion_AC_eq) (ax) g B A) (
                                And.intro (And.left hg) (
                                  Exists.intro f (And.intro (And.left hf) (And.right hg))
                                )
                              )
                            )
                          )
                    )
                )
          )
      )
      (
        fun (hAB : ((B ≿ A) ∨ (A = ∅ ∧ B ≠ ∅))) =>
          Or.elim hAB
          (
            fun (hBA : (B ≿ A)) =>
              Exists.elim hBA (
                fun (g) =>
                  fun (hg : g Surj B To A) =>
                    let u := Iff.mpr (Iff.mp (rightrev_criterion_AC_eq) ax g B A) hg
                    Exists.elim (And.right u) (
                      fun (f) =>
                        fun (hf : (f Fun A To B) ∧ g ∘ f = id_ A) =>
                          let v := And.left (Iff.mp (leftrev_criterion f A B) (

                            And.intro (And.left hf) (Exists.intro g (And.intro (And.left hg) (And.right hf) ))
                          ))
                          Exists.intro f (v)
                    )

              )


          )
          (
            fun (hABemp : (A = ∅ ∧ B ≠ ∅)) =>
              subs_then_incl A B (
                eq_subst (fun (t) => t ⊆ B) (∅) (A) (Eq.symm (And.left hABemp)) (empty_set_is_subset_any B)
              )
          )
      )


theorem cov_iff_subs_equinum_AC : choice_ax → ∀ A B, ((A ≿ B) ∨ (B = ∅ ∧ A ≠ ∅)) ↔ (∃ C, (C ⊆ A) ∧ B ~ C) :=
  fun (ax : choice_ax) =>
    fun (A B) =>
      Iff.intro
      (
        fun (hf₁ : ((A ≿ B) ∨ (B = ∅ ∧ A ≠ ∅))) =>
          Or.elim hf₁
          (
            fun (hAB : (A ≿ B)) =>

              let u := Iff.mpr (incl_cov_prop_AC ax B A) (
                Or.inl (hAB)
              )
              Iff.mp (incl_iff_subs_equinum B A) u
          )
          (
            fun (hABemp : (B = ∅ ∧ A ≠ ∅)) =>
              Exists.intro ∅ (And.intro (empty_set_is_subset_any A) (
                eq_subst (fun (t) => t ~ ∅) ∅ B (Eq.symm (And.left hABemp)) (equinum_refl ∅)
              ))
          )

      )
      (
        fun (hAB : (∃ C, (C ⊆ A) ∧ B ~ C)) =>
          let u := Iff.mpr (incl_iff_subs_equinum B A) (hAB)
          Iff.mp (incl_cov_prop_AC ax B A) u
      )



theorem cantor_lemma : ∀ A, A ≾ 𝒫 A :=
  fun (A) =>
    let P := fun (a) => {a}
    let φ := lam_fun A (𝒫 A) P

    let P_prop := fun (a) => fun (ha : a ∈ A) =>
      Iff.mpr (boolean_set_is_boolean A {a}) (
        fun (x) =>
          fun (hx : x ∈ {a}) =>
            let u := in_singl_elem a x hx
            eq_subst (fun (t) => t ∈ A) (a) (x) (Eq.symm u) (ha)
      )

    let func_prop := lam_then_fun_prop P A (𝒫 A) P_prop

    Exists.intro φ (And.intro (And.left func_prop) (
      And.right (Iff.mpr (func_inj_prop A (𝒫 A) φ (And.left func_prop)) (
        fun (x) =>
          fun (hx : x ∈ A) =>
            fun (y) =>
              fun (hy : y ∈ A) =>
                fun (hxy : φ⦅x⦆ = φ⦅y⦆) =>
                  let u : φ⦅x⦆ = {x} := And.right func_prop x hx
                  let v : φ⦅y⦆ = {y} := And.right func_prop y hy
                  let res : {x} = {y} := Eq.trans (Eq.symm u) (Eq.trans (hxy) v)

                  let prp : x ∈ {y} := eq_subst (fun (t) => x ∈ t) {x} {y} (res) (elem_in_singl x)
                  in_singl_elem y x (prp)
      ))
    ))



theorem cantor_theorem : ∀ A, 𝒫 A ⋠ A :=
  fun (A) =>
    fun (hinc : (𝒫 A ≾ A)) =>
      Exists.elim hinc (
        fun (f) =>
          fun (hf : f Inj (𝒫 A) To A) =>
            let P := fun (z) => ∃ S ∈ (𝒫 A); z = f⦅S⦆ ∧ f⦅S⦆ ∉ S

            let Y := {z ∈ A | P z}

            let yA : Y ⊆ A := specification_set_subset P A
            let yPA := Iff.mpr (boolean_set_is_boolean A Y) yA

            let v := Iff.mp (func_inj_prop (𝒫 A) A f (And.left hf)) hf

            Or.elim (em (f⦅Y⦆ ∈ Y))
            (
              fun (hfy : f⦅Y⦆ ∈ Y) =>
                let u := And.right (Iff.mp (spec_is_spec P (A) (f⦅Y⦆)) hfy)
                Exists.elim u (
                  fun (S) =>
                    fun (hs : S ∈ (𝒫 A) ∧ f⦅Y⦆ = f⦅S⦆ ∧ f⦅S⦆ ∉ S) =>
                      let first := v Y yPA S (And.left hs) (And.left (And.right hs))
                      eq_subst (fun (t) => f⦅t⦆ ∉ t) S Y (Eq.symm first) (And.right (And.right hs)) (hfy)
                )
            )
            (
              fun (hfy : f⦅Y⦆ ∉ Y) =>
                let u : P (f⦅Y⦆)  := Exists.intro (Y) (And.intro yPA (And.intro (Eq.refl (f⦅Y⦆)) (hfy)))
                let v := Iff.mpr (spec_is_spec P A (f⦅Y⦆)) (
                  And.intro (
                    val_in_B f (𝒫 A) A (And.left hf) Y (yPA)
                  ) (u)
                )

                hfy (v)
            )
      )


theorem strict_inc_infinite_chain : ∀ A, ∃ B, A ⋨ B :=
  fun (A) =>
    Exists.intro (𝒫 A) (And.intro (cantor_lemma A) (
      fun (s : (A ~ 𝒫 A)) =>
        let s₁ := equinum_symm A (𝒫 A) s
        cantor_theorem A (equinum_then_incl (𝒫 A) A (s₁))
    ))



theorem schroeder_bernstein_theorem : ∀ A B, (A ~ B) ↔ ((A ≾ B) ∧ (B ≾ A)) :=
  fun (A B) =>
    Iff.intro
    (
      fun (hAB : (A ~ B)) =>
        And.intro (equinum_then_incl A B hAB) (
          equinum_then_incl B A (equinum_symm A B (hAB))
        )
    )
    (
      fun (hAB : ((A ≾ B) ∧ (B ≾ A))) =>

        Exists.elim (And.left hAB) (
          fun (f) =>
            fun (hf : f Inj A To B) =>
              Exists.elim (And.right hAB) (
                fun (g) =>
                  fun (hg : g Inj B To A) =>

                    let g_bin := And.left (prop_then_binary_relation B A g (And.left (And.left (And.left hg))))
                    let f_bin := And.left (prop_then_binary_relation A B f (And.left (And.left (And.left hf))))

                    let P := fun (X) => g.[ B \ f.[ A \ X ] ]

                    let P_prop := fun (X) =>
                      let u := part_func_img_prop g B A (And.left (And.left hg)) (B \ f.[ A \ X ])
                      Iff.mpr (boolean_set_is_boolean A (g.[ B \ f.[ A \ X ] ])) (u)

                    let F := lam_fun (𝒫 A) (𝒫 A) P

                    let func_prop_all := lam_then_fun_prop P (𝒫 A) (𝒫 A) (fun (X) => fun (_ : X ∈ 𝒫 A) =>
                      P_prop X
                    )

                    let func_prop : F Fun (𝒫 A) To (𝒫 A) := And.left func_prop_all

                    let val_prop : ∀ X ∈ (𝒫 A); F⦅X⦆ = P X := And.right func_prop_all

                    let mon : ∀ X Y ∈ 𝒫 A; (X ⊆ Y) → (F⦅X⦆ ⊆ F⦅Y⦆) := fun (X) => fun (hX : X ∈ (𝒫 A)) =>
                      fun (Y) => fun (hY : Y ∈ (𝒫 A)) =>
                          fun (hXY : X ⊆ Y) =>
                            let u₁ := neg_mon_diff X Y A hXY
                            let u₂ := monotonic_rel_image (A \ Y) (A \ X) f (f_bin) u₁
                            let u₃ := neg_mon_diff (f.[ A \ Y ]) (f.[ A \ X ]) B u₂
                            let u₄ : P X ⊆ P Y := monotonic_rel_image (B \ f.[ A \ X ]) (B \ f.[ A \ Y ]) g g_bin u₃
                            eq_subst (fun (t) => F⦅X⦆ ⊆ t) (P Y) (F⦅Y⦆) (Eq.symm (val_prop Y hY)) (
                              eq_subst (fun (t) => t ⊆ P Y) (P X) (F⦅X⦆) (Eq.symm (val_prop X hX)) (u₄)
                            )

                    let exi_Z := monotonic_operator_fix_point A F (func_prop) (mon)

                    Exists.elim exi_Z (
                      fun (Z) =>
                        fun (hZ : Z ∈ 𝒫 A ∧ F⦅Z⦆ = Z) =>
                          let a₀ := Iff.mp (boolean_set_is_boolean A Z) (And.left hZ)
                          let a₁ := val_prop Z (And.left hZ)
                          let a₂ := Eq.trans (Eq.symm (And.right hZ)) (a₁)
                          let a₃ := eq_subst (fun (t) => Z ~ t) (Z) (g.[ B \ f.[ A \ Z ] ] ) (a₂) (equinum_refl Z)
                          let s := difference_subset_prop B (f.[ A \ Z ])
                          let s₂ := difference_subset_prop A Z
                          let a₄ := equinum_image B A (B \ f.[ A \ Z ]) g (s) hg
                          let a₅ : Z ~ (B \ f.[ A \ Z ]) := equinum_trans Z (g.[ B \ f.[ A \ Z ] ]) (B \ f.[ A \ Z ]) (a₃) (
                            equinum_symm (B \ f.[ A \ Z ]) (g.[ B \ f.[ A \ Z ] ]) (a₄)
                          )
                          let a₆ : (A \ Z) ~ (f.[ A \ Z ]) := equinum_image A B (A \ Z) f (s₂) hf

                          equinum_partition A B Z (B \ f.[ A \ Z ]) a₀ s (a₅) (
                            eq_subst (fun (t) => (A \ Z) ~ t) (f.[ A \ Z ]) (B \ (B \ (f.[ A \ Z ]))) (
                              Eq.symm (double_compl B (f.[ A \ Z ]) (
                                part_func_img_prop f A B (And.left (And.left hf)) (A \ Z)
                              ))
                            ) (a₆)
                          )
                    )



              )
        )
    )


theorem schroeder_bernstein_inc_cov_AC : choice_ax → (∀ A B, (A ~ B) ↔ ((A ≾ B) ∧ (A ≿ B))) :=
  fun (ax : choice_ax) =>
    fun (A B) =>
      Iff.intro
      (
        fun (hAB : (A ~ B)) =>
          And.intro (equinum_then_incl A B hAB) (equinum_then_cov A B hAB)
      )
      (
        fun (hAB : (A ≾ B) ∧ (A ≿ B)) =>
          Iff.mpr (schroeder_bernstein_theorem A B) (
            And.intro (And.left hAB) (
              Iff.mpr (incl_cov_prop_AC ax B A) (
                Or.inl (And.right (hAB))
              )
            )
          )
      )
