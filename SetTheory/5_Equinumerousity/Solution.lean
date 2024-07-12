import «Header»

-- set of all functions
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

    let g₁ := specification_set_is_specification (fun (t) => ∃ a ∈ X; (a . f . t)) (rng f)

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
                let h₂ := And.right (Iff.mp (specification_set_is_specification (fun (p) => p Fun C To A) (𝒫 (C × A)) f) hf)
                let h₃ := And.left (function_composition f ϕ C A B h₂ (And.left hϕ))
                Iff.mpr (specification_set_is_specification (fun (p) => p Fun C To B) (𝒫 (C × B)) (ϕ ∘ f)) (And.intro (
                  Iff.mpr (boolean_set_is_boolean (C × B) (ϕ ∘ f)) (And.left (And.left h₃))) (h₃))
            )

            And.intro (And.left func_prop) (And.intro (
              let h₂ := Iff.mpr (func_inj_prop (A ℙow C) (B ℙow C) ψ (And.left func_prop)) (
                fun (f) => fun (h₃ : f ∈ A ℙow C) =>
                  fun (g) => fun (h₄ : g ∈ A ℙow C) =>
                    fun (h₅ : ψ⦅f⦆ = ψ⦅g⦆) =>
                      let f_is_func := And.right (Iff.mp (specification_set_is_specification (fun (p) => p Fun C To A) (𝒫 (C × A)) f) h₃)
                      let g_is_func := And.right (Iff.mp (specification_set_is_specification (fun (p) => p Fun C To A) (𝒫 (C × A)) g) h₄)
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
                  let h₅ := And.right (Iff.mp (specification_set_is_specification (fun (p) => p Fun C To B) (𝒫 (C × B)) g) h₃)
                  let h₆ := function_composition g (ϕ⁻¹) C B A (h₅) (h₄)
                  let h₇ := Iff.mpr (specification_set_is_specification (fun (p) => p Fun C To A) (𝒫 (C × A)) (ϕ⁻¹ ∘ g)) (
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

    let pred_ψ := fun (f) =>
        let left_func := lam_fun C A (
          fun (c) => fst_coor f⦅c⦆
        )
        let right_func := lam_fun C B (
          fun (c) => snd_coor f⦅c⦆
        )
        (left_func, right_func)


    let ψ := lam_fun ((A × B) ℙow C) ((A ℙow C) × (B ℙow C)) (
      pred_ψ
    )

    let func_prop := lam_then_fun_prop pred_ψ ((A × B) ℙow C) ((A ℙow C) × (B ℙow C)) (
      fun (f) => fun (h₁ : f ∈ ((A × B) ℙow C)) =>
        Iff.mpr (cartesian_product_pair_prop (A ℙow C) (B ℙow C) (lam_fun C A (
          fun (c) => fst_coor f⦅c⦆
        )) (lam_fun C B (
          fun (c) => snd_coor f⦅c⦆
        ))) (And.intro (sorry) (sorry))
    )

    Exists.intro ψ (And.intro (And.left func_prop) (And.intro (sorry) (sorry)))


theorem equinum_power_cartesian : ∀ A B C, ((A ℙow B) ℙow C) ~ (A ℙow (B × C)) :=
  sorry


theorem equinum_boolean_congr : ∀ A B, (A ~ B) → (𝒫 A ~ 𝒫 B) :=
  sorry


theorem equinum_power_boolean : ∀ A, ({∅, {∅}} ℙow A) ~ 𝒫 A :=
  sorry


def includes (A B : Set) := ∃ f, f Inj A To B

syntax term "≾" term : term
syntax term "⋦" term : term
syntax term "≴" term : term

macro_rules
  | `($A:term ≾ $B:term) => `(includes $A $B)
  | `($A:term ≴ $B:term) => `(¬($A ≾ $B))
  | `($A:term ⋦ $B:term) => `(($A ≾ $B) ∧ ($A ≁ $B))

theorem incl_refl : ∀ A, A ≾ A :=
  fun (A) =>
    let h₁ := equinum_refl A
    Exists.elim h₁
    (
      fun (f) =>
        fun (hf : f Bij A To A) =>
          Exists.intro f (bij_is_inj A A f (hf))
    )



theorem incl_trans : ∀ A B, (A ≾ B) → (B ≾ C) → (A ≾ C) :=
  fun (A B) =>
    fun (h₁ : (A ≾ B)) =>
      fun (h₂ : (B ≾ C)) =>
        sorry



theorem equinum_then_incl : ∀ A B, (A ~ B) → A ≾ B :=
  fun (A B) => fun (h₁ : A ~ B) =>
    Exists.elim h₁
    (
      fun (f) =>
        fun (hf : f Bij A To B) =>
          Exists.intro f (bij_is_inj A B f (hf))
    )

theorem subs_then_incl : ∀ A B, (A ⊆ B) → (A ≾ B) := sorry

theorem incl_iff_subs_equinum : ∀ A B, (A ≾ B) ↔ ∃ C, (C ⊆ B) ∧ A ~ C := sorry

theorem cantor_lemma : ∀ A, A ≾ 𝒫 A := sorry

theorem cantor_theorem : ∀ A, 𝒫 A ≴ A := sorry

theorem strict_inc_infinite_chain : ∀ A, ∃ B, A ⋦ B :=
  fun (A) =>
    Exists.intro (𝒫 A) (And.intro (cantor_lemma A) (
      fun (s : (A ~ 𝒫 A)) =>
        let s₁ := equinum_symm A (𝒫 A) s
        cantor_theorem A (equinum_then_incl (𝒫 A) A (s₁))
    ))

theorem schroeder_bernstein_theorem : ∀ A B, (A ≾ B) → (B ≾ A) → (A ~ B) := sorry
