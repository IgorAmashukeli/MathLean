import «Header»


theorem Russel_paradox : ¬ ∃ A, ∀ x, (x ∈ A ↔ x ∉ x) :=
  fun (h : ∃ A, ∀ x, (x ∈ A ↔ x ∉ x)) =>
    Exists.elim h
    (
      fun (Russel) =>
        fun (hw : ∀ x, (x ∈ Russel ↔ x ∉ x)) =>
          (negation_not_equiv (Russel ∈ Russel)) (hw Russel)
    )

def comprehension_axiom := ∀ P : Set → Prop, ∃ A, ∀ x, (x ∈ A ↔ P x)
theorem comprehension_axiom_is_wrong : ¬(comprehension_axiom) :=
  fun (hcomp) =>
    let badP := fun (x) => x ∉ x
    Russel_paradox (
      hcomp badP
    )




theorem subset_refl : ∀ A, A ⊆ A :=
  fun (A : Set) => fun x => fun (h : x ∈ A) => h

theorem subset_trans : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C :=
  fun (A B C : Set) => fun (h : A ⊆ B) => fun (g : B ⊆ C) =>
    fun x => fun (h₁ : x ∈ A) => (g x) (h x h₁)




theorem empty_subset_any : ∀ A B, empty A → A ⊆ B :=
  fun (A B : Set) => fun (h : empty A) => fun x => fun (g : x ∈ A) =>
    (False.elim : False → x ∈ B) (h x g)



theorem subs_subs_eq : ∀ A B, A ⊆ B ∧ B ⊆ A ↔ A = B :=
  fun (A B : Set) =>
    Iff.intro
    (
      fun (h : A ⊆ B ∧ B ⊆ A) =>
        extensionality A B (fun x =>
          Iff.intro
          (
            fun (g : x ∈ A) => (And.left h) x g
          )
          (
            fun (g : x ∈ B) => (And.right h) x g
          )
        )
    )
    (
      fun (h : A = B) =>
        And.intro
        (
          fun x =>
            fun (g : x ∈ A) =>
              Eq.subst h g
        )
        (
          fun x =>
            fun (g : x ∈ B) =>
              -- Eq.substr was proved in the previous problem
              Eq.substr h g
        )
    )


theorem equality_then_subset : ∀ A B, A = B → A ⊆ B :=
  fun (A B) => fun (h : A = B) =>
    eq_subst (fun (u) => A ⊆ u) A B (h) (subset_refl A)


theorem exists_empty : (∃ x, empty x) :=
  Exists.elim infinity
  (
    fun (inf : Set) =>
      fun (h_inf : (∃ b, empty b ∧ b ∈ inf) ∧ (∀ x ∈ inf; ∀ y, is_successor x y → y ∈ inf)) =>
        Exists.elim (And.left h_inf)
        (
          fun (empt : Set) =>
            fun (h_empt : empty empt ∧ empt ∈ inf) =>
              Exists.intro empt (And.left h_empt)
        )
  )


theorem exists_unique_empty : (∃! x, empty x) :=

  Exists.elim exists_empty
  (
    fun (empt : Set) =>
      fun (h_empt : empty empt) =>
        Exists.intro empt (And.intro (h_empt) (
          fun (y : Set) => fun (h_y : empty y) =>
            Iff.mp (subs_subs_eq empt y)
            (And.intro
            (empty_subset_any empt y h_empt)
            (empty_subset_any y empt h_y))

        ))
  )



noncomputable def empty_set := set_intro empty exists_unique_empty

notation (priority := high) "∅" => empty_set

theorem empty_set_is_empty : empty ∅ := And.left (set_intro_prop empty exists_unique_empty)

theorem empty_set_subset_any : ∀ A, ∅ ⊆ A :=
  fun (_ : Set) => fun (x : Set) => fun (h : x ∈ ∅) => False.elim ((empty_set_is_empty x) h)


theorem unique_boolean : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ⊆ A)) :=
  fun (A : Set) =>
    Exists.elim (boolean A)
    (
      fun (w : Set) =>
        fun (hw : ∀ x, (x ∈ w ↔ x ⊆ A)) =>
          Exists.intro w (And.intro hw (fun (Y : Set) =>
            fun (hy : ∀ x, (x ∈ Y ↔ x ⊆ A)) =>
              extensionality w Y (fun (x) => iff_trans_symm (x ∈ w) (x ⊆ A) (x ∈ Y) (hw x) (hy x))
          ))
    )


theorem non_empty_uni_then_exi (P : Set → Prop) : ∀ A, (A ≠ ∅) → (∀ x ∈ A; P x) → ∃ x ∈ A; P x :=
  fun (A) => fun (h : A ≠ ∅) =>
    fun (g : ∀ x ∈ A; P x) =>
      Classical.byContradiction
      fun (s : ¬∃ x ∈ A; P x) =>
        let first := Iff.mpr (morgan_uni Set (fun (x) => x ∈ A ∧ P x)) s
        let third : ∀ (x), (x ∈ A) → P x := g
        let fourth : empty A := fun (x) => fun (s : x ∈ A) => first x (And.intro (s) (third x s))

        h (
          extensionality A ∅
          fun (x) =>
          Iff.intro
          (
            fun (s : x ∈ A) => (False.elim : False → x ∈ ∅) (fourth x s)
          )
          (
            fun (s : x ∈ ∅) => (False.elim : False → x ∈ A) ((empty_set_is_empty x) s)
          )
        )


theorem set_empty_iff_empty : ∀ A, (A = ∅) ↔ (∀ x, x ∉ A) :=
  fun (A) =>
    Iff.intro
    (
      fun (hA : (A = ∅)) =>
        fun (x) =>
          fun (hx : (x ∈ A)) =>
            empty_set_is_empty x (
              eq_subst (fun (t) => x ∈ t) (A) (∅) hA hx
            )
    )
    (
      fun (hA : (∀ x, x ∉ A)) =>
        Iff.mp (subs_subs_eq A ∅) (
          And.intro (
            fun (y) =>
              fun (hy : y ∈ A) =>
                False.elim (
                  hA y hy
                )
          ) (empty_set_subset_any A)
        )
    )


theorem set_non_empty_iff_non_empty : ∀ A, (A ≠ ∅) ↔ ∃ x, x ∈ A :=
  fun (A) =>
    Iff.intro
    (
      fun (h : A ≠ ∅) =>
      Exists.elim (non_empty_uni_then_exi (fun (_) => True) A h (fun (x) => fun (_ : x ∈ A) => True.intro)) (
        fun (s) =>
          fun (hs : s ∈ A ∧ True) =>
            Exists.intro s (And.left hs)
      )
    )
    (
      fun (hA : (∃ x, x ∈ A)) =>
        fun (hAemp : (A = ∅)) =>
          Exists.elim hA (
            fun (x) =>
              fun (hx : x ∈ A) =>
                empty_set_is_empty x (
                  eq_subst (fun (t) => x ∈ t) (A) (∅) (hAemp) (hx)
                )
          )
    )





noncomputable def boolean_func_sym : Set → Set :=
  fun (A : Set) => set_intro (fun (B : Set) => ∀ x, (x ∈ B ↔ x ⊆ A)) (unique_boolean A)


notation (priority := high) "𝒫" => boolean_func_sym




theorem boolean_set_is_boolean : ∀ A, (∀ x, x ∈ 𝒫 A ↔ x ⊆ A) :=
  fun (A : Set) => And.left (set_intro_prop (fun (B : Set) => ∀ x, (x ∈ B ↔ x ⊆ A)) (unique_boolean A))



theorem empty_elem_boolean : ∀ A, ∅ ∈ 𝒫 A :=
  fun (A : Set) =>
    Iff.mpr (boolean_set_is_boolean A ∅) (empty_set_subset_any A)


theorem boolean_set_not_empty : ∀ A, 𝒫 A ≠ ∅ :=
  fun (A : Set) =>
    fun (g : 𝒫 A = ∅) =>
      (Eq.substr g empty_set_is_empty : empty (𝒫 A)) ∅ (empty_elem_boolean A)


theorem unique_replacement (P : Set → Set → Prop) : ∀ A, functional_predicate A P → ∃! B, ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y) :=
    fun (A) => fun (s : functional_predicate A P) =>
      let first := replacement P A s
      Exists.elim first
      (
        fun (w) => fun (hw : ∀ (y : Set), y ∈ w ↔ ∃ x ∈ A; P x y) =>
          Exists.intro w (And.intro hw (
            fun (u) => fun (hu : ∀ (y : Set), y ∈ u ↔ ∃ x ∈ A; P x y) =>
              extensionality w u (fun (t) => iff_trans_symm (t ∈ w) (∃ x ∈ A; P x t) (t ∈ u) (hw t) (hu t))
              )
          )
      )


noncomputable def replacement_set (P : Set → Set → Prop) (A : Set) (h : functional_predicate A P) : Set :=
  set_intro (fun (B) => ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y)) (unique_replacement P A h)



syntax "RepImg" "["  term ";"  term ";" term "]"  : term



macro_rules
  | `(RepImg [ $P:term ; $A:term ; $fun_rel_proof:term ])  => `(replacement_set $P $A $fun_rel_proof)



theorem replacement_set_is_replacement (p : Set → Set → Prop) (A : Set) (h : functional_predicate A P) :
  ∀ y, (y ∈ RepImg [P; A; h]) ↔ ∃ x ∈ A; P x y :=
    And.left (set_intro_prop (fun (B) => ∀ y, y ∈ B ↔ ∃ x ∈ A; P x y) (unique_replacement P A h))




def functional_predicate_picker (a₁ : Set) (a₂ : Set) : Set → Set → Prop :=
  fun (b : Set) => fun (c : Set) => (b = ∅ → c = a₁) ∧ (b ≠ ∅ → c = a₂)


noncomputable def Pow_Pow_empty : Set := 𝒫 (𝒫 ∅)




theorem functional_func_pred_pick (a₁ : Set) (a₂ : Set) : functional_predicate Pow_Pow_empty (functional_predicate_picker a₁ a₂) :=
    fun (x) =>
      fun (_ : x ∈ 𝒫 (𝒫 ∅)) =>
        Or.elim (Classical.em (x = ∅))
        (
          fun (h : x = ∅) =>
            Exists.intro a₁ (And.intro
            (
              And.intro (fun (_ : x = ∅) => Eq.refl a₁) (fun (g : x ≠ ∅) => (False.elim : False → (a₁ = a₂)) (g h))
            )
            (
              fun (y : Set) =>
                fun (hy : (x = ∅ → y = a₁) ∧ (x ≠ ∅ → y = a₂)) =>
                  -- Eq.symm was proved in the previous task
                  Eq.symm ((And.left hy) h)
            )
            )
        )
        (
          fun (h : x ≠ ∅) =>
            Exists.intro a₂ (And.intro
            (
              And.intro (fun (g : x = ∅) => (False.elim : False → (a₂ = a₁)) (h g)) (fun (_ : x ≠ ∅) => Eq.refl a₂)
            )
            (
              fun (y : Set) =>
                fun (hy : (x = ∅ → y = a₁) ∧ (x ≠ ∅ → y = a₂)) =>
                  Eq.symm ((And.right hy) h)
            ))
        )


theorem exists_unordered_pair : ∀ a₁ a₂, ∃ C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂) :=
  fun (a₁) => fun (a₂) =>
    let exists_st := replacement (functional_predicate_picker a₁ a₂) Pow_Pow_empty (functional_func_pred_pick a₁ a₂)

    Exists.elim exists_st

    (
      fun (w) =>
        fun (hw : ∀ (y : Set), y ∈ w ↔ ∃ x ∈ Pow_Pow_empty; (x = ∅ → y = a₁) ∧ (x ≠ ∅ → y = a₂)) =>
          Exists.intro w
          (
            fun (y) =>
              Iff.intro
              (
                fun (g : y ∈ w) =>
                  let first := Iff.mp (hw y) g
                  Exists.elim first
                  (
                    fun (w) => fun (hw : (w ∈ Pow_Pow_empty) ∧ ((w = ∅ → y = a₁) ∧ (w ≠ ∅ → y = a₂))) =>
                      Or.elim (Classical.em (w = ∅))
                      (
                        fun (h₁ : w = ∅) =>
                        (Or.inl : y = a₁ → (y = a₁ ∨ y = a₂))
                        ((And.left (And.right hw)) h₁)
                      )
                      (
                        fun (h₂ : w ≠ ∅) =>
                        (Or.inr : y = a₂ → (y = a₁ ∨ y = a₂))
                        ((And.right (And.right hw)) h₂)
                      )
                  )

              )
              (
                fun (g : y = a₁ ∨ y = a₂) =>
                  Or.elim g
                  (
                    fun (g₁ : y = a₁) =>
                      let first := Iff.mpr (hw y)

                      let second := (
                        And.intro (
                          fun (_ :∅ = ∅) => g₁
                        )
                        (
                          fun (s : ∅ ≠ ∅) =>
                            (False.elim : False → y = a₂) (s (Eq.refl ∅))
                        )
                      )

                      let third := empty_elem_boolean (𝒫 ∅)

                      let fourth : ∃ x ∈ Pow_Pow_empty; ((x = ∅ → y = a₁) ∧ (x ≠ ∅ → y = a₂)) := Exists.intro ∅ (And.intro third second)

                      let fifth := first fourth

                      fifth

                  )
                  (
                    fun (g₂ : y = a₂) =>
                      let first := Iff.mpr (hw y)

                      let second := 𝒫 ∅

                      let third : ((𝒫 ∅ = ∅) → (y = a₁)) ∧ ((𝒫 ∅ ≠ ∅) → ( y = a₂)) := (
                        And.intro
                        (fun (s : second = ∅) =>
                          (False.elim : (False → y = a₁) ) ((boolean_set_not_empty ∅) s)
                        )
                        (
                          fun (_ : second ≠ ∅) =>
                            g₂
                        )
                      )

                      let fourth := subset_refl (𝒫 ∅)

                      let fifth := Iff.mpr (boolean_set_is_boolean (𝒫 ∅) (𝒫 ∅))

                      let sixth : (𝒫 ∅) ∈ Pow_Pow_empty := fifth fourth

                      let seventh : ∃ x ∈ Pow_Pow_empty; ((x = ∅ → y = a₁) ∧ (x ≠ ∅ → y = a₂)) := Exists.intro (𝒫 ∅) (And.intro sixth third)

                      let eighth := first seventh
                      eighth
                  )
              )
          )
    )



theorem unique_unordered_pair : (∀ a₁ a₂, ∃! C, ∀ x, (x ∈ C ↔ x = a₁ ∨ x = a₂)) :=
  fun (a₁) => fun (a₂) =>
    Exists.elim (exists_unordered_pair a₁ a₂)
    (
      fun (w) =>
        fun (hw : ∀ x, (x ∈ w ↔ x = a₁ ∨ x = a₂)) =>
          Exists.intro w (And.intro hw (fun (y) => fun (hy : ∀ x, (x ∈ y ↔ x = a₁ ∨ x = a₂)) =>

            (extensionality w y) (fun (x) => iff_trans_symm (x ∈ w) (x = a₁ ∨ x = a₂) (x ∈ y) (hw x) (hy x))

          ))
    )




noncomputable def unordered_pair_set : (Set → Set → Set) := fun (a₁ : Set) => fun (a₂ : Set) =>
  set_intro (fun (B) => ∀ x, (x ∈ B ↔ x = a₁ ∨ x = a₂)) (unique_unordered_pair a₁ a₂)


notation (priority := high) "{" a₁ ", " a₂ "}" => unordered_pair_set a₁ a₂


theorem unordered_pair_set_is_unordered_pair : ∀ a₁ a₂ x, x ∈ {a₁, a₂} ↔ x = a₁ ∨ x = a₂ :=
  fun (a₁) => fun (a₂) =>

    And.left (set_intro_prop (fun (B) => ∀ x, (x ∈ B ↔ x = a₁ ∨ x = a₂)) (unique_unordered_pair a₁ a₂))


noncomputable def singleton_set : (Set → Set) := fun (a) => unordered_pair_set a a

notation (priority := high) "{" a "}" => singleton_set a



theorem singleton_a_elem_is_a : ∀ a x, x ∈ {a} ↔ x = a :=
  fun (a) =>
    fun (x) =>
      Iff.intro
      (
        fun (h : x ∈ {a}) =>
          let first := Iff.mp (unordered_pair_set_is_unordered_pair a a x)
          let second := first h
          let third := Iff.mp (disj_idemp (x = a))
          let fourth := third second

          fourth
      )
      (
        fun (h : x = a) =>
          let third := Iff.mpr (disj_idemp (x = a))
          let fourth := third h
          let first := Iff.mpr (unordered_pair_set_is_unordered_pair a a x)

          first fourth

      )


theorem x_in_singl_x : ∀ x, x ∈ {x} :=
  fun (x) => Iff.mpr (singleton_a_elem_is_a x x) (Eq.refl x)

theorem singleton_non_empty : ∀ x, non_empty {x} :=
  fun (x) => Exists.intro x (x_in_singl_x x)



theorem neg_notin_refl : ∀ x, x ∉ x :=
  fun (x) =>
  let first := { x }
  let second := regularity first (singleton_non_empty x)
  Exists.elim second
  (
    fun (w) =>
      fun (hw : w ∈ { x } ∧ ∀ A ∈ w; A ∉ {x}) =>
        let third := (Iff.mp (singleton_a_elem_is_a x w)) (And.left hw)
        let fourth : ∀ A ∈ x; A ∉ {x} := eq_subst (fun (B : Set) => ∀ A ∈ B; A ∉ {x}) w x third (And.right hw)

        fun (s : (x ∈ x)) =>
          let fifth : x ∉ {x} := fourth x s

          fifth (x_in_singl_x x)
  )



theorem no_universal_set : ¬∃ A, ∀ x, x ∈ A :=
  fun (h : ∃ A, ∀ x, x ∈ A) =>
    Exists.elim h
    (
      fun (w) =>
        fun (hw : ∀ x, x ∈ w) =>
          let first : ∃ A, ∀ x, (x ∈ A) ↔ (x ∉ x) :=
            Exists.intro w (fun (x) => Iff.intro (fun (_ : x ∈ w) => neg_notin_refl x) (fun (_ : x ∉ x) => hw x))
          Russel_paradox first
    )



theorem left_unordered_pair : ∀ a₁ a₂, a₁ ∈ {a₁, a₂} :=
  fun (a₁) => fun (a₂) =>
    Iff.mpr (unordered_pair_set_is_unordered_pair a₁ a₂ a₁) ((Or.inl : a₁ = a₁ → a₁ = a₁ ∨ a₁ = a₂) (Eq.refl a₁))


theorem right_unordered_pair : ∀ a₁ a₂, a₂ ∈ {a₁, a₂} :=
  fun (a₁) => fun (a₂) =>
    Iff.mpr (unordered_pair_set_is_unordered_pair a₁ a₂ a₂) ((Or.inr : a₂ = a₂ → a₂ = a₁ ∨ a₂ = a₂) (Eq.refl a₂))




theorem unordered_pair_is_unordered : ∀ a₁ a₂, {a₁, a₂} = {a₂, a₁} :=
  fun (a₁) => fun (a₂) =>
    extensionality {a₁, a₂} {a₂, a₁} (
      fun (x) =>
      Iff.intro
      (
        fun (h : (x ∈ {a₁, a₂})) =>
          let first := (Iff.mp ((unordered_pair_set_is_unordered_pair a₁ a₂) x)) h

          let second := Iff.mp (disj_comm (x = a₁) (x = a₂))

          let third := second first

          let fourth := (Iff.mpr ((unordered_pair_set_is_unordered_pair a₂ a₁) x))

          let fifth := fourth third

          fifth

      )
      (
        fun (h : (x ∈ {a₂, a₁})) =>
          let first := (Iff.mp ((unordered_pair_set_is_unordered_pair a₂ a₁) x)) h

          let second := Iff.mp (disj_comm (x = a₂) (x = a₁))

          let third := second first

          let fourth := (Iff.mpr ((unordered_pair_set_is_unordered_pair a₁ a₂) x))

          let fifth := fourth third

          fifth
      )
    )


theorem unordered_pair_subs : ∀ a₁ a₂ A, (a₁ ∈ A) → (a₂ ∈ A) → ({a₁, a₂} ⊆ A) :=
  fun (a₁ a₂ A ha₁ ha₂) =>
    fun (x hx) =>
      Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair a₁ a₂ x) hx)
      (
        fun (hxa₁) =>
          eq_subst (fun (t) => t ∈ A) a₁ x (Eq.symm hxa₁) (ha₁)
      )
      (
        fun (hxa₂) =>
          eq_subst (fun (t) => t ∈ A) a₂ x (Eq.symm hxa₂) (ha₂)
      )

theorem singl_subs : ∀ x A, (x ∈ A) → {x} ⊆ A :=
  fun (x A hx) =>
    unordered_pair_subs x x A (hx) (hx)

theorem unique_union : ∀ A, ∃! B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y) :=
  fun (A) =>
    Exists.elim (union A)
    (
      fun (w) =>
        fun (hw : ∀ x, (x ∈ w ↔ ∃ y ∈ A; x ∈ y)) =>
          Exists.intro w (And.intro hw (fun (s) =>
            fun (hs : ∀ x, (x ∈ s ↔ ∃ y ∈ A; x ∈ y)) =>
              extensionality w s (fun (x) => iff_trans_symm (x ∈ w) (∃ y ∈ A; x ∈ y) (x ∈ s) (hw x) (hs x))
          ))
    )



noncomputable def union_set : (Set → Set) := fun (A) => set_intro (fun (B) => ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)) (unique_union A)


notation (priority := high) "⋃" => union_set


theorem union_set_is_union : (∀ A x, (x ∈ ⋃ A ↔ ∃ y ∈ A; x ∈ y)) :=
  fun (A) =>
    And.left (set_intro_prop (fun (B : Set) => ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)) (unique_union A))



theorem union_empty : ⋃ ∅ = ∅ :=
    Iff.mp (subs_subs_eq (⋃ ∅) ∅) (And.intro (
      fun (x) =>
        fun (g : x ∈ (⋃ ∅)) =>
          let first := Iff.mp (union_set_is_union ∅ x) g
          Exists.elim first
          (
            fun (y) =>
              fun (hy : y ∈ ∅ ∧ x ∈ y) =>
                False.elim (empty_set_is_empty y (And.left hy))
          )
    ) (empty_set_subset_any (⋃ ∅)))


theorem union_singleton : ∀ A, ⋃ {A} = A :=
  fun (A) =>
    extensionality (⋃ {A}) A
    (
      fun (x) =>
        Iff.intro
        (
          fun (g : x ∈ ⋃ {A}) =>
            Exists.elim ((Iff.mp (union_set_is_union {A} x)) g)
            (
              fun w =>
                fun (hw : w ∈ {A} ∧ x ∈ w) =>
                  let first := (Iff.mp (singleton_a_elem_is_a A w)) (And.left hw)
                  Eq.subst (first) (And.right hw)
            )
        )
        (
          fun (g : x ∈ A) =>
            let first := x_in_singl_x A
            let second : ∃ y ∈ {A}; x ∈ y := Exists.intro A (And.intro first g)

            let third := Iff.mpr (union_set_is_union {A} x)

            let fourth := third second

            fourth
        )
    )


theorem union_boolean : (∀ A, ⋃ (𝒫 A) = A) :=
  fun (A) =>
    extensionality (⋃ (𝒫 A)) (A)
    (
      fun (x) =>
        Iff.intro
        (
          fun (g : x ∈ ⋃ (𝒫 A)) =>
            let first := Iff.mp (union_set_is_union (𝒫 A) x) g
            Exists.elim first
            (
              fun (w) => fun (hw : w ∈ 𝒫 A ∧ x ∈ w) =>
                let second := And.left hw
                let third := Iff.mp (boolean_set_is_boolean A w) second x (And.right hw)
                third

            )
        )
        (
          fun (g : x ∈ A) =>
            let first := subset_refl A
            let second := Iff.mpr (boolean_set_is_boolean A A) first
            let third : ∃ y ∈ (𝒫 A); x ∈ y := Exists.intro A (And.intro (second) (g))
            let fourth := Iff.mpr (union_set_is_union (𝒫 A) x) third
            fourth
        )
    )


theorem elem_subset_union : (∀ A, ∀ x ∈ A; x ⊆ ⋃ A) :=
  fun (A) => fun (x) => fun (g : (x ∈ A)) =>
    fun (s) => fun (h : s ∈ x) =>
    let first := And.intro g h
    let second : ∃ x ∈ A; s ∈ x := Exists.intro x first
    let third := Iff.mpr (union_set_is_union A s) second
    third




theorem boolean_union : (∀ A, A ⊆ 𝒫 (⋃ A)) :=
  fun (A) =>
    fun (x) =>
      fun (g : x ∈ A) =>
        let first := (Iff.mpr (boolean_set_is_boolean (⋃ A) x))
        let second := first (elem_subset_union A x g)
        second



theorem sub_bool_un_mem_bool : ∀ A B, (A ⊆ 𝒫 B → ((⋃ A) ∈ 𝒫 B)) :=
  fun (A B) =>
    fun (hAB : A ⊆ 𝒫 B) =>
      Iff.mpr (boolean_set_is_boolean B (⋃ A)) (
        fun (m) =>
          fun (hm : m ∈ ⋃ A) =>
            let u := Iff.mp (union_set_is_union A m) hm
            Exists.elim u (
              fun (x) =>
                fun (hx : x ∈ A ∧ m ∈ x) =>
                  let v := hAB x (And.left hx)
                  Iff.mp (boolean_set_is_boolean B x) v m (And.right hx)
            )
      )






theorem specification_simple (P : Set → Prop) :  (∀ A, (¬∃ x ∈ A; P x) → ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) :=
    fun (A) =>
      fun (h : ¬∃ x ∈ A; P x) =>
      Exists.intro ∅ (fun (x) =>
        Iff.intro
        (
          fun (g : x ∈ ∅) =>
          (False.elim : False → x ∈ A ∧ P x)
          (empty_set_is_empty x g)
        )
        (
          fun (g : x ∈ A ∧ P x) =>
            let first : ∃ x ∈ A; P x := Exists.intro x g

            (False.elim : False → x ∈ ∅) (h first)
        )
      )


def functional_predicate_selector (P : Set → Prop) (e : Set)  : Set → Set → Prop :=
  fun (b : Set) => fun (c : Set) => (P b → c = b) ∧ (¬P b → c = e)


def functional_func_pred_sel (A : Set) (P : Set → Prop) (e : Set) : functional_predicate A (functional_predicate_selector P e) :=
  fun (x) =>
    fun (_ : x ∈ A) =>
      Or.elim (Classical.em (P x))
      (fun (g₁ : P x) =>
        Exists.intro x (And.intro (And.intro (fun (_ : P x) => Eq.refl x) (fun (s : ¬P x) => (False.elim : False → x = e) (s g₁))) (
          fun (y) => fun (hy : (P x → y = x) ∧ (¬P x → y = e)) =>
            Eq.symm (And.left hy g₁)
        ))
      )
      (
        fun (g₁ : ¬P x) =>
        Exists.intro e (And.intro (And.intro (fun (s : P x) => (False.elim : False → e = x) (g₁ s)) (fun (_ : ¬P x) => Eq.refl e)) (
          fun (y) => fun (hy : (P x → y = x) ∧ (¬ P x → y = e)) =>
            Eq.symm (And.right hy g₁)
        ))
      )





theorem specification_hard (P : Set → Prop) : (∀ A, (∃ x ∈ A; P x) → ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) :=
  fun (A) =>
    fun (h : ∃ x ∈ A; P x) =>
      Exists.elim h
      (
        fun (e) =>
          fun (e_property : e ∈ A ∧ P e) =>
        (
          let selector := functional_predicate_selector P e
          let selector_us_functional := functional_func_pred_sel A P e
          let first := replacement selector A selector_us_functional
          Exists.elim first
          (
            fun (w) =>
              fun (hw : ∀ y, (y ∈ w ↔ ∃ t ∈ A; (P t → y = t) ∧ (¬ P t → y = e))) =>
                Exists.intro w
                (
                  fun (x) =>
                  Iff.intro
                  (
                    fun (s : x ∈ w) =>
                      let second := (Iff.mp (hw x)) s
                      Exists.elim second
                      (
                        fun (u) =>
                          fun (hu : u ∈ A ∧ (P u → x = u) ∧ (¬ P u → x = e)) =>
                          Or.elim (Classical.em (P u))
                          (
                            fun (h₁ : P u) =>
                              let third := (And.left (And.right hu) (h₁))
                              eq_subst (fun (elem) => elem ∈ A ∧ P elem) (u) (x) (Eq.symm third)
                              (And.intro (And.left hu) (h₁))
                          )
                          (
                            fun (h₁ : ¬ P u) =>
                              let third := (And.right (And.right hu) (h₁))
                              eq_subst (fun (elem) => elem ∈ A ∧ P elem) (e) (x) (Eq.symm third)
                              (e_property)
                          )
                      )
                  )
                  (
                    fun (s : x ∈ A ∧ P x) =>
                      let second := (Iff.mpr (hw x))
                      let third := Exists.intro x (And.intro
                      (And.left s)
                      (And.intro
                      (fun (_ : P x) => Eq.refl x)
                      (fun (npx : ¬P x) => (False.elim : False → x = e) (npx (And.right s))))
                      )
                      second third
                  )
                )
          )
        )
      )








theorem specification (P : Set → Prop) : (∀ A, ∃ B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) :=
  fun (A) =>
    Or.elim (Classical.em (∃ x ∈ A; P x))
    (specification_hard P A)
    (specification_simple P A)


theorem unique_specification (P : Set → Prop) : (∀ A, ∃! B, ∀ x, (x ∈ B ↔ x ∈ A ∧ P x)) :=
  fun (A) =>
    Exists.elim (specification P A)
    (
      fun (w) =>
        fun (hw : ∀ s, (s ∈ w ↔ s ∈ A ∧ P s)) =>
          Exists.intro w (And.intro hw (fun (y) =>
            fun (hy : ∀ s, (s ∈ y ↔ s ∈ A ∧ P s)) =>
              extensionality w y (fun (x) => iff_trans_symm (x ∈ w) (x ∈ A ∧ P x) (x ∈ y) (hw x) (hy x))
          ))
    )



noncomputable def specification_set (P : Set → Prop) : (Set → Set) :=
  fun (A) => set_intro (fun (B) => (∀ x, x ∈ B ↔ x ∈ A ∧ P x)) (unique_specification P A)





syntax "{" ident "∈" term "|" term "}" : term



macro_rules
  | `({ $x:ident ∈ $A:term | $property:term })  => `(specification_set (fun ($x) => $property) $A)


theorem spec_is_spec (P : Set → Prop) : (∀ A x, x ∈ {x ∈ A | P x} ↔ x ∈ A ∧ P x) :=
  fun (A) =>
    And.left (set_intro_prop (fun (B) => ∀ x, x ∈ B ↔ x ∈ A ∧ P x) (unique_specification P A))


theorem specification_set_subset (P : Set → Prop) : (∀ A, {x ∈ A | P x} ⊆ A) :=
  fun (A) => fun(t) => fun (g : (t ∈ {x ∈ A | P x})) =>
    And.left ((Iff.mp (spec_is_spec P A t)) g)


def is_collective (P : Set → Prop) := ∃ A, ∀ x, (P x) → x ∈ A
def is_comprehense (P : Set → Prop) (X : Set) := (is_collective P ∧ ∀ x, (x ∈ X ↔ P x)) ∨ (¬(is_collective P) ∧ X = ∅)
theorem spec_unique (P : Set → Prop) : ∃! X, is_comprehense P X :=
  Or.elim (Classical.em (is_collective P))
  (
    fun (hins) =>
      Exists.elim hins (
        fun (A hA) =>
          Exists.intro {x ∈ A | P x} (
                let u₁ := fun (x) => Iff.intro (
                    fun (hx) =>
                      And.right (Iff.mp (spec_is_spec P A x) hx)
                  ) (
                    fun (hx) =>
                      Iff.mpr (spec_is_spec P A x) (
                        And.intro (hA x hx) (hx)
                      )
                  )
            And.intro (Or.inl (
              And.intro (hins) (
                u₁
              )
            )) (
              fun (y hy) =>
                Or.elim hy
                (
                  fun (hinsP) =>
                    extensionality {x ∈ A | P x} y (
                      fun (x) =>
                        Iff.intro
                        (
                          fun (hx) =>
                            let u₂ := Iff.mp (u₁ x) hx
                            Iff.mpr (And.right hinsP x) u₂
                        )
                        (
                          fun (hx) =>
                            Iff.mpr (u₁ x) (
                              Iff.mp (And.right hinsP x) (hx)
                            )
                        )
                    )

                )
                (
                  fun (hninsemp) =>
                    False.elim ((And.left hninsemp) (hins))
                )
            )
          )
      )
  )
  (
    fun (hnins) =>
      Exists.intro ∅ (
        And.intro (Or.inr (And.intro hnins (Eq.refl ∅))) (
          fun (y hy) =>
            Or.elim (hy)
            (
              fun (hinsP) =>
                False.elim (hnins (And.left hinsP))
            )
            (
              fun (hninsemp) =>
                Eq.symm (And.right hninsemp)
            )
        )
      )
  )




noncomputable def collect_compreh_set (P : Set → Prop) := set_intro (fun (X) => is_comprehense P X) (spec_unique P)
syntax "{" ident "|" term "}" : term
macro_rules
  | `({ $x:ident | $property:term })  => `(collect_compreh_set (fun ($x) => $property))

theorem compr_is_compr (P : Set → Prop) : is_collective P → (∀ x, (x ∈ {x | P x} ↔ P x)) :=
  fun (hP) =>
    let u₁ : is_comprehense P {x | P x} := And.left (set_intro_prop (fun (X) => is_comprehense P X) (spec_unique P))

    Or.elim u₁ (
      fun (hinsP) =>
        And.right hinsP
    ) (
      fun (hninsP) =>
        False.elim ((And.left hninsP) (hP))
    )


noncomputable def intersection_set : Set → Set := fun (A) => {x ∈ ⋃ A | ∀ y ∈ A; x ∈ y}

notation (priority := high) "⋂" => intersection_set

theorem intersection_set_is_intersection : ∀ A x, x ∈ ⋂ A ↔ (x ∈ ⋃ A ∧ ∀ y ∈ A; x ∈ y) :=
  fun (A) =>
    spec_is_spec (fun (x) => ∀ y ∈ A; x ∈ y) (⋃ A)


theorem intersection_sub_union : ∀ A, (⋂ A) ⊆ (⋃ A) :=
  fun (A) =>
    specification_set_subset (fun (x) => ∀ y ∈ A; x ∈ y) (⋃ A)


theorem intersection_non_empty : ∀ A, (A ≠ ∅ → ∀ x, (x ∈ ⋂ A) ↔ ∀ y ∈ A; x ∈ y) :=
  fun (A) => fun (h : A ≠ ∅) =>
    fun (x) =>
      Iff.intro
      (
        fun (g :x ∈ ⋂ A) => And.right ((Iff.mp (intersection_set_is_intersection A x)) g)
      )
      (
        fun (g : ∀ y ∈ A; x ∈ y) =>
          let first := non_empty_uni_then_exi (fun (t) => x ∈ t) A h g
          let second := Iff.mpr (union_set_is_union A x) first
          let fourth := And.intro second g
          let fifth := Iff.mpr (intersection_set_is_intersection A x) fourth
          fifth
      )



theorem union_subset_monotonic : ∀ A B, A ⊆ B → ⋃ A ⊆ ⋃ B :=
  fun (A) => fun (B) => fun (h : A ⊆ B) =>
    fun (x) => fun (g : x ∈ ⋃ A) =>
      let first := Iff.mp (union_set_is_union A x) g
      Exists.elim first
      (
        fun (w) =>
          fun (hw : w ∈ A ∧ x ∈ w) =>
          let second := And.intro (h w (And.left hw)) (And.right hw)
          let third : ∃ y ∈ B; x ∈ y := Exists.intro w second
          let fourth := Iff.mpr (union_set_is_union B x)
          fourth third
      )


theorem intersect_subset_monotonic : ∀ A B, (A ≠ ∅) → (A ⊆ B) → (⋂ B ⊆ ⋂ A) :=
  fun (A) => fun (B) => fun (g : A ≠ ∅) => fun (h : A ⊆ B) =>
    fun (x) => fun (s : x ∈ ⋂ B) =>
      let first : B ≠ ∅ := fun (h₁ : B = ∅) =>
        let second := (And.intro (Eq.subst h₁ h)) (empty_set_subset_any A)
        let third := (Iff.mp (subs_subs_eq A ∅))
        let fourth := third second
        g fourth
      let fifth: ∀ t ∈ B; x ∈ t := (Iff.mp (intersection_non_empty B first x)) s
      let sixth: ∀ t ∈ A; x ∈ t := fun (t) => fun (r : t ∈ A) => fifth t (h t r)
      let seventh := (Iff.mpr (intersection_non_empty A g x)) sixth
      seventh



theorem all_ss_then_union_ss : ∀ A B, (∀ X ∈ A; X ⊆ B) → (⋃ A ⊆ B) :=
  fun (A B) => fun (h₁ : ∀ X ∈ A; X ⊆ B) =>
    fun (x) => fun (h₂ : x ∈ (⋃ A)) => Exists.elim (Iff.mp (union_set_is_union A x) (h₂)) (
      fun (w) =>
        fun (hw : w ∈ A ∧ x ∈ w) =>
          h₁ w (And.left hw) x (And.right hw)
    )



noncomputable def singlbool_set (A) := {S ∈ 𝒫 (A) | ∃ x ∈ A; S = {x}}
syntax "𝒫₁" term : term
macro_rules
| `(𝒫₁ $A) => `(singlbool_set $A)

theorem singlbool_set_prop : ∀ A S, (S ∈ 𝒫₁ (A)) ↔ (∃ x ∈ A; S = {x}) :=
  fun (A S) =>
    let P := fun (S) => (∃ x ∈ A; S = {x})
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
              let u₁ := eq_subst (fun (t) => t ⊆ A) {x} S (Eq.symm (And.right hx)) (
                fun (s) =>
                  fun (hs) =>
                    let u₂ := Iff.mp (singleton_a_elem_is_a x s) hs
                    eq_subst (fun (t) => t ∈ A) x s (Eq.symm u₂) (And.left hx)
              )
              Iff.mpr (spec_is_spec P (𝒫 A) S) (
              And.intro (Iff.mpr (boolean_set_is_boolean A S) (
                u₁
              )) (hS)

              )
        )

    )


theorem in_singlbool_set : ∀ A x, ({x} ∈ 𝒫₁ (A)) ↔ (x ∈ A) :=
  fun (A x) =>
    Iff.intro
    (
      fun (hx) =>
        let u₁ := Iff.mp (singlbool_set_prop A {x}) hx
        Exists.elim u₁ (
          fun (y) =>
            fun (hy) =>
              eq_subst (fun (t) => t ∈ A) y x (
                Eq.symm (Iff.mp (singleton_a_elem_is_a y x) (
                  eq_subst (fun (t) => x ∈ t) {x} {y} (And.right hy) (x_in_singl_x x)
                ))
              ) (And.left hy)
        )
    )
    (
      fun (hx) =>
        Iff.mpr (singlbool_set_prop A {x}) (
          Exists.intro x (And.intro (hx) (Eq.refl {x}))
        )
    )
