import «Header»


noncomputable def union_2sets (A B : Set) := ⋃ {A, B}
infix:60 (priority:=high) " ∪ " => union_2sets
noncomputable def intersect_2sets (A B : Set) := {x ∈ A | x ∈ B}
infix:60 (priority:=high) " ∩ " => intersect_2sets
noncomputable def difference (A B : Set) := {x ∈ A | x ∉ B}
infix:60 (priority:=high) " \\ " => difference
noncomputable def symmetric_difference (A B : Set) := (A \ B) ∪ (B \ A)
infix:60 (priority:=high) " △ " => symmetric_difference
declare_syntax_cat set_comprehension
syntax term "; " set_comprehension : set_comprehension
syntax term : set_comprehension
syntax "{" set_comprehension "}" : term
macro_rules
| `({$term1:term; $term2:term}) => `(unordered_pair_set $term1:term $term2:term)
| `({$elem:term; $rest:set_comprehension}) => `({$rest:set_comprehension} ∪ {$elem:term})




theorem union2_sets_prop : (∀ A B x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B) :=
  fun (A) => fun(B) => fun(x) =>
    Iff.intro
    (
      fun (g : (x ∈ A ∪ B)) =>
      let first := (Iff.mp (union_set_is_union {A, B} x)) g
      Exists.elim first
      (
        fun (w) =>
          fun (hw : w ∈ {A, B} ∧ x ∈ w) =>
            let second := Iff.mp (unordered_pair_set_is_unordered_pair A B w) (And.left hw)
            Or.elim second
            (
              fun (h : (w = A)) =>
                let third := Eq.subst h (And.right hw)
                let fourth := (Or.inl : (x ∈ A) → (x ∈ A ∨ x ∈ B))
                fourth third
            )
            (
              fun (h : (w = B)) =>
              let third := Eq.subst h (And.right hw)
              let fourth := (Or.inr : (x ∈ B) → (x ∈ A ∨ x ∈ B))
              fourth third
            )
      )
    )
    (
      fun (g : (x ∈ A ∨ x ∈ B)) =>
        let first := (Iff.mpr (union_set_is_union {A, B} x))
        Or.elim g
        (
          fun (f : (x ∈ A)) =>
            let second := Iff.mpr (unordered_pair_set_is_unordered_pair A B A)
            let third := Eq.refl A
            let fourth := (Or.inl : A = A → (A = A ∨ A = B)) third
            let fifth := second fourth
            let sixth : ∃ w ∈ {A, B}; x ∈ w := Exists.intro A (And.intro (fifth) (f))
            let seventh := first sixth
            seventh
        )
        (
          fun (f : (x ∈ B)) =>
            let second := Iff.mpr (unordered_pair_set_is_unordered_pair A B B)
            let third := Eq.refl B
            let fourth := (Or.inr : B = B → (B = A ∨ B = B)) third
            let fifth := second fourth
            let sixth : ∃ w ∈ {A, B}; x ∈ w := Exists.intro B (And.intro (fifth) (f))
            let seventh := first sixth
            seventh
        )
    )


theorem intersect_2sets_prop : (∀ A B x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B) :=
  fun (A) => fun (B) =>
    spec_is_spec (fun (x) => x ∈ B) A

theorem intersect_2sets_is_intersect : (∀ A B, (⋂ {A, B}) = A ∩ B) :=
  fun (A B) =>
    let u₀ := Iff.mpr (set_non_empty_iff_non_empty {A, B}) (
      Exists.intro A (left_unordered_pair A B)
    )
    extensionality (⋂ {A, B}) (A ∩ B) (
      fun (x) =>
        Iff.intro
        (
          fun (hx) =>
            let u₁ := Iff.mp (intersection_non_empty {A, B} (u₀) x) hx
            Iff.mpr (intersect_2sets_prop A B x) (
              And.intro (u₁ A (left_unordered_pair A B)) (u₁ B (right_unordered_pair A B))
            )
        )
        (
          fun (hx) =>
            let u₁ := Iff.mp (intersect_2sets_prop A B x) hx
            Iff.mpr (intersection_non_empty {A, B} u₀ x) (
              fun (y) =>
                fun (hy) =>
                  Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair A B y) (hy))
                  (
                    fun (hy) =>
                      eq_subst (fun (t) => x ∈ t) A (y) (Eq.symm hy) (
                        And.left u₁
                      )
                  )
                  (
                    fun (hy) =>
                      eq_subst (fun (t) => x ∈ t) B (y) (Eq.symm hy) (
                        And.right u₁
                      )
                  )
            )
        )
    )


theorem difference_prop : (∀ A B x, x ∈ A \ B ↔ x ∈ A ∧ x ∉ B) :=
  fun (A) => fun (B) =>
    spec_is_spec (fun (x) => x ∉ B) A


theorem symmetric_difference_prop : (∀ A B x, x ∈ A △ B ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A)) :=
  fun (A) => fun (B) =>
    fun (x) =>
    Iff.intro
    (
      fun (g: x ∈ A △ B) =>
        let first := (Iff.mp (union2_sets_prop (A \ B) (B \ A) x)) g
        Or.elim (first)
        (
          fun (h : x ∈ A \ B) =>
            let second := (Iff.mp (difference_prop A B x)) h

            (Or.inl : (x ∈ A ∧ x ∉ B) → (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A))
            (second)
        )
        (
          fun (h : x ∈ B \ A) =>
            let second := (Iff.mp (difference_prop B A x)) h

            (Or.inr : (x ∈ B ∧ x ∉ A) → (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A))
            (second)
        )
    )
    (
      fun (g: (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A)) =>
        let first := Iff.mpr (union2_sets_prop (A \ B) (B \ A) x)
        Or.elim g
        (
          fun (h : x ∈ A ∧ x ∉ B) =>

            let second := (Or.inl : x ∈ A \ B → (x ∈ A \ B ∨ x ∈ B \ A)) ((Iff.mpr (difference_prop A B x)) h)
            first second
        )
        (
          fun (h : x ∈ B ∧ x ∉ A) =>

            let second := (Or.inr : x ∈ B \ A → (x ∈ A \ B ∨ x ∈ B \ A)) ((Iff.mpr (difference_prop B A x)) h)
            first second
        )
    )


theorem union2sets_subset_prop : (∀ A B, (A ⊆ A ∪ B) ∧ (B ⊆ A ∪ B)) :=
  fun (A) => fun (B) =>
    And.intro
    (
      fun (x) =>
      fun (g : x ∈ A) =>
        let first := Iff.mpr (union2_sets_prop A B x)
        first ((Or.inl : (x ∈ A → x ∈ A ∨ x ∈ B)) g)
    )
    (
      fun (x) =>
      fun (g : x ∈ B) =>
        let first := Iff.mpr (union2_sets_prop A B x)
        first ((Or.inr : (x ∈ B → x ∈ A ∨ x ∈ B)) g)
    )


theorem interset2sets_subset_prop : (∀ A B, (A ∩ B ⊆ A) ∧ (A ∩ B ⊆ B)) :=
  fun (A) => fun (B) =>
    And.intro
    (
      specification_set_subset (fun (x) => x ∈ B) A
    )
    (
      fun (x) =>
        fun (g : x ∈ A ∩ B) =>
          And.right ((Iff.mp (intersect_2sets_prop A B x)) g)
    )


theorem difference_subset_prop : (∀ A B, A \ B ⊆ A) :=
  fun (A) => fun (B) =>
    specification_set_subset (fun (x) => x ∉ B) A



theorem sub_sub_inter_sub : ∀ A B X, (X ⊆ A) → (X ⊆ B) → (X ⊆ (A ∩ B))  :=
  fun (A B X) =>
    fun (hXA : (X ⊆ A)) =>
      fun (hXB : (X ⊆ B)) =>
        fun (x) =>
          fun (hx : x ∈ X) =>
            Iff.mpr (intersect_2sets_prop A B x) (
              And.intro (hXA x hx) (hXB x hx)
            )


theorem sub_sub_union_sub : ∀ A B X, (A ⊆ X) → (B ⊆ X) → ((A ∪ B) ⊆ X) :=
  fun (A B X) =>
    fun (hAX : (A ⊆ X)) =>
      fun (hBX : (B ⊆ X)) =>
        fun (x) =>
          fun (hx : x ∈ (A ∪ B)) =>
            let u := Iff.mp (union2_sets_prop A B x) hx
            Or.elim u
            (
              fun (hxA : x ∈ A) =>
                hAX x hxA
            )
            (
              fun (hxB : x ∈ B) =>
                hBX x hxB
            )



theorem equivalence_3 (p q r : Prop) : (p → q) → (q → r) → (r → p) → ((p ↔ q) ∧ (p ↔ r) ∧ (q ↔ r)) :=
  fun (h₁ : p → q) =>
   fun (h₂ : q → r) =>
    fun (h₃ : r → p) =>
      And.intro
      (
        Iff.intro
        (
          h₁
        )
        (
          syllogism q r p h₂ h₃
        )
      )
      (
        And.intro
        (
          Iff.intro
          (
            syllogism p q r h₁ h₂
          )
          (
            h₃
          )
        )
        (
          Iff.intro
          (
            h₂
          )
          (
            syllogism r p q h₃ h₁
          )
        )
      )



theorem subset_using_equality : ∀ A B, (A ⊆ B ↔ A ∩ B = A) ∧ (A ⊆ B ↔ A ∪ B = B) ∧ (A ∩ B = A ↔ A ∪ B = B) :=
  fun (A) => fun (B) =>
    equivalence_3 (A ⊆ B) (A ∩ B = A) (A ∪ B = B) (
      fun (g : A ⊆ B) =>
        subset_then_equality (A ∩ B) A
        (And.intro
        (
          And.left (interset2sets_subset_prop A B)
        )
        (
          fun (x) =>
          fun (h : x ∈ A) =>
            (Iff.mpr (intersect_2sets_prop A B x)) (And.intro (h) (g x h))
        )

        )

    ) (
        fun (g : A ∩ B = A) =>
          subset_then_equality (A ∪ B) B (And.intro (
            fun (x) =>
            fun (h : x ∈ A ∪ B) =>
              Or.elim (Iff.mp (union2_sets_prop A B x) h)
              (fun (s : x ∈ A) =>
                let first: x ∈ A ∩ B := Eq.substr g s
                And.right ((Iff.mp (intersect_2sets_prop A B x)) first)
              )
              (
                fun (s : x ∈ B) => s
              )
          ) (And.right (union2sets_subset_prop A B)))
    ) (
        fun (g : A ∪ B = B) =>
          fun (x) =>
            fun (s : x ∈ A) =>
              let first := (Or.inl : x ∈ A → (x ∈ A ∨ x ∈ B)) s
              let second := (Iff.mpr (union2_sets_prop A B x)) first
              Eq.subst g second
    )


theorem conj_congr_both (p q r s : Prop) : (p ↔ q) → (r ↔ s) → (p ∧ r ↔ q ∧ s) :=
  fun (h : p ↔ q) =>
    fun (g : r ↔ s) =>
      let first := conj_congr_right p q r h
      let second := conj_congr_left r s q g
      iff_transitivity (p ∧ r) (q ∧ r) (q ∧ s) first second


theorem disj_congr_both (p q r s : Prop) : (p ↔ q) → (r ↔ s) → (p ∨ r ↔ q ∨ s) :=
  fun (h : p ↔ q) =>
    fun (g : r ↔ s) =>
      let first := disj_congr_right p q r h
      let second := disj_congr_left r s q g
      iff_transitivity (p ∨ r) (q ∨ r) (q ∨ s) first second


theorem contradiction_equiv (p : Prop) : (p ∧ ¬p) ↔ False :=
  Iff.intro (no_contradiction p) (False.elim : False → (p ∧ ¬p))





theorem intersec2_idemp : (∀ A, A ∩ A = A) :=
  fun (A) =>
    extensionality (A ∩ A) A (
      fun (x) =>
        let first := (intersect_2sets_prop A A x)
        let second := conj_indempodent (x ∈ A)
        let iff_trans := iff_transitivity (x ∈ A ∩ A) (x ∈ A ∧ x ∈ A) (x ∈ A)
        iff_trans first second
    )


theorem union2_idepm : (∀ A, A ∪ A = A) :=
  fun (A) =>
    extensionality (A ∪ A) A (
      fun (x) =>
        let first := (union2_sets_prop A A x)
        let second := disj_indempodent (x ∈ A)
        let iff_trans := iff_transitivity (x ∈ A ∪ A) (x ∈ A ∨ x ∈ A) (x ∈ A)
        iff_trans first second
    )


theorem intersec2_comm : (∀ A B, A ∩ B = B ∩ A) :=
  fun (A) => fun (B) =>
    extensionality (A ∩ B) (B ∩ A) (
      fun (x) =>
        let first := (intersect_2sets_prop A B x)
        let second:= iff_symm (x ∈ B ∩ A) (x ∈ B ∧ x ∈ A) (intersect_2sets_prop B A x)
        let third := (conj_comm) (x ∈ A) (x ∈ B)
        let iff_trans1 := iff_transitivity (x ∈ A ∩ B) (x ∈ A ∧ x ∈ B) (x ∈ B ∧ x ∈ A)
        let iff_trans2 := iff_transitivity (x ∈ A ∩ B) (x ∈ B ∧ x ∈ A) (x ∈ B ∩ A)
        iff_trans2 (iff_trans1 (first) (third)) second
    )


theorem union2_comm : (∀ A B, A ∪ B = B ∪ A) :=
  fun (A) => fun (B) =>
    extensionality (A ∪ B) (B ∪ A) (
      fun (x) =>
        let first := (union2_sets_prop A B x)
        let second := iff_symm (x ∈ B ∪ A) (x ∈ B ∨ x ∈ A) (union2_sets_prop B A x)
        let third := (disj_comm) (x ∈ A) (x ∈ B)
        let iff_trans1 := iff_transitivity (x ∈ A ∪ B) (x ∈ A ∨ x ∈ B) (x ∈ B ∨ x ∈ A)
        let iff_trans2 := iff_transitivity (x ∈ A ∪ B) (x ∈ B ∨ x ∈ A) (x ∈ B ∪ A)
        iff_trans2 (iff_trans1 (first) (third)) second
    )


theorem inter2_assoc : (∀ A B C, (A ∩ B) ∩ C = A ∩ (B ∩ C)) :=
  fun (A) => fun (B) => fun (C) =>
    extensionality ((A ∩ B) ∩ C) (A ∩ (B ∩ C)) (
      fun (x) =>
        let first := (intersect_2sets_prop (A ∩ B) C x)
        let second := (intersect_2sets_prop A B x)
        let third := conj_congr_right (x ∈ A ∩ B) (x ∈ A ∧ x ∈ B) (x ∈ C) second
        let iff_trans1 := iff_transitivity (x ∈ (A ∩ B) ∩ C) (x ∈ A ∩ B ∧ x ∈ C) ((x ∈ A ∧ x ∈ B) ∧ x ∈ C) first third

        let fourth := (intersect_2sets_prop (A) (B ∩ C) x)
        let fifth := (intersect_2sets_prop B C x)
        let sixth := conj_congr_left (x ∈ B ∩ C) (x ∈ B ∧ x ∈ C) (x ∈ A) fifth
        let iff_trans2 := iff_symm (x ∈ (A ∩ (B ∩ C))) (x ∈ A ∧ x ∈ B ∧ x ∈ C) (iff_transitivity (x ∈ (A ∩ (B ∩ C))) (x ∈ A ∧ x ∈ B ∩ C) (x ∈ A ∧ (x ∈ B ∧ x ∈ C)) fourth sixth)

        let seventh := conj_assoc (x ∈ A) (x ∈ B) (x ∈ C)

        let iff_trans3 := iff_transitivity (x ∈ (A ∩ B) ∩ C) ((x ∈ A ∧ x ∈ B) ∧ x ∈ C) (x ∈ A ∧ x ∈ B ∧ x ∈ C) iff_trans1 seventh
        iff_transitivity (x ∈ (A ∩ B) ∩ C) (x ∈ A ∧ x ∈ B ∧ x ∈ C) (x ∈ A ∩ (B ∩ C)) iff_trans3 iff_trans2
    )


theorem union2_assoc : (∀ A B C, (A ∪ B) ∪ C = A ∪ (B ∪ C)) :=
  fun (A) => fun (B) => fun (C) =>
    extensionality ((A ∪ B) ∪ C) (A ∪ (B ∪ C)) (
      fun (x) =>
        let first := (union2_sets_prop (A ∪ B) C x)
        let second := (union2_sets_prop A B x)
        let third := disj_congr_right (x ∈ A ∪ B) (x ∈ A ∨ x ∈ B) (x ∈ C) second
        let iff_trans1 := iff_transitivity (x ∈ (A ∪ B) ∪ C) (x ∈ A ∪ B ∨ x ∈ C) ((x ∈ A ∨ x ∈ B) ∨ x ∈ C) first third

        let fourth := (union2_sets_prop (A) (B ∪ C) x)
        let fifth := (union2_sets_prop B C x)
        let sixth := disj_congr_left (x ∈ B ∪ C) (x ∈ B ∨ x ∈ C) (x ∈ A) fifth
        let iff_trans2 := iff_symm (x ∈ (A ∪ (B ∪ C))) (x ∈ A ∨ x ∈ B ∨ x ∈ C) (iff_transitivity (x ∈ (A ∪ (B ∪ C))) (x ∈ A ∨ x ∈ B ∪ C) (x ∈ A ∨ (x ∈ B ∨ x ∈ C)) fourth sixth)

        let seventh := disj_assoc (x ∈ A) (x ∈ B) (x ∈ C)

        let iff_trans3 := iff_transitivity (x ∈ (A ∪ B) ∪ C) ((x ∈ A ∨ x ∈ B) ∨ x ∈ C) (x ∈ A ∨ x ∈ B ∨ x ∈ C) iff_trans1 seventh
        iff_transitivity (x ∈ ((A ∪ B) ∪ C)) (x ∈ A ∨ x ∈ B ∨ x ∈ C) (x ∈ A ∪ (B ∪ C)) iff_trans3 iff_trans2
    )



theorem inter_union_absorbtion : (∀ A B, A ∩ (A ∪ B) = A) :=
  fun (A) => fun (B) =>
    extensionality (A ∩ (A ∪ B)) A
    (
      fun (x) =>
        let first := intersect_2sets_prop A (A ∪ B) x
        let second := union2_sets_prop A B x
        let third := conj_congr_left (x ∈ A ∪ B) (x ∈ A ∨ x ∈ B) (x ∈ A) second
        let iff_trans1 := iff_transitivity (x ∈ (A ∩ (A ∪ B))) (x ∈ A ∧ (x ∈ A ∪ B)) (x ∈ A ∧ (x ∈ A ∨ x ∈ B)) first third

        let fourth := conj_disj_absorbtion (x ∈ A) (x ∈ B)
        iff_transitivity (x ∈ A ∩ (A ∪ B)) (x ∈ A ∧ (x ∈ A ∨ x ∈ B)) (x ∈ A) iff_trans1 fourth
    )


theorem union_inter_absorbtion : (∀ A B, A ∪ (A ∩ B) = A) :=
  fun (A) => fun (B) =>
    extensionality (A ∪ (A ∩ B)) A
    (
      fun (x) =>
        let first := union2_sets_prop A (A ∩ B) x
        let second := intersect_2sets_prop A B x
        let third := disj_congr_left (x ∈ A ∩ B) (x ∈ A ∧ x ∈ B) (x ∈ A) second
        let iff_trans1 := iff_transitivity (x ∈ (A ∪ (A ∩ B))) (x ∈ A ∨ (x ∈ A ∩ B)) (x ∈ A ∨ (x ∈ A ∧ x ∈ B)) first third

        let fourth := disj_conj_absorbtion (x ∈ A) (x ∈ B)
        iff_transitivity (x ∈ A ∪ (A ∩ B)) (x ∈ A ∨ (x ∈ A ∧ x ∈ B)) (x ∈ A) iff_trans1 fourth
    )


theorem inter_union_distribution : (∀ A B C, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)) :=
  fun (A) => fun (B) => fun(C) =>
    extensionality (A ∩ (B ∪ C)) ((A ∩ B) ∪ (A ∩ C))
    (
      fun (x) =>
        let first := intersect_2sets_prop A (B ∪ C) x
        let second := union2_sets_prop B C x
        let third := conj_congr_left (x ∈ B ∪ C) (x ∈ B ∨ x ∈ C) (x ∈ A) second
        let iff_trans1 := iff_transitivity (x ∈ (A ∩ (B ∪ C))) (x ∈ A ∧ (x ∈ B ∪ C)) (x ∈ A ∧ (x ∈ B ∨ x ∈ C)) first third

        let fourth := union2_sets_prop (A ∩ B) (A ∩ C) x
        let fifth := intersect_2sets_prop A B x
        let sixth := intersect_2sets_prop A C x
        let seventh := disj_congr_both (x ∈ A ∩ B) (x ∈ A ∧ x ∈ B) (x ∈ A ∩ C) (x ∈ A ∧ x ∈ C) fifth sixth
        let eight:= iff_symm (x ∈ ((A ∩ B) ∪ (A ∩ C))) (x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C) (iff_transitivity (x ∈ ((A ∩ B) ∪ (A ∩ C))) (x ∈ A ∩ B ∨ x ∈ A ∩ C)
         (x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C) fourth seventh)


        let nineth := conj_disj_distrib (x ∈ A) (x ∈ B) (x ∈ C)

        iff_transitivity (x ∈ A ∩ (B ∪ C)) (x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C) (x ∈ ((A ∩ B) ∪ (A ∩ C)))
        (iff_transitivity (x ∈ A ∩ (B ∪ C)) (x ∈ A ∧ (x ∈ B ∨ x ∈ C)) (x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C) iff_trans1 nineth) (eight)
    )


theorem union_inter_distribution : (∀ A B C, A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)) :=
  fun (A) => fun (B) => fun (C) =>
    extensionality (A ∪ (B ∩ C)) ((A ∪ B) ∩ (A ∪ C)) (
      fun (x) =>
        let first := union2_sets_prop A (B ∩ C) x
        let second := intersect_2sets_prop B C x
        let third := disj_congr_left (x ∈ B ∩ C) (x ∈ B ∧ x ∈ C) (x ∈ A) second
        let iff_trans1 := iff_transitivity (x ∈ (A ∪ (B ∩ C))) (x ∈ A ∨ (x ∈ B ∩ C)) (x ∈ A ∨ (x ∈ B ∧ x ∈ C)) first third

        let fourth := intersect_2sets_prop (A ∪ B) (A ∪ C) x
        let fifth := union2_sets_prop A B x
        let sixth := union2_sets_prop A C x
        let seventh := conj_congr_both (x ∈ A ∪ B) (x ∈ A ∨ x ∈ B) (x ∈ A ∪ C) (x ∈ A ∨ x ∈ C) fifth sixth
        let eighth := iff_symm (x ∈ (A ∪ B) ∩ (A ∪ C)) ((x ∈ A ∨ x ∈ B) ∧ (x ∈ A ∨ x ∈ C)) (iff_transitivity (x ∈ (A ∪ B) ∩ (A ∪ C)) (x ∈ A ∪ B ∧ x ∈ A ∪ C)
        ((x ∈ A ∨ x ∈ B) ∧ (x ∈ A ∨ x ∈ C)) fourth seventh)

        let nineth := disj_conj_distrib (x ∈ A) (x ∈ B) (x ∈ C)

        iff_transitivity (x ∈ A ∪ (B ∩ C)) ((x ∈ A ∨ x ∈ B) ∧ (x ∈ A ∨ x ∈ C)) (x ∈ ((A ∪ B) ∩ (A ∪ C)))
        (iff_transitivity (x ∈ A ∪ (B ∩ C)) (x ∈ A ∨ (x ∈ B ∧ x ∈ C)) ((x ∈ A ∨ x ∈ B) ∧ (x ∈ A ∨ x ∈ C)) iff_trans1 nineth) (eighth)
    )


theorem double_compl (U : Set) (A : Set)  (h : A ⊆ U) : (U \ (U \ A)) = A :=
  extensionality (U \ (U \ A)) A (
    fun (x) =>
      let first : x ∈ (U \ (U \ A)) ↔ x ∈ U ∧ x ∉ (U \ A) := difference_prop U (U \ A) x
      let second : x ∈ (U \ (U \ A)) ↔ (x ∈ U ∧ ¬ (x ∈ U ∧ x ∉ A)) := iff_subst_pred_arg (fun (s) => x ∈ (U \ (U \ A)) ↔ x ∈ U ∧ ¬ s) (x ∈ (U \ A)) (x ∈ U ∧ x ∉ A) (difference_prop U A x) (first)
      let third : x ∈ (U \ (U \ A)) ↔ x ∈ U ∧ (x ∉ U ∨ ¬ (x ∉ A)) := iff_subst_pred_arg (fun (s) => x ∈ (U \ (U \ A)) ↔ (x ∈ U ∧ s)) (¬ (x ∈ U ∧ x ∉ A)) (x ∉ U ∨ ¬ (x ∉ A)) (de_morgan_conj (x ∈ U) (x ∉ A)) (second)
      let fourth : x ∈ (U \ (U \ A)) ↔ ((x ∈ U ∧ x ∉ U) ∨ (x ∈ U ∧ ¬ (x ∉ A))) := iff_subst_pred_arg (fun (s) => x ∈ (U \ (U \ A)) ↔ s) (x ∈ U ∧ (x ∉ U ∨ ¬ (x ∉ A))) ((x ∈ U ∧ x ∉ U) ∨ (x ∈ U ∧ ¬ (x ∉ A))) (conj_disj_distrib (x ∈ U) (x ∉ U) (¬ (x ∉ A))) (third)
      let fifth : x ∈ (U \ (U \ A)) ↔ (False ∨ (x ∈ U ∧ ¬ (x ∉ A))) := iff_subst_pred_arg (fun (s) => x ∈ (U \ (U \ A)) ↔ s ∨ (x ∈ U ∧ ¬ (x ∉ A))) (x ∈ U ∧ x ∉ U) False (contradiction_equiv (x ∈ U)) fourth
      let sixth : x ∈ ((U \ (U \ A))) ↔ (x ∈ U ∧ ¬ (x ∉ A)) := iff_subst_pred_arg (fun (s) => x ∈ (U \ (U \ A)) ↔ s) (False ∨ (x ∈ U ∧ ¬ (x ∉ A))) (x ∈ U ∧ ¬ (x ∉ A)) (False_or_p (x ∈ U ∧ ¬ (x ∉ A))) fifth
      let seventh : x ∈ ((U \ (U \ A))) ↔ (x ∈ U ∧ x ∈ A) := iff_subst_pred_arg (fun (s) => x ∈ (U \ (U \ A)) ↔ x ∈ U ∧ s) (¬ (x ∉ A)) (x ∈ A) (double_neg (x ∈ A)) sixth
      iff_subst_pred_arg (fun (s) => x ∈ (U \ (U \ A)) ↔ s) (x ∈ U ∧ x ∈ A) (x ∈ A) (Iff.intro (fun (t : x ∈ U ∧ x ∈ A) => And.right t) (fun (t : x ∈ A) => And.intro (h x t) (t))) (seventh)
  )









theorem demorgan_inter : ∀ U A B, (U \ (A ∩ B) = (U \ A) ∪ (U \ B)) :=
  fun (U A B) =>
  extensionality (U \ (A ∩ B)) ((U \ A) ∪ (U \ B)) (
    fun (x) =>
      Iff.intro
      (
        fun (g : (x ∈ U \ (A ∩ B))) =>
          let first := And.right (Iff.mp (difference_prop U (A ∩ B) x) g)
          let second := intersect_2sets_prop A B x
          let third := Iff.mp (neg_congr (x ∈ A ∩ B) (x ∈ A ∧ x ∈ B) second) first
          let fourth := Iff.mp (de_morgan_conj (x ∈ A) (x ∈ B)) third
          Or.elim fourth
          (
            fun (s : x ∉ A) =>
              let fifth := And.intro (And.left (Iff.mp (difference_prop U (A ∩ B) x) g)) (s)
              let sixth := Iff.mpr (difference_prop U A x) fifth
              And.left (union2sets_subset_prop (U \ A) (U \ B)) x sixth
          )
          (
            fun (s : x ∉ B) =>
              let fifth := And.intro (And.left ((Iff.mp ((difference_prop U (A ∩ B) x)) g))) (s)
              let sixth := Iff.mpr (difference_prop U B x) fifth
              And.right (union2sets_subset_prop (U \ A) (U \ B)) x sixth
          )
      )
      (
        fun (g : (x ∈ (U \ A) ∪ (U \ B))) =>
          Or.elim (Iff.mp (union2_sets_prop (U \ A) (U \ B) x) g)
          (
            fun (s : (x ∈ U \ A)) =>
              let first := Iff.mp (difference_prop U A x) s
              let second := (Iff.mpr (de_morgan_conj (x ∈ A) (x ∈ B)) ((Or.inl : x ∉ A → x ∉ A ∨ x ∉ B) (And.right first)))
              (Iff.mpr (difference_prop U (A ∩ B) x)) (And.intro (And.left first) (Iff.mpr (neg_congr (x ∈ A ∩ B) (x ∈ A ∧ x ∈ B) (intersect_2sets_prop A B x)) second))
          )
          (
            fun (s : (x ∈ U \ B)) =>
              let first := Iff.mp (difference_prop U B x) s
              let second := (Iff.mpr (de_morgan_conj (x ∈ A) (x ∈ B)) ((Or.inr : x ∉ B → x ∉ A ∨ x ∉ B) (And.right first)))
              (Iff.mpr (difference_prop U (A ∩ B) x)) (And.intro (And.left first) (Iff.mpr (neg_congr (x ∈ A ∩ B) (x ∈ A ∧ x ∈ B) (intersect_2sets_prop A B x)) second))
          )

      )
  )


theorem demorgan_union: ∀ U A B, (U \ (A ∪ B) = (U \ A) ∩ (U \ B)) :=
  fun (U A B) =>
  extensionality (U \ (A ∪ B)) ((U \ A) ∩ (U \ B)) (
    fun (x) =>
      Iff.intro
      (
        fun (g : (x ∈ U \ (A ∪ B))) =>
          let first := And.left (Iff.mp (difference_prop U (A ∪ B) x) g)
          let second := And.right (Iff.mp (difference_prop U (A ∪ B) x) g)
          let third := Iff.mp (de_morgan_disj (x ∈ A) (x ∈ B)) (Iff.mp (neg_congr (x ∈ A ∪ B) (x ∈ A ∨ x ∈ B) (union2_sets_prop A B x)) second)
          let fourth := (Iff.mpr (difference_prop U A x)) (And.intro first (And.left third))
          let fifth := (Iff.mpr (difference_prop U B x)) (And.intro first (And.right third))
          (Iff.mpr (intersect_2sets_prop (U \ A) (U \ B) x)) (And.intro (fourth) (fifth))

      )
      (
        fun (g : (x ∈ (U \ A) ∩ (U \ B))) =>
          let first := And.left (Iff.mp (difference_prop U A x) (And.left (Iff.mp (intersect_2sets_prop (U \ A) (U \ B) x) g)))
          let second := And.right (Iff.mp (difference_prop U A x) (And.left (Iff.mp (intersect_2sets_prop (U \ A) (U \ B) x) g)))
          let third := And.right (Iff.mp (difference_prop U B x) (And.right (Iff.mp (intersect_2sets_prop (U \ A) (U \ B) x) g)))
          let fourth := Iff.mpr ((neg_congr (x ∈ A ∪ B) (x ∈ A ∨ x ∈ B) (union2_sets_prop A B x))) (Iff.mpr (de_morgan_disj (x ∈ A) (x ∈ B)) (And.intro second third))
          Iff.mpr (difference_prop U (A ∪ B) x) (And.intro first fourth)
      )
  )



theorem inter_to_empty: ∀ U A, (A ∩ (U \ A) = ∅) :=
  fun (U A) =>
  extensionality (A ∩ (U \ A)) (∅) (
      fun (x) =>
      Iff.intro
      (
        fun (h : x ∈ A ∩ (U \ A)) =>
          let first := And.left (Iff.mp (intersect_2sets_prop A (U \ A) x) h)
          let second := And.right ((Iff.mp (difference_prop U A x)) (And.right (Iff.mp (intersect_2sets_prop A (U \ A) x) h)))
          (False.elim : (False → x ∈ ∅)) (second first)

      )
      (
        empty_set_is_subset_any (A ∩ (U \ A)) x
      )
  )



theorem difference_inter_prop (U A B : Set) (h : A ⊆ U) : (A \ B = A ∩ (U \ B)) :=
  extensionality (A \ B) (A ∩ (U \ B)) (
    fun (x) =>
      Iff.intro
      (
        fun (g : (x ∈ A \ B)) =>
          Iff.mpr (intersect_2sets_prop A (U \ B) x)
          (And.intro (And.left (Iff.mp (difference_prop A B x) g))
          (Iff.mpr (difference_prop U B x) (And.intro (h x (And.left (Iff.mp (difference_prop A B x) g))) (And.right (Iff.mp (difference_prop A B x) g)))))
      )
      (
        fun (g : (x ∈ A ∩ (U \ B))) =>
          let first := Iff.mp (intersect_2sets_prop A (U \ B) x) g
          let second := And.left first
          let third := And.right first
          Iff.mpr ((difference_prop A B x)) (And.intro (second) (And.right (Iff.mp (difference_prop U B x) third)))
      )
  )



theorem union_to_universum (U A : Set) (h : A ⊆ U) : (A ∪ (U \ A) = U) :=
  extensionality (A ∪ (U \ A)) (U) (
    fun (x) =>
    Iff.intro
    (
      fun (g : (x ∈ A ∪ (U \ A))) =>
        let first := Iff.mp (union2_sets_prop A (U \ A) x) g
        Or.elim first
        (
          h x
        )
        (
          difference_subset_prop U A x
        )
    )
    (
      fun (g : (x ∈ U)) =>
        Or.elim (Classical.em (x ∈ A))
        (
          fun (s : x ∈ A) =>
            Iff.mpr (union2_sets_prop A (U \ A) x) ((Or.inl : (x ∈ A → (x ∈ A ∨ x ∈ (U \ A)) )) (s))
        )
        (
          fun (s : x ∉ A) =>
            And.right (union2sets_subset_prop A (U \ A)) x ((Iff.mpr ((difference_prop U A x)) (And.intro g s)))
        )
    )
  )


theorem intersec2_empty : (∀ A, A ∩ ∅ = ∅) :=
  fun (A) =>
    extensionality (A ∩ ∅) ∅ (
      fun (x) =>
        Iff.intro
        (
          (And.right (interset2sets_subset_prop A ∅)) x
        )
        (
          fun (g : x ∈ ∅) =>
            (False.elim : False → x ∈ (A ∩ ∅)) (empty_set_is_empty x g)

        )
    )


theorem union2_empty : (∀ A, A ∪ ∅ = A) :=
  fun (A) =>
    extensionality (A ∪ ∅) A (
      fun (x) =>
        Iff.intro
        (
          fun (h : x ∈ (A ∪ ∅)) =>
            Or.elim (Iff.mp (union2_sets_prop A ∅ x) h)
            (
              fun (h : x ∈ A) => h
            )
            (
              empty_set_is_subset_any A x
            )
        )
        (
          fun (h : x ∈ A) =>
            Iff.mpr ((union2_sets_prop A ∅ x)) ((Or.inl : x ∈ A → (x ∈ A ∨ (x ∈ ∅))) h)
        )
    )


theorem inter2_universum (U A : Set) (h : A ⊆ U) : A ∩ U = A :=
  Iff.mp (And.left (subset_using_equality A U)) h

theorem union2_universum (U A : Set) (h : A ⊆ U) : A ∪ U = U :=
  Iff.mp (And.left (And.right (subset_using_equality A U))) h



-- now, using set algebra properties and eq_subst, it is easy to prove the equality
-- such sets without 'low-level' manipulation with elements

-- use eq_subst and previous properties to prove 2 examples below:

theorem example_theorem1  : (∀ A B C, A \ (B \ C) = (A \ B) ∪ (A ∩ C)) :=
  fun (A) => fun (B) => fun (C) =>
    let U := (A ∪ B) ∪ C
    let h₁ := And.left (union2sets_subset_prop A B)
    let h₂ := And.right (union2sets_subset_prop A B)
    let g := (And.left (union2sets_subset_prop (A ∪ B) C))
    let f₁ : A ⊆ U := subset_trans A (A ∪ B) ((A ∪ B) ∪ C) h₁ g
    let f₂ : B ⊆ U := subset_trans B (A ∪ B) ((A ∪ B) ∪ C) h₂ g
    let f₃ : C ⊆ U := And.right (union2sets_subset_prop (A ∪ B) C)

    let first := difference_inter_prop U A (B \ C) f₁
    let second : A \ (B \ C) = (A ∩ (U \ (B ∩ (U \ C)))) := eq_subst (fun (x) => (A \ (B \ C) = A ∩ (U \ x))) (B \ C) (B ∩ (U \ C)) (difference_inter_prop U B C f₂)  first
    let third : A \ (B \ C) = A ∩ ((U \ B) ∪ (U \ (U \ C))) := eq_subst (fun (x) => A \ (B \ C) = A ∩ x) (U \ (B ∩ (U \ C))) ((U \ B) ∪ (U \ (U \ C))) (demorgan_inter U B (U \ C)) second
    let fourth : A \ (B \ C) = A ∩ ((U \ B) ∪ C) := eq_subst (fun (x) => A \ (B \ C) = A ∩ ((U \ B) ∪ x)) (U \ (U \ C)) C (double_compl U C f₃) third
    let fifth : A \ (B \ C) = (A ∩ (U \ B)) ∪ (A ∩ C):= eq_subst (fun (x) => A \ (B \ C) = x) (A ∩ ((U \ B) ∪ C)) ((A ∩ (U \ B)) ∪ (A ∩ C)) (inter_union_distribution A (U \ B) C) fourth
    eq_subst (fun (x) => A \ (B \ C) = ((x) ∪ (A ∩ C))) (A ∩ (U \ B)) (A \ B) (eq_symm (A \ B) (A ∩ (U \ B)) (difference_inter_prop U A B f₁)) fifth



theorem example_theorem2 : (∀ A B, A △ B = (A ∪ B) \ (A ∩ B)) :=
  fun (A) => fun (B) =>
    let U := (A ∪ B)
    let P := (fun (x) => (A ∪ B) \ (A ∩ B) = x)
    let h₁ := And.left (union2sets_subset_prop A B)
    let m₁ := And.right (union2sets_subset_prop A B)
    let h₄ : (A ∪ B) \ (A ∩ B) = (A ∪ B) ∩ (U \ (A ∩ B)) := difference_inter_prop U (A ∪ B) (A ∩ B) (subset_refl (A ∪ B))
    let h₅ := inter_union_distribution ((U \ (A ∩ B))) A B
    let h₆ : (A ∪ B) \ (A ∩ B) = (U \ (A ∩ B)) ∩ (A ∪ B) := eq_subst P ((A ∪ B) ∩ (U \ (A ∩ B))) ((U \ (A ∩ B)) ∩ (A ∪ B)) (intersec2_comm (A ∪ B) ((U \ (A ∩ B)))) (h₄)
    let h₇ : (A ∪ B) \ (A ∩ B) = (((U \ (A ∩ B)) ∩ A) ∪ ((U \ (A ∩ B)) ∩ B)) := eq_subst P ((U \ (A ∩ B)) ∩ (A ∪ B)) (((U \ (A ∩ B)) ∩ A) ∪ ((U \ (A ∩ B)) ∩ B)) (h₅) (h₆)
    let h₈ : (A ∪ B) \ (A ∩ B) = (A ∩ (U \ (A ∩ B))) ∪ ((U \ (A ∩ B)) ∩ B) := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = (x) ∪ ((U \ (A ∩ B)) ∩ B))  (((U \ (A ∩ B)) ∩ A)) ((A ∩ (U \ (A ∩ B)))) (intersec2_comm ((U \ (A ∩ B))) A) (h₇)
    let h₉ : (A ∪ B) \ (A ∩ B) = (A ∩ (U \ (A ∩ B))) ∪ (B ∩ (U \ (A ∩ B))) := eq_subst (fun (x) =>  (A ∪ B) \ (A ∩ B) = (A ∩ (U \ (A ∩ B))) ∪ x) ((U \ (A ∩ B)) ∩ B) (B ∩ (U \ (A ∩ B))) (intersec2_comm (U \ (A ∩ B)) B) (h₈)
    let f₁ : (A ∪ B) \ (A ∩ B) = (A ∩ ((U \ A) ∪ (U \ B))) ∪ (B ∩ (U \ (A ∩ B)))
     := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = (A ∩ x) ∪ (B ∩ (U \ (A ∩ B)))) (U \ (A ∩ B)) ((U \ A) ∪ (U \ B)) (demorgan_inter U A B) (h₉)
    let f₂ : (A ∪ B) \ (A ∩ B) = (A ∩ ((U \ A) ∪ (U \ B))) ∪ (B ∩ ((U \ A) ∪ (U \ B)))
      := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = (A ∩ ((U \ A) ∪ (U \ B))) ∪ (B ∩ x)) (U \ (A ∩ B)) ((U \ A) ∪ (U \ B)) (demorgan_inter U A B) (f₁)
    let f₃ : (A ∪ B) \ (A ∩ B) = ((A ∩ (U \ A)) ∪ (A ∩ (U \ B))) ∪ (B ∩ ((U \ A) ∪ (U \ B)))
      := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = x ∪ (B ∩ ((U \ A) ∪ (U \ B)))) (A ∩ ((U \ A) ∪ (U \ B))) ((A ∩ (U \ A)) ∪ (A ∩ (U \ B))) (inter_union_distribution A (U \ A) (U \ B)) (f₂)
    let f₄ : (A ∪ B) \ (A ∩ B) = ((A ∩ (U \ A)) ∪ (A ∩ (U \ B))) ∪ ((B ∩ (U \ A)) ∪ (B ∩ (U \ B)))
      := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = ((A ∩ (U \ A)) ∪ (A ∩ (U \ B))) ∪ x) (B ∩ ((U \ A) ∪ (U \ B))) ((B ∩ (U \ A)) ∪ (B ∩ (U \ B))) (inter_union_distribution B (U \ A) (U \ B)) (f₃)
    let f₅ : (A ∪ B) \ (A ∩ B) = (∅ ∪ (A ∩ (U \ B))) ∪ ((B ∩ (U \ A)) ∪ (B ∩ (U \ B)))
      := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = (x ∪ (A ∩ (U \ B))) ∪ ((B ∩ (U \ A)) ∪ (B ∩ (U \ B)))) (A ∩ (U \ A)) ∅ (inter_to_empty U A) (f₄)
    let f₆ : (A ∪ B) \ (A ∩ B) = (∅ ∪ (A ∩ (U \ B))) ∪ ((B ∩ (U \ A)) ∪ ∅)
      := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = (∅ ∪ (A ∩ (U \ B))) ∪ ((B ∩ (U \ A)) ∪ x)) (B ∩ (U \ B)) ∅ (inter_to_empty U B) (f₅)
    let fx : (A ∩ (U \ B)) ∪ ∅ = A ∩ (U \ B) := union2_empty (A ∩ (U \ B))
    let fy : ∅ ∪ (A ∩ (U \ B)) = A ∩ (U \ B) := eq_subst (fun (x) => ∅ ∪ (A ∩ (U \ B)) = x) ((A ∩ (U \ B)) ∪ ∅) (A ∩ (U \ B)) (fx) (union2_comm ∅ (A ∩ (U \ B)))
    let f₇ : (A ∪ B) \ (A ∩ B) = (A ∩ (U \ B)) ∪ ((B ∩ (U \ A)) ∪ ∅)
      := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = x ∪ ((B ∩ (U \ A)) ∪ ∅)) (∅ ∪ (A ∩ (U \ B))) (A ∩ (U \ B)) (fy) (f₆)
    let f₈ : (A ∪ B) \ (A ∩ B) = (A ∩ (U \ B)) ∪ ((B ∩ (U \ A)))
      := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = (A ∩ (U \ B)) ∪ x) ((B ∩ (U \ A)) ∪ ∅) ((B ∩ (U \ A))) (union2_empty (B ∩ (U \ A))) (f₇)
    let f₉ : (A ∪ B) \ (A ∩ B) = (A \ B) ∪ (B ∩ (U \ A))
      := eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = x ∪ (B ∩ (U \ A))) (A ∩ (U \ B))  (A \ B) (Eq.symm (difference_inter_prop U A B h₁)) (f₈)
    let s : (A ∪ B) \ (A ∩ B) = (A △ B) :=
    eq_subst (fun (x) => (A ∪ B) \ (A ∩ B) = (A \ B) ∪ x) (B ∩ (U \ A)) (B \ A) (Eq.symm (difference_inter_prop U B A m₁)) (f₉)
    Eq.symm s



theorem neg_mon_diff : ∀ A B C, (A ⊆ B) → (C \ B) ⊆ (C \ A) :=
  fun (A B C) =>
    fun (hAB : (A ⊆ B)) =>
      fun (x) =>
        fun (hx : (x ∈ (C \ B))) =>
          let u := Iff.mp (difference_prop C B x) hx
          Iff.mpr (difference_prop C A x) (
            And.intro (And.left u) (
              fun (hx : x ∈ A) =>
                And.right u (
                  hAB x (hx)
                )
            )
          )
