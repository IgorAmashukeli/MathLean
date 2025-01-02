import «Header»




def is_semilattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ x y ∈ (setPO(𝓐)); (𝓐 InfmExi ({x, y})))
syntax "SemiLatt" term : term
macro_rules
| `(SemiLatt $𝓐) => `(is_semilattice $𝓐)



def is_lattice (𝓐 : Set) : Prop := (PartOrd 𝓐) ∧
(∀ x y ∈ (setPO(𝓐)); (𝓐 SuprExi ({x, y})) ∧ (𝓐 InfmExi ({x, y})))
syntax "Latt" term : term
macro_rules
| `(Latt $𝓐:term) => `(is_lattice $𝓐)


theorem latt_inv : ∀ 𝓐, (PartOrd 𝓐) → ((Latt 𝓐) ↔ (Latt (invPO 𝓐))) :=
  fun (𝓐 h𝓐) =>
    Iff.intro
    (
      fun (hlatt) =>
        let u₁ := And.left hlatt
        let u₂ := inv_is_PO 𝓐 u₁
        And.intro (u₂) (
          fun (x hx y hy) =>
            let hx₁ := eq_subst (fun (t) => x ∈ t) (setPO(invPO 𝓐)) (setPO(𝓐)) (setPO_is_setPO setPO(𝓐) (≻(𝓐)) (≽(𝓐))) hx
            let hy₁ := eq_subst (fun (t) => y ∈ t) (setPO(invPO 𝓐)) (setPO(𝓐)) (setPO_is_setPO setPO(𝓐) (≻(𝓐)) (≽(𝓐))) hy
            let u₃ := And.right hlatt x hx₁ y hy₁
            Exists.elim (And.left u₃) (
              fun (sup hsup) =>
                Exists.elim (And.right u₃) (
                  fun (inf hinf) =>
                    And.intro (Exists.intro inf (Iff.mp (inv_is_inf_sup 𝓐 {x, y} h𝓐 inf) (hinf))) (
                      Exists.intro sup (Iff.mp (inv_is_sup_inf 𝓐 {x, y} h𝓐 sup) (hsup))
                    )
                )
            )

        )
    )
    (
      fun (hlattinv) =>
        And.intro h𝓐 (
          fun (x hx y hy) =>
            let hx₁ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐)) (setPO(invPO 𝓐)) (Eq.symm (setPO_is_setPO setPO(𝓐) (≻(𝓐)) (≽(𝓐)))) hx
            let hy₁ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐)) (setPO(invPO 𝓐)) (Eq.symm (setPO_is_setPO setPO(𝓐) (≻(𝓐)) (≽(𝓐)))) hy
            let u₃ := And.right hlattinv x hx₁ y hy₁
            Exists.elim (And.left u₃) (
              fun (sup hsup) =>
                Exists.elim (And.right u₃) (
                  fun (inf hinf) =>
                    And.intro (Exists.intro inf (Iff.mpr (inv_is_sup_inf 𝓐 {x, y} h𝓐 inf) (hinf))) (
                      Exists.intro sup (Iff.mpr (inv_is_inf_sup 𝓐 {x, y} h𝓐 sup) (hsup))
                    )
                )
            )
        )
    )


theorem latt_is_semilatt : ∀ 𝓐, (Latt 𝓐) → (SemiLatt 𝓐) :=
  fun (_ h𝓐) =>
    And.intro (And.left h𝓐) (fun (x hx y hy) => (And.right ((And.right h𝓐) x hx y hy)))


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
                              low_upp_low_is_upp 𝓐 X (hPart) hX
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
                                upp_low_upp_is_low 𝓐 X (hPart) hX
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



theorem compllatt_inv : ∀ 𝓐, (PartOrd 𝓐) → ((CompLatt 𝓐) ↔ (CompLatt (invPO 𝓐))) :=
  fun (𝓐 h𝓐) =>
    Iff.intro
    (
      fun (hcomplatt) =>
        let u₁ := inv_is_PO 𝓐 h𝓐
        And.intro u₁ (
          fun (X hX) =>
            let u₂ := setPO_is_setPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
            let hsub := eq_subst (fun (t) => X ⊆ t) (setPO(invPO(𝓐))) (setPO(𝓐)) (u₂) (hX)
            let pr₁ := Iff.mp (compl_latt_inf_crit 𝓐 h𝓐) hcomplatt X hsub
            Exists.elim (pr₁) (
              fun (inf hinf) =>
                Exists.intro inf (Iff.mp (inv_is_inf_sup 𝓐 X h𝓐 inf) (hinf))
            )

        )
    )
    (
      fun (hcomplattinv) =>
        And.intro h𝓐 (
          fun (X hX) =>
          let u₂ := setPO_is_setPO (setPO(𝓐)) (≻(𝓐)) (≽(𝓐))
          let hsub := eq_subst (fun (t) => X ⊆ t) (setPO(𝓐)) (setPO(invPO(𝓐))) (Eq.symm u₂) (hX)
          let pr₁ := Iff.mp (compl_latt_inf_crit (invPO 𝓐) (And.left hcomplattinv)) hcomplattinv X hsub
          Exists.elim (pr₁) (
            fun (inf hinf) =>
              Exists.intro inf (Iff.mpr (inv_is_sup_inf 𝓐 X h𝓐 inf) (hinf))
          )
        )
    )


def is_operation (A f : Set) : Prop := f Fun (A × A) To A
def is_impodent_op (A f : Set) : Prop := ∀ x ∈ A; f⦅x; x⦆ = x
def is_commut_op (A f : Set) : Prop := ∀ x y ∈ A; f⦅x; y⦆ = f⦅y ; x⦆
def is_assoc_op (A f : Set) : Prop := ∀ x y z ∈ A; f⦅f⦅x; y⦆; z⦆ = f⦅x; f⦅y;z⦆⦆
def is_semilattfunc (A f : Set) : Prop := (f Fun (A × A) To A) ∧ is_impodent_op A f ∧ is_commut_op A f ∧ is_assoc_op A f
syntax term "SemLatFunOn" term : term
macro_rules
| `($f SemLatFunOn $A) => `(is_semilattfunc $A $f)

noncomputable def leq_semifunclatt (A f) := {(x, y) ∈ A × A | f⦅x; y⦆ = x}
syntax term "LSFL" term : term
macro_rules
| `($f LSFL $A) => `(leq_semifunclatt $A $f)


theorem leq_in : ∀ x y A f, ((x . (f LSFL A) . y)) ↔ ((x ∈ A ∧ y ∈ A) ∧ (f⦅x; y⦆ = x)) :=
  fun (x y A f) =>
    bin_spec_is_spec (fun (x) => fun (y) => f⦅x; y⦆ = x) A A x y


noncomputable def fun_semilat (A f) := A NoNStrIntro (f LSFL A)
syntax term "SemLatF" term : term
macro_rules
| `($A SemLatF $f) => `(fun_semilat $A $f)

theorem semilatt_op : ∀ A f, (A ≠ ∅) → (f SemLatFunOn A) → (SemiLatt (A SemLatF f)) ∧ (∀ x y ∈ A; f⦅x; y⦆ = (A SemLatF f) Infm {x, y}) :=
  fun (A f hA hfA) =>
    let 𝓐 := A SemLatF f
    let R₂ := f LSFL A
    let lesseq := lesseqPO_is_lesseqPO A (str A R₂) R₂
    let setpo := setPO_is_setPO A (str A R₂) R₂

    let u₁ : PartOrd 𝓐 := po_from_non_str_is_po A R₂ hA (

      And.intro (bin_spec_is_binAB (fun (x) => fun (y) => f⦅x; y⦆ = x) A A)
      (And.intro (
        fun (x hx) =>

          Iff.mpr (leq_in x x A f) (
            And.intro (And.intro hx hx) (And.left (And.right hfA) x hx)
          )
      ) (And.intro (
        fun (x y hxy) =>
          let u₁ := Iff.mp (leq_in x y A f) (And.left hxy)
          let u₂ := Iff.mp (leq_in y x A f) (And.right hxy)
          let u₀ := And.left (And.right (And.right hfA)) x (And.left (And.left u₁)) y (And.right (And.left u₁))
          Eq.trans (Eq.symm (And.right u₁)) (Eq.trans (u₀) (And.right u₂))

      ) (
        fun (x y z hxyz) =>
          let u₁ := Iff.mp (leq_in x y A f) (And.left hxyz)
          let u₂ := Iff.mp (leq_in y z A f) (And.right hxyz)
          let u₃ := eq_subst (fun (t) => f⦅x; z⦆ = f⦅t; z⦆) x (f⦅x; y⦆) (Eq.symm (And.right u₁)) (Eq.refl (f⦅x; z⦆))
          let u₄ := And.right (And.right (And.right hfA)) x (And.left (And.left u₁)) y (And.right (And.left u₁)) z (And.right (And.left u₂))
          let u₅ := eq_subst (fun (t) => f⦅f⦅x; y⦆; z⦆ = f⦅x; t⦆) (f⦅y; z⦆) y (And.right u₂) (u₄)


          let u₆ := Eq.trans (u₃) (Eq.trans u₅ (And.right u₁))
          Iff.mpr (leq_in x z A f) (
            And.intro (And.intro (And.left (And.left u₁)) (And.right (And.left u₂))) (u₆)
          )
      ))

      )
    )

    let u₂ : ∀ x y ∈ A; is_infimum 𝓐 {x, y} (f⦅x; y⦆) :=
      fun (x hx y hy) =>
        let X := {x, y}
        let m := (f⦅x; y⦆)
        let m_in := val_in_B f (A × A) A (And.left hfA) (x, y) (Iff.mpr (cartesian_product_pair_prop A A x y) (And.intro (hx) (hy)))
        let m_in₂ : m ∈ setPO(𝓐) := eq_subst (fun (t) => f⦅x; y⦆ ∈ t) A (setPO(𝓐)) (Eq.symm (setpo)) (m_in)
        And.intro (Iff.mpr (low_bou_set_is_low_bou 𝓐 X m) (
          And.intro (m_in₂) (
            fun (s hs) =>
              Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair x y s) hs)
              (
                fun (hsx) =>
                  eq_subst (fun (t) => (m . ≼(𝓐) . t)) (x) (s) (Eq.symm hsx) (
                    eq_subst (fun (t) => (m . t . x)) (R₂) (≼(𝓐)) (Eq.symm (lesseq)) (
                      Iff.mpr (leq_in m x A f) (
                        And.intro (And.intro (m_in) (hx)) (
                          let u₀ := And.left (And.right (And.right hfA)) x hx y hy
                          let u₀₁ := eq_subst (fun (t) => f⦅m; x⦆ = f⦅t; x⦆) (f⦅x; y⦆) (f⦅y; x⦆) (u₀) (Eq.refl (f⦅m; x⦆))
                          let u₀₂ := And.right (And.right (And.right hfA)) y hy x hx x hx
                          let u₀₃ := Eq.trans u₀₁ u₀₂
                          let u₀₄ := eq_subst (fun (t) => f⦅m; x⦆  = f⦅y; t⦆) (f⦅x; x⦆) x (And.left (And.right hfA) x hx) (u₀₃)
                          Eq.trans u₀₄ (And.left (And.right (And.right hfA)) y hy x hx)
                        )
                      )
                    )

                  )
              )
              (
                fun (hsy) =>
                  eq_subst (fun (t) => (m . ≼(𝓐) . t)) (y) (s) (Eq.symm hsy) (
                    eq_subst (fun (t) => (m . t . y)) (R₂) (≼(𝓐)) (Eq.symm (lesseq)) (
                      Iff.mpr (leq_in m y A f) (
                        And.intro (And.intro m_in hy) (
                          let u₀ := And.right (And.right (And.right hfA)) x hx y hy y hy
                          eq_subst (fun (t) => f⦅m; y⦆ = f⦅x; t⦆) (f⦅y; y⦆) y (And.left (And.right hfA) y hy) (u₀)
                        )
                      )
                    )

                  )
              )

          )
        )) (
          fun (s hs) =>
            let u₁₀ := Iff.mp (low_bou_set_is_low_bou 𝓐 X s) hs
            let u₁₁ := eq_subst (fun (t) => s ∈ t) (setPO(𝓐)) A (setpo) (And.left u₁₀)
            let m := f⦅x; y⦆
            let u₁₂ := And.right (u₁₀) x (left_unordered_pair x y)
            let u₁₃ := eq_subst (fun (t) => (s . t . x)) (≼(𝓐)) (R₂) lesseq u₁₂
            let u₁₄ := Iff.mp (leq_in s x A f) u₁₃
            let u₁₅ := And.right (u₁₀) y (right_unordered_pair x y)
            let u₁₆ := eq_subst (fun (t) => (s . t . y)) (≼(𝓐)) (R₂) lesseq u₁₅
            let u₁₇ := Iff.mp (leq_in s y A f) u₁₆


            eq_subst (fun (t) => (s . t . m)) (R₂) (≼(𝓐)) (Eq.symm (lesseq)) (
              Iff.mpr (leq_in s m A f) (
                And.intro (And.intro (u₁₁) (m_in)) (

                  let u₁₈ := Eq.symm (And.right (And.right (And.right hfA)) s u₁₁ x hx y hy)
                  let u₁₉ := eq_subst (fun (t) => f⦅s ; m⦆ = f⦅t; y⦆) (f⦅s; x⦆) (s) (And.right u₁₄) (u₁₈)
                  Eq.trans u₁₉ (And.right u₁₇)
                )
              )
            )
        )

    let u₃ : ∀ x y ∈ A; 𝓐 InfmExi {x, y} := fun (x hx y hy) => Exists.intro (f⦅x; y⦆) (u₂ x hx y hy)

    let u₄ : ∀ x y ∈ setPO(𝓐); 𝓐 InfmExi {x, y} := eq_subst (fun (t) => ∀ x y ∈ t; (𝓐) InfmExi {x, y}) (A) (setPO(𝓐)) (
      Eq.symm (setPO_is_setPO (A) (str A (leq_semifunclatt A f)) (leq_semifunclatt A f))
    ) (u₃)

    let u₅ : (SemiLatt (𝓐)) := And.intro (u₁) (u₄)

    let u₆ : ∀ x y ∈ A; f⦅x; y⦆ = (A SemLatF f) Infm {x, y} := fun (x hx y hy) => Iff.mp (infm_po_crit 𝓐 {x, y} (f⦅x; y⦆) u₁ (u₃ x hx y hy)) (
      u₂ x hx y hy
    )

    And.intro u₅ u₆


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


theorem latt_as_semilatts : ∀ 𝓐, (Latt 𝓐) ↔ ((SemiLatt 𝓐) ∧ (SemiLatt (invPO 𝓐))) :=
  fun (𝓐) =>
    Iff.intro
    (
      fun (hlatt) =>
        let u₁ := latt_is_semilatt 𝓐 hlatt
        let u₂ := Iff.mp (latt_inv 𝓐 (And.left hlatt)) hlatt
        let u₃ := latt_is_semilatt (invPO 𝓐) u₂
        And.intro (u₁) (u₃)
    )
    (
      fun (hsemiinv) =>
        let u₁ := And.right (And.left hsemiinv)
        let u₂ := And.right (And.right hsemiinv)
        And.intro (And.left (And.left hsemiinv)) (
          fun (x hx y hy) =>
            let hx₁ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐)) (setPO(invPO 𝓐)) (Eq.symm (setPO_is_setPO setPO(𝓐) (≻(𝓐)) (≽(𝓐)))) hx
            let hy₁ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐)) (setPO(invPO 𝓐)) (Eq.symm (setPO_is_setPO setPO(𝓐) (≻(𝓐)) (≽(𝓐)))) hy
            let u₃ := u₂ x hx₁ y hy₁

            Exists.elim u₃ (
              fun (inf hinf) =>
                let u₄ := Iff.mpr (inv_is_sup_inf 𝓐 {x, y} (And.left (And.left (hsemiinv))) inf) (hinf)
                And.intro (Exists.intro inf u₄) (u₁ x hx y hy)
            )

        )
    )



theorem sum_semilatt : ∀ 𝓐 𝓑, (SemiLatt 𝓐) → (SemiLatt 𝓑) → (SemiLatt (𝓐 P⨁O 𝓑)) :=
  fun (𝓐 𝓑 h𝓐 h𝓑) =>
    let u₁ := sum_is_PO 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑)
    let A := setPO(𝓐)
    let B := setPO(𝓑)
    let R₁ := le_disj2 𝓐 𝓑
    let R₂ := (nonstr (setPO(𝓐) ⊔ setPO(𝓑)) R₁)
    let u₂ := setPO_is_setPO (A ⊔ B) R₁ R₂
    And.intro (u₁) (
      fun (x hx y hy) =>
        let u₀ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 P⨁O 𝓑)) (A ⊔ B) (u₂) (hx)
        let u₀₁ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 P⨁O 𝓑)) (A ⊔ B) (u₂) (hy)
        let u₁ := disj2_xAB_in A B x u₀
        let u₂ := disj2_xAB_in A B y u₀₁
        Or.elim u₁
        (
          fun (hxA) =>
            Or.elim u₂
            (
              fun (hyA) =>
                let u₃ := And.right h𝓐 (π₁ x) (And.left hxA) (π₁ y) (And.left hyA)
                Exists.elim u₃
                (
                  fun (inf hinf) =>
                    Exists.intro (inf, l2) (
                      And.intro (sorry) (sorry)
                    )
                )
            )
            (
              fun (hyB) =>
                sorry
            )
        )
        (
          fun (hxB) =>
            Or.elim u₂
            (
              fun (hyA) =>
                sorry
            )
            (
              fun (hyB) =>
                sorry
            )
        )
    )


theorem sum_latt : ∀ 𝓐 𝓑, (Latt 𝓐) → (Latt 𝓑) → (Latt (𝓐 P⨁O 𝓑)) :=
  fun (𝓐 𝓑 h𝓐 h𝓑) =>
    let u₁ := sum_is_PO 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑)
    And.intro (u₁) (
      fun (x hx y hy) =>
        sorry
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


                      Or.elim (Classical.em (X = ∅))
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

                          let v₅ := eq_subst (fun (t) => is_lowest (𝓐 SubsPO (⟦ a ; b ⟧ of 𝓐)) t a) (
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


theorem Knaster_Tarski_lemma₁ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (𝓐 GrtExi (f FixOn 𝓐)) :=
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



theorem Knaster_Tarski_lemma₂ : ∀ 𝓐 f, (CompLatt 𝓐) → (f MotFunRelOn 𝓐) → (𝓐 LowExi (f FixOn 𝓐)) :=
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
              fun (hmaxel : is_greatest 𝓐 (f FixOn 𝓐) maxel) =>
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
                              fun (hr : is_lowest (RLat) (spec_f FixOn RLat) r) =>

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

                                    let hr_N := eq_subst (fun (t) => is_lowest RLat t r) M N (u₁₈) (hr)
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

                                    let hr_N₂ : is_lowest Sub (Sub ▴ X) r := And.intro hr_N₀ hr_N₁

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


theorem sum_is_LO : ∀ 𝓐 𝓑, (LinOrd 𝓐) → (LinOrd 𝓑) → (LinOrd (𝓐 P⨁O 𝓑)) :=
  fun (𝓐 𝓑 h𝓐 h𝓑) =>
    let A := (setPO(𝓐) ⊔ setPO(𝓑))
    let R₁ := le_disj2 𝓐 𝓑
    let R₂ := (nonstr (setPO(𝓐) ⊔ setPO(𝓑)) R₁)
    let u₁ := sum_is_PO 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑)
    And.intro (u₁) (
      fun (x hx y hy) =>
        let u₂ := setPO_is_setPO (A) R₁ R₂
        let u₃ := eq_subst (fun (t) => x ∈ t) (setPO(𝓐 P⨁O 𝓑)) A (u₂) (hx)
        let u₄ := disj2_xAB_in (setPO(𝓐)) (setPO(𝓑)) x u₃
        let u₅ := eq_subst (fun (t) => y ∈ t) (setPO(𝓐 P⨁O 𝓑)) A (u₂) (hy)
        let u₆ := disj2_xAB_in (setPO(𝓐)) (setPO(𝓑)) y u₅
        Or.elim u₄
        (
          fun (hxA) =>
            Or.elim u₆
            (
              fun (hyA) =>
                let u₇ := And.right h𝓐 (π₁ x) (And.left hxA) (π₁ y) (And.left hyA)
                Or.elim u₇
                (
                  fun (hxy) =>
                    Or.inl (
                      Iff.mpr (sum_PO_lesseq 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑) x hx y hy) (
                        Or.inl (
                          And.intro (And.right hxA) (And.intro (And.right hyA) (hxy))
                        )
                      )
                    )
                )
                (
                  fun (hyx) =>
                    Or.inr (
                      Iff.mpr (sum_PO_lesseq 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑) y hy x hx) (
                          Or.inl (
                              And.intro (And.right hyA) (And.intro (And.right hxA) (hyx))
                          )
                      )
                    )
                )
            )
            (
              fun (hyB) =>
                Or.inl (
                  Iff.mpr (sum_PO_lesseq 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑) x hx y hy) (
                    Or.inr (
                      Or.inr (
                        And.intro (And.left hxA) (And.intro (And.left hyB) (And.intro (And.right hxA) (And.right hyB)))
                      )
                    )
                  )
                )
            )
        )
        (
          fun (hxB) =>
            Or.elim u₆
            (
              fun (hyA) =>
                Or.inr (
                  Iff.mpr (sum_PO_lesseq 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑) y hy x hx) (
                    Or.inr (
                      Or.inr (
                        And.intro (And.left hyA) (And.intro (And.left hxB) (And.intro (And.right hyA) (And.right hxB)))
                      )
                    )
                  )
                )
            )
            (
              fun (hyB) =>
                let u₇ := And.right h𝓑 (π₁ x) (And.left hxB) (π₁ y) (And.left hyB)
                Or.elim u₇
                (
                  fun (hxy) =>
                    Or.inl (
                      Iff.mpr (sum_PO_lesseq 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑) x hx y hy) (
                        Or.inr (Or.inl (
                            And.intro (And.right hxB) (And.intro (And.right hyB) (hxy))
                          )
                        )
                      )
                    )
                )
                (
                  fun (hyx) =>
                    Or.inr (
                      Iff.mpr (sum_PO_lesseq 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑) y hy x hx) (
                        Or.inr ( Or.inl (
                              And.intro (And.right hyB) (And.intro (And.right hxB) (hyx))
                          )
                        )
                      )
                    )
                )
            )
        )
    )


theorem linmin_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_minimal 𝓐 X x) ↔ (is_lowest 𝓐 X x)) :=
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



theorem linmax_al_um : ∀ 𝓐 X x, (LinOrd 𝓐) → (X ⊆ setPO(𝓐)) → ((is_maximal 𝓐 X x) ↔ (is_greatest 𝓐 X x)):=
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


theorem lin_partmin_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 LowExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_minimal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_minimal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimal 𝓐 (B _ i) y} x)) :=
    fun (𝓐 B I x) =>
      fun (h𝓐 : (LinOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hmin : (∀ i ∈ I; (𝓐 LowExi (B _ i)))) =>
            fun (hset : (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))) =>
              let u₀ := fun (r) =>
                fun (hr : r ∈ (⋃[i in I] B at i)) =>
                  let u₁ := Iff.mp (indexed_union_is_union B I (hBI) r) hr
                  Exists.elim u₁ (
                    fun (i) =>
                      fun (hi : i ∈ I ∧ r ∈ (B _ i)) =>
                        hset i (And.left hi) r (And.right hi)
                  )

              let T := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_lowest 𝓐 (B _ i) y}
              let S := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_minimal 𝓐 (B _ i) y}

              let TS : T ⊆ S:=
                fun (s) =>
                  fun (hs : s ∈ T) =>
                    let a := (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_lowest 𝓐 (B _ i) P) (setPO(𝓐)) s) hs)
                    Exists.elim (And.right a) (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ is_lowest 𝓐 (B _ i) s) =>
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
                          Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_lowest 𝓐 (B _ i) P) (setPO(𝓐)) s) (
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




              let u₁ := specification_set_subset (fun (P) => ∃ i ∈ I; is_lowest 𝓐 (B _ i) P) (setPO(𝓐))

              let u₂ := linmin_al_um 𝓐 (⋃[i in I] B at i) x (h𝓐) (u₀)
              let u₃ := linmin_al_um 𝓐 ({y ∈ setPO(𝓐) | ∃ i ∈ I; is_lowest 𝓐 (B _ i) y}) x (h𝓐) (u₁)


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



theorem lin_partmax_al_un_prop : ∀ 𝓐 B I x, (LinOrd 𝓐) → (B Indx I) → (∀ i ∈ I; (𝓐 GrtExi (B _ i))) →
 (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐)) → ((is_maximal 𝓐 (⋃[i in I] B at i) x) ↔ (
  is_maximal 𝓐 {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximal 𝓐 (B _ i) y} x)) :=
    fun (𝓐 B I x) =>
      fun (h𝓐 : (LinOrd 𝓐)) =>
        fun (hBI : (B Indx I)) =>
          fun (hmin : (∀ i ∈ I; (𝓐 GrtExi (B _ i)))) =>
            fun (hset : (∀ i ∈ I; (B _ i) ⊆ setPO(𝓐))) =>
              let u₀ := fun (r) =>
                fun (hr : r ∈ (⋃[i in I] B at i)) =>
                  let u₁ := Iff.mp (indexed_union_is_union B I (hBI) r) hr
                  Exists.elim u₁ (
                    fun (i) =>
                      fun (hi : i ∈ I ∧ r ∈ (B _ i)) =>
                        hset i (And.left hi) r (And.right hi)
                  )

              let T := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_greatest 𝓐 (B _ i) y}
              let S := {y ∈ setPO(𝓐) | ∃ i ∈ I; is_maximal 𝓐 (B _ i) y}

              let TS : T ⊆ S:=
                fun (s) =>
                  fun (hs : s ∈ T) =>
                    let a := (Iff.mp (spec_is_spec (fun (P) => ∃ i ∈ I; is_greatest 𝓐 (B _ i) P) (setPO(𝓐)) s) hs)
                    Exists.elim (And.right a) (
                      fun (i) =>
                        fun (hi : i ∈ I ∧ is_greatest 𝓐 (B _ i) s) =>
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
                          Iff.mpr (spec_is_spec (fun (P) => ∃ i ∈ I; is_greatest 𝓐 (B _ i) P) (setPO(𝓐)) s) (
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




              let u₁ := specification_set_subset (fun (P) => ∃ i ∈ I; is_greatest 𝓐 (B _ i) P) (setPO(𝓐))

              let u₂ := linmax_al_um 𝓐 (⋃[i in I] B at i) x (h𝓐) (u₀)
              let u₃ := linmax_al_um 𝓐 ({y ∈ setPO(𝓐) | ∃ i ∈ I; is_greatest 𝓐 (B _ i) y}) x (h𝓐) (u₁)


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
                max_um_is_sup 𝓐 {x, y} y (And.left h𝓐) (u₀) (u₁)



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
                min_um_is_inf 𝓐 {x, y} x (And.left h𝓐) (u₀) (u₁)



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

def is_well_found_order 𝓐 := (PartOrd 𝓐) ∧ (∀ X, ( (X ⊆ setPO(𝓐)) →  (X ≠ ∅) → (𝓐 LowExi X)))
syntax "WellFoundOrd" term : term
macro_rules
| `(WellFoundOrd $𝓐) => `(is_well_found_order $𝓐)

def is_well_order 𝓐 := (LinOrd 𝓐) ∧ ∀ X, (X ⊆ setPO(𝓐)) → (X ≠ ∅) → (𝓐 LowExi X)
syntax "WellOrd" term : term
macro_rules
| `(WellOrd $𝓐) => `(is_well_order $𝓐)


theorem wellord_wellfoundcrit : ∀ 𝓐, (WellOrd 𝓐) ↔ ((LinOrd 𝓐) ∧ (WellFoundOrd 𝓐)) :=
  fun (_) =>
    Iff.intro
    (
      fun (hwell) =>
        And.intro (And.left hwell) (And.intro (And.left (And.left hwell)) (And.right hwell))
    )
    (
      fun (hliwefo) =>
        And.intro (And.left hliwefo) (And.right (And.right hliwefo))
    )


theorem well_found : ∀ 𝓐 𝓑, (WellFoundOrd 𝓐) → (WellFoundOrd 𝓑) → (WellFoundOrd (𝓐 P⨁O 𝓑)) := sorry


theorem well_ord : ∀ 𝓐 𝓑, (WellOrd 𝓐) → (WellOrd 𝓑) → (WellOrd (𝓐 P⨁O 𝓑)) :=
  fun (𝓐 𝓑 h𝓐 h𝓑) =>
    let u₁ := sum_is_LO 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑)
    let u₂ := Iff.mp (wellord_wellfoundcrit 𝓐) h𝓐
    let u₃ := Iff.mp (wellord_wellfoundcrit 𝓑) h𝓑
    Iff.mpr (wellord_wellfoundcrit (𝓐 P⨁O 𝓑)) (And.intro (u₁) (well_found 𝓐 𝓑 (And.right u₂) (And.right u₃)))



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


theorem antichain : ∀ 𝓐 𝓑 A B, (𝓐 AntiChain A) → (𝓑 AntiChain B) → ((𝓐 Cart2CordPO 𝓑) AntiChain (A × B)) :=
  fun (𝓐 𝓑 A B) =>
    fun (h𝓐 : (𝓐 AntiChain A)) =>
      fun (h𝓑 : (𝓑 AntiChain B)) =>
        let L₀ := (≼(𝓐 Cart2CordPO 𝓑))
        let L₂ := (le_cart 𝓐 𝓑)
        let L₃ := (leq_cart 𝓐 𝓑)
        let S := setPO(𝓐) × setPO(𝓑)
        let cart_po_po := cart_PO_PO 𝓐 𝓑 (And.left h𝓐) (And.left h𝓑)
        let ABsub₀ := cartesian_product_subset A B (setPO(𝓐)) (setPO(𝓑)) (And.left (And.right h𝓐)) (And.left (And.right h𝓑))
        let ABsub := eq_subst (fun (t) => (A × B) ⊆ t) (setPO(𝓐) × setPO(𝓑)) (setPO(𝓐 Cart2CordPO 𝓑)) (Eq.symm (setPO_is_setPO (setPO(𝓐) × setPO(𝓑))
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

                      fun (hxy : (x, y) ∈ ≺(𝓐 Cart2CordPO 𝓑)) =>
                        let u₁ := Iff.mp (And.left (part_ord_pair_prop (𝓐 Cart2CordPO 𝓑) cart_po_po x hxcart y hycart)) hxy
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
                      fun (hyx : (x, y) ∈ ≻(𝓐 Cart2CordPO 𝓑)) =>
                        let hxy : (y, x) ∈ ≺(𝓐 Cart2CordPO 𝓑) := Iff.mpr (po_less_more (𝓐 Cart2CordPO 𝓑) (cart_po_po) y x) (hyx)
                        let u₁ := Iff.mp (And.left (part_ord_pair_prop (𝓐 Cart2CordPO 𝓑) cart_po_po y hycart x hxcart)) hxy
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
