import «Header»


noncomputable def ordered_pair_set (a b : Set) := {{a}, {a, b}}
notation (priority := high) "(" a₁ ", " a₂ ")" => ordered_pair_set a₁ a₂


theorem ordered_pair_set_prop : ∀ a b c d, (a, b) = (c, d) ↔ (a = c ∧ b = d) :=
  fun (a) => fun(b) => fun(c) => fun(d) =>
    Iff.intro
    (
      fun (h : (a, b) = (c, d)) =>
        let first: {a} ∈ {{a}, {a, b}} := left_unordered_pair {a} {a, b}
        let second: {a} ∈ {{c}, {c, d}} := eq_subst (fun (x) => {a} ∈ x) (a, b) (c, d) h first
        let third: {a} = {c} ∨ {a} = {c, d} := Iff.mp (unordered_pair_set_is_unordered_pair {c} {c, d} {a}) second
        let ac : a = c
        := Or.elim (third) (
          fun (g : {a} = {c}) =>
            let fourth: c ∈ {c} := elem_in_singl c
            let fifth: c ∈ {a} := eq_subst (fun (x) => c ∈ x) {c} {a} (Eq.symm g) fourth
            Eq.symm (in_singl_elem a c fifth)
        ) (
          fun (g : {a} = {c, d}) =>
            let fourth: c ∈ {c, d} := left_unordered_pair c d
            let fifth: c ∈ {a} := eq_subst (fun (x) => c ∈ x) {c, d} {a} (Eq.symm g) fourth
            Eq.symm (in_singl_elem a c fifth)

        )

        let fourth: {a, b} ∈ {{a}, {a, b}} := right_unordered_pair {a} {a, b}
        let fifth: {a, b} ∈ {{c}, {c, d}} := eq_subst (fun (x) => {a, b} ∈ x) (a, b) (c, d) h fourth
        let sixth: {a, b} = {c} ∨ {a, b} = {c, d} :=Iff.mp (unordered_pair_set_is_unordered_pair {c} {c, d} {a, b}) fifth
        Or.elim (sixth) (
            fun (g : {a, b} = {c}) =>
              let seventh : b ∈ {a, b} := right_unordered_pair a b
              let eighth: b ∈ {c} := eq_subst (fun (x) => b ∈ x) {a, b} {c} g seventh
              let nineth: b = c := in_singl_elem c b eighth
              let tenth: {c, d} ∈ {{c}, {c, d}} := right_unordered_pair {c} {c, d}
              let eleventh: {c, d} ∈ {{a}, {a, b}} := eq_subst (fun (x) => {c, d} ∈ x) (c, d) (a, b) (Eq.symm h) tenth
              let twelve: {c, d} = {a} ∨ {c, d} = {a, b} := Iff.mp (unordered_pair_set_is_unordered_pair {a} {a, b} {c, d}) eleventh
              Or.elim (twelve)
              (
                fun (s : {c, d} = {a}) =>
                  let y₁ : d ∈ {c, d} := right_unordered_pair c d
                  let y₂ : d ∈ {a} := eq_subst (fun (x) => d ∈ x) {c, d} {a} s y₁
                  let y₃ : d = a := in_singl_elem a d y₂
                  let y₄ : d = c := Eq.trans y₃ ac
                  let y₅ : b = d := Eq.trans nineth (Eq.symm y₄)
                  And.intro ac y₅
              )
              (
                fun (s : {c, d} = {a, b}) =>
                  let y₁: d ∈ {c, d} := right_unordered_pair c d
                  let y₂ : d ∈ {a, b} := eq_subst (fun (x) => d ∈ x) {c, d} {a, b} s y₁
                  let y₃ : d = a ∨ d = b := Iff.mp (unordered_pair_set_is_unordered_pair a b d) y₂
                  Or.elim (y₃)
                  (
                    fun (y₄ : d = a) =>
                      let y₅ : d = c := Eq.trans y₄ ac
                      let y₆ : b = d := Eq.trans nineth (Eq.symm y₅)
                      And.intro ac y₆
                  )
                  (
                    fun (y₄ : d = b) =>
                      And.intro ac (Eq.symm y₄)
                  )
              )

        )
        (
          fun (g : {a, b} = {c, d}) =>
            let y₁ : {c, d} = {a, d} := eq_subst (fun (x) => {c, d} = {x, d}) c a (Eq.symm ac) (Eq.refl {c, d})
            let y₂ : {a, b} = {a, d} := Eq.trans g y₁
            let y₃ : d ∈ {a, d} := right_unordered_pair a d
            let y₄ : d ∈ {a, b} := eq_subst (fun (x) => d ∈ x) {a, d} {a, b} (Eq.symm y₂) y₃
            let y₅ := Iff.mp (unordered_pair_set_is_unordered_pair a b d) y₄
            Or.elim (y₅)
            (
              fun (y₆: d = a) =>
                let y₇ : d = c := Eq.trans y₆ ac
                let y₈ : b ∈ {a, b} := right_unordered_pair a b
                let y₉ : b ∈ {c, d} := eq_subst (fun (x) => b ∈ x) {a, b} {c, d} g y₈
                let t : b = c ∨ b = d := Iff.mp (unordered_pair_set_is_unordered_pair c d b) y₉
                Or.elim (t)
                (
                  fun (u : b = c) =>
                    And.intro ac (Eq.trans (u) (Eq.symm y₇))
                )
                (
                  fun (u : b = d) =>
                    And.intro ac u
                )
            )
            (
              fun (y₆ : d = b) =>
                And.intro ac (Eq.symm y₆)
            )
        )

    )
    (
      fun (h : (a = c ∧ b = d)) =>
        eq_subst (fun (x) => (a, b) = x) (c, b) (c, d)
        (eq_subst (fun (x) => (c, b) = (c, x)) b d (And.right h) (Eq.refl (c, b)))
        (eq_subst (fun (x) => (a, b) = (x, b)) a c (And.left h) (Eq.refl (a, b)))
    )







theorem ordered_pair_set_belonging: ∀ A B, ∀ a ∈ A; ∀ b ∈ B; (a, b) ∈ 𝒫 (𝒫 (A ∪ B)) :=
    fun (A) => fun (B) => fun (a) => fun (g : (a ∈ A)) =>
      fun (b) => fun (h : (b ∈ B)) =>
        let first : ({a, b} ⊆ A ∪ B)
        := fun (x) => fun (s : (x ∈ {a, b})) => Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair a b x) s)  (fun (r : x = a) =>
                let second := eq_subst (fun (s) => s ∈ A) (a) (x) (Eq.symm r) (g)
                let third := (Or.inl : (x ∈ A) → (x ∈ A ∨ x ∈ B)) second
                Iff.mpr (union2_sets_prop A B x) third
          ) (fun (r : x = b) =>
                let second := eq_subst (fun (s) => s ∈ B) (b) (x) (Eq.symm r) (h)
                let third := (Or.inr : (x ∈ B) → (x ∈ A ∨ x ∈ B)) second
                Iff.mpr (union2_sets_prop A B x) third

          )

        let fourth : ({a} ⊆ A ∪ B) := fun (x) => fun (s : (x ∈ {a})) => (
          let second := in_singl_elem a x s
          let third := eq_subst (fun (s) => s ∈ A) (a) (x) (Eq.symm second) (g)
          let fourth := (Or.inl : (x ∈ A) → (x ∈ A ∨ x ∈ B)) third
          Iff.mpr (union2_sets_prop A B x) fourth
        )

        let fifth : {a} ∈ 𝒫 (A ∪ B) := Iff.mpr (boolean_set_is_boolean (A ∪ B) {a}) (fourth)
        let sixth : {a, b} ∈ 𝒫 (A ∪ B) := Iff.mpr (boolean_set_is_boolean (A ∪ B) {a, b}) (first)

        let seventh : {{a}, {a, b}} ⊆ 𝒫 (A ∪ B) := fun (x) => fun (s : x ∈ {{a}, {a, b}}) => Or.elim (Iff.mp (unordered_pair_set_is_unordered_pair {a} {a, b} x) s) (fun (r : x = {a}) =>
          eq_subst (fun (t) => t ∈ 𝒫 (A ∪ B)) {a} x (Eq.symm r) fifth

        ) (
          fun (r : x = {a, b}) => eq_subst (fun (t) => t ∈ 𝒫 (A ∪ B)) {a, b} x (Eq.symm r) sixth
        )

        Iff.mpr (boolean_set_is_boolean (𝒫 (A ∪ B)) (a, b)) seventh


theorem inter_pair_is_singl_fst : ∀ a b, ⋂ (a, b) = {a} :=
  fun (a) => fun (b) =>
    extensionality (⋂ (a, b)) {a}
    (
      fun (x) =>
      Iff.intro
      (
        fun (h : x ∈ ⋂ (a, b)) =>
          And.right (Iff.mp (intersection_set_is_intersection (a, b) x) h) {a} (left_unordered_pair {a} {a, b})

      )
      (
        fun (h : x ∈ {a}) =>
          let first := in_singl_elem a x h
          let h₁ : forall_in_A (fun y => a ∈ y) (a, b) := (
              fun (m : Set) => fun (r : m ∈ (a, b)) =>
              let third := Iff.mp (unordered_pair_set_is_unordered_pair {a} {a, b} m) r
              Or.elim third
              (
                fun (t : m = {a}) =>
                  let fourth := left_unordered_pair a a
                  eq_subst (fun (u) => a ∈ u) {a} m (Eq.symm t) fourth

              )
              (
                fun (t : m = {a, b}) =>
                  let fourth := left_unordered_pair a b
                  eq_subst (fun (u) => a ∈ u) {a, b} m (Eq.symm t) fourth

              )
          )
          let second := Iff.mpr (intersection_non_empty (a, b) (fun (g : (a, b) = ∅) => (empty_set_is_empty {a}) (eq_subst (fun (s) => {a} ∈ s) (a, b) ∅ (g) (left_unordered_pair {a} {a, b}))) a) (h₁)
          eq_subst (fun (u) => u ∈ ⋂ (a, b)) a x (Eq.symm first) (second)
      )
  )


theorem union_pair_is_all_coords : ∀ a b, ⋃ (a, b) = {a, b} :=
  fun (a) => fun (b) =>
    extensionality (⋃ (a, b)) {a, b}
    (
      fun (x) =>
      Iff.intro
      (
        fun (h : x ∈ ⋃ (a, b)) =>
          let first := Iff.mp (union2_sets_prop {a} {a, b} x) h
          Or.elim first
          (
            fun (t : x ∈ {a}) =>
              Iff.mpr (unordered_pair_set_is_unordered_pair a b x) ( (Or.inl : x = a → x = a ∨ x = b)  (in_singl_elem a x t))
          )
          (
            fun (t : x ∈ {a, b}) => t
          )

      )
      (
        fun (h : x ∈ {a, b}) =>
          let first := Iff.mp (unordered_pair_set_is_unordered_pair a b x) h
          Or.elim first
          (
            fun (g : x = a) =>
              Iff.mpr (union2_sets_prop {a} {a, b} x) ((Or.inl : x ∈ {a} → x ∈ {a} ∨ x ∈ {a, b}) (eq_subst (fun (u) => u ∈ {a}) a x (Eq.symm g) (elem_in_singl a)))

          )
          (
            fun (g : x = b) =>
              Iff.mpr (union2_sets_prop {a} {a, b} x) ((Or.inr : x ∈ {a, b} → x ∈ {a} ∨ x ∈ {a, b}) (eq_subst (fun (u) => u ∈ {a, b}) b x (Eq.symm g) (right_unordered_pair a b)))
          )

      )
  )



open Classical


theorem coordinates_snd_corr_lemma : ∀ a b, {x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)} = {b} :=
  fun (a) => fun (b) =>
    extensionality {x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)} {b}
    (
      fun (x) =>
      Iff.intro
      (
        fun (h : x ∈ {x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)}) =>
          let first := Iff.mp (spec_is_spec (fun (p) => ⋃ (a, b) ≠ ⋂ (a, b) → p ∉ ⋂ (a, b)) (⋃ (a, b)) x) h
          let second := And.left first
          let third := And.right first
          let fourth := eq_subst (fun (u) => x ∈ u) (⋃ (a, b)) {a, b} (union_pair_is_all_coords a b) (second)
          let fifth := Iff.mp (unordered_pair_set_is_unordered_pair a b x) fourth
          Or.elim fifth
          (
            fun (t : x = a) =>
              Or.elim (em (⋃ (a, b) = ⋂ (a, b)))
              (
                fun (r : ⋃ (a, b) = ⋂ (a, b)) =>
                let fourth := eq_subst (fun (u) => ⋃ (a, b) = u) (⋂ (a, b)) {a} (inter_pair_is_singl_fst a b) (r)
                let fifth := eq_subst (fun (u) => u = {a}) (⋃ (a, b)) {a, b} (union_pair_is_all_coords a b) (fourth)
                let sixth := eq_subst (fun (u) => b ∈ u) {a, b} {a} fifth (right_unordered_pair a b)
                let seventh := in_singl_elem a b sixth
                let eightht := eq_subst (fun (u) => u = b) a x (Eq.symm t) (Eq.symm seventh)

                eq_subst (fun (u) => u ∈ {b}) b x (Eq.symm eightht) (elem_in_singl b)

              )
              (
                fun (r : ⋃ (a, b) ≠ ⋂ (a, b)) =>
                  let fourth := third r
                  let fifth := eq_subst (fun (u) => x ∉ u) (⋂ (a, b)) {a} (inter_pair_is_singl_fst a b) (fourth)
                  let sixth := (fun (g : x = a) => fifth (eq_subst (fun (u) => u ∈ {a}) a x (Eq.symm g) (elem_in_singl a)))
                  let seventh := sixth t
                  (False.elim : False → (x ∈ {b})) (seventh)
              )
          )
          (
            fun (t : x = b) =>
              eq_subst (fun (u) => u ∈ {b}) b x (Eq.symm t) (elem_in_singl b)
          )
      )
      (
        fun (h : x ∈ {b}) =>
          let first := in_singl_elem b x h
          let second: b ∈ ⋃ (a, b) := eq_subst (fun (u) => b ∈ u) ({a, b}) (⋃ (a, b)) (Eq.symm (union_pair_is_all_coords a b)) (right_unordered_pair a b)
          let third : ⋃ (a, b) ≠ ⋂ (a, b) → b ∉ ⋂ (a, b) := (Iff.mp (contraposition (b ∈ ⋂ (a, b)) (⋃ (a, b) = ⋂ (a, b)))) (
            fun (t : b ∈ ⋂ (a, b)) =>
                let fourth := eq_subst (fun (u) => b ∈ u) (⋂ (a, b)) {a} (inter_pair_is_singl_fst a b) (t)
                let fifth := in_singl_elem a b fourth
                let _ : ⋃ (a, b) = {a, b} := union_pair_is_all_coords a b
                let seventh : {a, b} = {a} := extensionality {a, b} {a} (
                  fun (s) =>
                  Iff.intro
                  (
                    fun (property : s ∈ {a, b}) =>
                      let h₁ := Iff.mp (unordered_pair_set_is_unordered_pair a b s) property
                      Or.elim (h₁)
                      (
                        fun (h₂ : s = a) =>
                          eq_subst (fun (u) => u ∈ {a}) a s (Eq.symm h₂) (elem_in_singl a)
                      )
                      (
                        fun (h₂ : s = b) =>
                          eq_subst (fun (u) => u ∈ {a}) a s (Eq.trans (Eq.symm fifth) (Eq.symm h₂)) (elem_in_singl a)
                      )
                  )
                  (
                    fun (property : s ∈ {a}) =>
                      Iff.mpr (unordered_pair_set_is_unordered_pair a b s) ((Or.inl : s = a → s = a ∨ s = b) (in_singl_elem a s (property)))
                  )
                )
                let eighth : ⋃ (a, b) = {a} := eq_subst (fun (u) => ⋃ (a, b) = u) {a, b} {a} (seventh) (union_pair_is_all_coords a b)
                eq_subst (fun (u) => ⋃ (a, b) = u) {a} (⋂ (a, b)) (Eq.symm (inter_pair_is_singl_fst a b)) (eighth)
          )
          let fourth : b ∈ ⋃ (a, b) ∧ (⋃ (a, b) ≠ ⋂ (a, b) → b ∉ ⋂ (a, b)) := And.intro (second) (third)
          let fifth: x ∈ ⋃ (a, b) ∧ (⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)) := eq_subst (fun (u) => u ∈ ⋃ (a, b) ∧ (⋃ (a, b) ≠ ⋂ (a, b) → u ∉ ⋂ (a, b))) b x (Eq.symm first) (fourth)
          Iff.mpr (spec_is_spec (fun (u) => (⋃ (a, b) ≠ ⋂ (a, b) → u ∉ ⋂ (a, b))) (⋃ (a, b)) x) (fifth)
      )
    )


noncomputable def fst_coor (A : Set) : Set := ⋃ (⋂ A)
noncomputable def snd_coor (A : Set) : Set := ⋃ ({x ∈ ⋃ A | ⋃ A ≠ ⋂ A → x ∉ ⋂ A})
syntax "π₁" term : term
syntax "π₂" term : term
macro_rules
| `(π₁ $s) => `(fst_coor $s)
| `(π₂ $s) => `(snd_coor $s)


theorem coordinates_fst_coor : ∀ a b, fst_coor (a, b) = a :=
  fun (a) => fun (b) =>
    let first : ⋃ (⋂ (a, b)) = ⋃ ({a}) := eq_subst (fun (u) => ⋃ (⋂ (a, b)) = ⋃ u) (⋂ (a, b)) {a} (inter_pair_is_singl_fst a b) (Eq.refl (⋃ (⋂ (a, b))))
    eq_subst (fun (u) => ⋃ (⋂ (a, b)) = u) (⋃ ({a})) a (union_sing a) (first)



theorem coordinates_snd_coor : ∀ a b, snd_coor (a, b) = b :=
  fun (a) => fun (b) =>
    let first : ⋃ ({x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)}) = ⋃ ({b})
    := eq_subst (fun (u) => ⋃ ({x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)}) = ⋃ u) ({x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)}) {b} (coordinates_snd_corr_lemma a b) (Eq.refl (⋃ ({x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)})))
    eq_subst (fun (u) => ⋃ ({x ∈ ⋃ (a, b) | ⋃ (a, b) ≠ ⋂ (a, b) → x ∉ ⋂ (a, b)}) = u) (⋃ {b}) (b) (union_sing b) (first)



noncomputable def cartesian_product (A : Set) (B : Set) : Set := {z ∈ 𝒫 (𝒫 (A ∪ B)) | ∃ x ∈ A; ∃ y ∈ B; z = (x, y)}
infix:60 (priority:=high) " × " => cartesian_product


theorem cartesian_product_is_cartesian: ∀ A B pr, pr ∈ (A × B) ↔ (∃ x ∈ A; ∃ y ∈ B; pr = (x, y)) :=
    fun (A) => fun (B) => fun (pr) =>
      Iff.intro
      (
        fun (h : pr ∈ A × B) =>
          let second := 𝒫 (𝒫 (A ∪ B))
          And.right (Iff.mp (spec_is_spec (fun (pr) => (∃ x ∈ A; ∃ y ∈ B; pr = (x, y))) second pr) h)

      )
      (
        fun (h : (∃ x ∈ A; ∃ y ∈ B; pr = (x, y))) =>
          Exists.elim h
          (
            fun (w) =>
              fun (hw : w ∈ A ∧ ∃ y ∈ B; pr = (w, y)) =>
                Exists.elim (And.right (hw))
                (
                  fun (u) =>
                    fun (hu : u ∈ B ∧ pr = (w, u)) =>
                    let first : (w, u) ∈ 𝒫 (𝒫 (A ∪ B)) := ordered_pair_set_belonging A B w (And.left hw) u (And.left hu)
                    let second : pr ∈ 𝒫 (𝒫 (A ∪ B)):= eq_subst (fun (st) => st ∈ 𝒫 (𝒫 (A ∪ B))) ((w, u)) (pr) (Eq.symm (And.right hu)) (first)
                    let third := And.intro second h
                    Iff.mpr (spec_is_spec (fun (pr) => (∃ x ∈ A; ∃ y ∈ B; pr = (x, y))) (𝒫 (𝒫 (A ∪ B))) pr) third
                )
          )
      )





theorem cartesian_product_pair_prop : ∀ A B a b, (a, b) ∈ (A × B) ↔ (a ∈ A ∧ b ∈ B) :=
  fun (A B a b) =>
    Iff.intro
    (
      fun (h : (a, b) ∈ (A × B)) =>
        let first := Iff.mp (cartesian_product_is_cartesian A B (a, b)) h
        Exists.elim first
        (
          fun (w) =>
            fun (hw : w ∈ A ∧ ∃ y ∈ B; (a, b) = (w, y)) =>
              Exists.elim (And.right hw)
              (
                fun (u) =>
                  fun (hu : u ∈ B ∧ (a, b) = (w, u)) =>
                    let first := Iff.mp (ordered_pair_set_prop a b w u) (And.right hu)
                    let second := eq_subst (fun (elem1) => elem1 ∈ A) w a (Eq.symm (And.left first)) (And.left hw)
                    let third := eq_subst (fun (elem1) => elem1 ∈ B) u b (Eq.symm (And.right first)) (And.left hu)
                    And.intro second third
              )
        )
    )
    (
      fun (h : a ∈ A ∧ b ∈ B) =>
        let first := Iff.mpr (cartesian_product_is_cartesian A B (a, b))
        let second: exists_in_A (fun x => exists_in_A (fun y => (a, b) = (x, y)) B) A := Exists.intro a (And.intro (And.left h) (Exists.intro b (And.intro (And.right h) (Eq.refl (a, b)))))
        first second
    )



theorem fst_coor_set : ∀ A B pr, pr ∈ A × B → fst_coor pr ∈ A :=
  fun (A B pr) => fun (h₁ : pr ∈ A × B) =>
    let s := Iff.mp (cartesian_product_is_cartesian A B pr) h₁
    Exists.elim s
    (
      fun (w) => fun (hw : w ∈ A ∧ ∃ u ∈ B; pr = (w, u)) =>
        Exists.elim (And.right hw)
        (
          fun (u) => fun (hu : u ∈ B ∧ pr = (w, u)) =>
            eq_subst (fun (p) => fst_coor p ∈ A) (w, u) pr (Eq.symm (And.right hu)) (
              eq_subst (fun (p) => p ∈ A) (w) (fst_coor (w, u)) (Eq.symm (coordinates_fst_coor w u)) (And.left hw)
            )
        )
    )


theorem snd_coor_set : ∀ A B pr, pr ∈ A × B → snd_coor pr ∈ B :=
  fun (A B pr) => fun (h₁ : pr ∈ A × B) =>
    let s := Iff.mp (cartesian_product_is_cartesian A B pr) h₁
    Exists.elim s
    (
      fun (w) => fun (hw : w ∈ A ∧ ∃ u ∈ B; pr = (w, u)) =>
        Exists.elim (And.right hw)
        (
          fun (u) => fun (hu : u ∈ B ∧ pr = (w, u)) =>
            eq_subst (fun (p) => snd_coor p ∈ B) (w, u) pr (Eq.symm (And.right hu)) (
              eq_subst (fun (p) => p ∈ B) (u) (snd_coor (w, u)) (Eq.symm (coordinates_snd_coor w u)) (And.left hu)
            )
        )
    )


theorem fst_snd_then_unique : ∀ A B pr, pr ∈ A × B → pr = (fst_coor pr, snd_coor pr) :=
  fun (A B pr) => fun (h₁ : pr ∈ A × B) =>
    let h₂ := Iff.mp (cartesian_product_is_cartesian A B pr) h₁
    Exists.elim h₂
    (
      fun (w) => fun (hw : w ∈ A ∧ ∃ u ∈ B; pr = (w, u)) =>
        Exists.elim (And.right hw)
        (
          fun (u) => fun (hu : u ∈ B ∧ pr = (w, u)) =>
            let h₃ := coordinates_fst_coor w u
            let h₄ := coordinates_snd_coor w u
            let h₅ := eq_subst (fun (p) => fst_coor p = w) (w, u) pr (Eq.symm (And.right hu)) h₃
            let h₆ := eq_subst (fun (p) => snd_coor p = u) (w, u) pr (Eq.symm (And.right hu)) h₄
            Eq.trans (And.right hu) (Iff.mpr (ordered_pair_set_prop w u (fst_coor pr) (snd_coor pr)) (And.intro (Eq.symm h₅) (Eq.symm h₆)))
        )
    )




theorem equal_fst_snd : ∀ A B pr₁ pr₂, (pr₁ ∈ A × B) → (pr₂ ∈ A × B) →
  (fst_coor pr₁ = fst_coor pr₂) → (snd_coor pr₁ = snd_coor pr₂) → pr₁ = pr₂ :=
  fun (A B pr₁ pr₂) => fun (hpr₁ : pr₁ ∈ A × B) => fun (hpr₂ : pr₂ ∈ A × B) =>
    fun (hfst : (fst_coor pr₁ = fst_coor pr₂)) => fun (hsnd : (snd_coor pr₁ = snd_coor pr₂)) =>
      Eq.trans (fst_snd_then_unique A B pr₁ hpr₁)
      (Eq.trans (Iff.mpr (ordered_pair_set_prop (fst_coor pr₁) (snd_coor pr₁) (fst_coor pr₂) (snd_coor pr₂))
        (And.intro (hfst) (hsnd)))
       (Eq.symm (fst_snd_then_unique A B pr₂ hpr₂)))







theorem cartesian_product_subset : ∀ A B C D, A ⊆ C → B ⊆ D → (A × B) ⊆ C × D :=
  fun (A B C D) => fun (h₁ : A ⊆ C) => fun (h₂ : B ⊆ D) =>
    fun (x) =>
      fun (t : x ∈ A × B) =>
        let first := Iff.mp (cartesian_product_is_cartesian A B x) t
        Exists.elim first
        (
          fun (w) =>
            fun (hw : w ∈ A ∧ ∃ u ∈ B; x = (w, u)) =>
              Exists.elim (And.right hw)
              (
                fun (u) =>
                  fun (hu : u ∈ B ∧ x = (w, u)) =>
                    Iff.mpr ((cartesian_product_is_cartesian C D x)) (
                      Exists.intro w (And.intro (h₁ w (And.left hw)) (Exists.intro u (And.intro (h₂ u (And.left hu)) (And.right hu))))
                    )

              )
        )




theorem cartesian_product_intersect : ∀ A B C D, (A × B) ∩ (C × D) ⊆ (A ∩ C) × (B ∩ D) :=
  fun (A B C D) => fun (x) => fun (t : x ∈ (A × B) ∩ (C × D)) =>
    let h₁ := Iff.mp (intersect_2sets_prop (A × B) (C × D) x) t
    let h₂ := And.left h₁
    let h₃ := And.right h₁
    let h₄ := Iff.mp (cartesian_product_is_cartesian A B x) h₂
    let h₅ := Iff.mp (cartesian_product_is_cartesian C D x) h₃
    Exists.elim h₄
    (
      fun (w) =>
        fun (hw : w ∈ A ∧ ∃ y ∈ B; x = (w, y)) =>
          Exists.elim (And.right hw)
          (
            fun (u) =>
              fun (hu : u ∈ B ∧ x = (w, u)) =>
                Exists.elim h₅
                (
                  fun (y) =>
                    fun (hy : y ∈ C ∧ ∃ r ∈ D; x = (y, r)) =>
                      Exists.elim (And.right hy)
                      (
                        fun (z) =>
                          fun (hz : z ∈ D ∧ x = (y, z)) =>
                            let h₆ := Iff.mp (ordered_pair_set_prop w u y z) (Eq.trans (Eq.symm (And.right hu)) (And.right hz))
                            let h₇ := Iff.mpr (intersect_2sets_prop A C w) (And.intro (And.left hw) (eq_subst (fun (u) => u ∈ C) y w (Eq.symm (And.left h₆)) (And.left hy)))
                            let h₈ := Iff.mpr (intersect_2sets_prop B D u) (And.intro (And.left hu) (eq_subst (fun (p) => p ∈ D) z u (Eq.symm (And.right h₆)) (And.left hz)))
                            let h₉ := Iff.mpr (cartesian_product_pair_prop (A ∩ C) (B ∩ D) w u) (And.intro (h₇) (h₈))
                            eq_subst (fun (p) => p ∈ (A ∩ C) × (B ∩ D)) (w, u) x (Eq.symm (And.right hu)) (h₉)
                      )
                )
          )
    )







noncomputable def disjoint_union (A B : Set) := (A × {∅}) ∪ (B × {{∅}})
syntax term "⊔" term : term
macro_rules
| `($A ⊔ $B) => `(disjoint_union $A $B)

theorem disj_in_left : ∀ A B x, (x ∈ A) → ((x, ∅) ∈ (A ⊔ B)) :=
  fun (A B x hx) =>
    Iff.mpr (union2_sets_prop (A × {∅}) (B × {{∅}}) (x, ∅)) (
      Or.inl (
        Iff.mpr (cartesian_product_pair_prop A {∅} x ∅) (
          And.intro hx (elem_in_singl ∅)
        )
      )
    )


theorem disj_in_righ : ∀ A B x, (x ∈ B) → ((x, {∅}) ∈ (A ⊔ B)) :=
  fun (A B x hx) =>
    Iff.mpr (union2_sets_prop (A × {∅}) (B × {{∅}}) (x, {∅})) (
      Or.inr (
        Iff.mpr (cartesian_product_pair_prop B {{∅}} x {∅}) (
          And.intro hx (elem_in_singl {∅})
        )
      )
    )


theorem disjunion2_pair_prop : ∀ A B x y, (x, y) ∈ (A ⊔ B) ↔ (x ∈ A ∧ y = ∅) ∨ (x ∈ B ∧ y = {∅}) :=
  fun (A B x y) =>
    Iff.intro
    (
      fun (hxy) =>
        let u₁ := Iff.mp (union2_sets_prop (A × {∅}) (B × {{∅}}) (x, y)) hxy
        Or.elim u₁
        (
          fun (hxyA) =>
            Or.inl (
              let u₂ := Iff.mp (cartesian_product_pair_prop A {∅} x y) hxyA
              And.intro (And.left u₂) (in_singl_elem ∅ y (And.right u₂))
            )
        )
        (
          fun (hxyB) =>
            Or.inr (
              let u₂ := Iff.mp (cartesian_product_pair_prop B {{∅}} x y) hxyB
              And.intro (And.left u₂) (in_singl_elem {∅} y (And.right u₂))
            )
        )
    )
    (
      fun (hxy) =>
        Or.elim hxy
        (
          fun (hxyA) =>
            Iff.mpr (union2_sets_prop (A × {∅}) (B × {{∅}}) (x, y)) (
              Or.inl (
                Iff.mpr (cartesian_product_pair_prop A {∅} x y) (
                  And.intro (And.left hxyA) (eq_subst (fun (t) => y ∈ {t}) y ∅ (And.right hxyA) (elem_in_singl y))
                )
              )
            )
        )
        (
          fun (hxyB) =>
            Iff.mpr (union2_sets_prop (A × {∅}) (B × {{∅}}) (x, y)) (
              Or.inr (
                Iff.mpr (cartesian_product_pair_prop B {{∅}} x y) (
                  And.intro (And.left hxyB) (eq_subst (fun (t) => y ∈ {t}) y {∅} (And.right hxyB) (elem_in_singl y))
                )
              )
            )
        )
    )


noncomputable def disjoint_union_left (X: Set) := {y ∈ X | (π₂ y) = ∅}
noncomputable def disjoint_union_right (X : Set) := {y ∈ X | (π₂ y) = {∅}}
syntax "DUL" term : term
syntax "DUR" term : term
macro_rules
| `(DUL $X) => `(disjoint_union_left $X)
| `(DUR $X) => `(disjoint_union_right $X)


theorem dul_A : ∀ A B, (DUL (A ⊔ B)) = (A × {∅}) :=
  fun (A B) =>
    let P := fun (t) => (π₂ t) = ∅
    let S := (DUL (A ⊔ B))
    let T := (A × {∅})
    extensionality S T (
      fun (x) =>
        Iff.intro
        (
          fun (xS) =>
            let u₁ := Iff.mp (spec_is_spec P (A ⊔ B) x) xS
            let u₂ := And.left u₁
            let u₃ := And.right u₁
            let u₄ := Iff.mp (union2_sets_prop (A × {∅}) (B × {{∅}}) x) u₂
            Or.elim u₄
            (
              fun (hx) =>
                hx
            )
            (
              fun (hx) =>
                let u₅ := Iff.mp (cartesian_product_pair_prop B {{∅}} (π₁ x) (π₂ x)) (
                  eq_subst (fun (t) => t ∈ B × {{∅}}) (x) (π₁ x, π₂ x) (fst_snd_then_unique B {{∅}} x hx) (hx)
                )
                let u₆ := in_singl_elem {∅} (π₂ x) (And.right u₅)

                False.elim (empty_set_is_empty ∅ (
                  eq_subst (fun (t) => ∅ ∈ t) ({∅}) ∅ (Eq.trans (Eq.symm u₆) (u₃)) (elem_in_singl ∅)
                ))
            )
        )
        (
          fun (xT) =>
            Iff.mpr (spec_is_spec P (A ⊔ B) x) (
              And.intro (Iff.mpr (union2_sets_prop (A × {∅}) (B × {{∅}}) x) (
                Or.inl (xT)
              )) (
                let u₁ := eq_subst (fun (t) => t ∈ T) (x) (π₁ x, π₂ x) (fst_snd_then_unique A {∅} x xT) (xT)
                let u₂ := And.right (Iff.mp (cartesian_product_pair_prop A {∅} (π₁ x) (π₂ x)) (u₁))
                in_singl_elem ∅ (π₂ x) (u₂)
              )
            )

        )
    )
theorem dur_B : ∀ A B, (DUR (A ⊔ B)) = (B × {{∅}}) :=
  fun (A B) =>
    let P := fun (t) => (π₂ t) = {∅}
    let S := (DUR (A ⊔ B))
    let T := (B × {{∅}})
    extensionality S T (
      fun (x) =>
        Iff.intro
        (
          fun (xS) =>
            let u₁ := Iff.mp (spec_is_spec P (A ⊔ B) x) xS
            let u₂ := And.left u₁
            let u₃ := And.right u₁
            let u₄ := Iff.mp (union2_sets_prop (A × {∅}) (B × {{∅}}) x) u₂
            Or.elim u₄
            (
              fun (hx) =>
                let u₅ := Iff.mp (cartesian_product_pair_prop A {∅} (π₁ x) (π₂ x)) (
                  eq_subst (fun (t) => t ∈ A × {∅}) (x) (π₁ x, π₂ x) (fst_snd_then_unique A {∅} x hx) (hx)
                )
                let u₆ := in_singl_elem ∅ (π₂ x) (And.right u₅)

                False.elim (empty_set_is_empty ∅ (
                  eq_subst (fun (t) => ∅ ∈ t) ({∅}) ∅ (Eq.trans (Eq.symm u₃) (u₆)) (elem_in_singl ∅)
                ))
            )
            (
              fun (hx) =>
                hx
            )
        )
        (
          fun (xT) =>
            Iff.mpr (spec_is_spec P (A ⊔ B) x) (
              And.intro (Iff.mpr (union2_sets_prop (A × {∅}) (B × {{∅}}) x) (
                Or.inr (xT)
              )) (
                let u₁ := eq_subst (fun (t) => t ∈ T) (x) (π₁ x, π₂ x) (fst_snd_then_unique B {{∅}} x xT) (xT)
                let u₂ := And.right (Iff.mp (cartesian_product_pair_prop B {{∅}} (π₁ x) (π₂ x)) (u₁))
                in_singl_elem {∅} (π₂ x) (u₂)
              )
            )

        )
    )
theorem dul_subs : ∀ A B, (DUL (A ⊔ B)) ⊆ (A ⊔ B) :=
  fun (A B) =>
    let S := (A × {∅})
    let T := (B × {{∅}})
    eq_subst (fun (t) => t ⊆ A ⊔ B) (S) (DUL (A ⊔ B)) (Eq.symm (dul_A A B)) (And.left (union2_sets_subset_prop S T))


theorem dur_subs : ∀ A B, (DUR (A ⊔ B)) ⊆ (A ⊔ B) :=
  fun (A B) =>
    let S := (A × {∅})
    let T := (B × {{∅}})
    eq_subst (fun (t) => t ⊆ A ⊔ B) (T) (DUR (A ⊔ B)) (Eq.symm (dur_B A B)) (And.right (union2_sets_subset_prop S T))


theorem dulr_un : ∀ A B, (A ⊔ B) = (DUL (A ⊔ B)) ∪ (DUR (A ⊔ B)) :=
  fun (A B) =>
    let M := (A ⊔ B)
    let S := (A × {∅})
    let T := (B × {{∅}})
    let Lu := (DUL (A ⊔ B))
    let Ru := (DUR (A ⊔ B))
    eq_subst (fun (t) => M = (t ∪ Ru)) (S) (Lu) (Eq.symm (dul_A A B)) (
      eq_subst (fun (t) => M = (S ∪ t)) (T) (Ru) (Eq.symm (dur_B A B)) (Eq.refl M)
    )

theorem dulr_in : ∀ A B, (DUL (A ⊔ B)) ∩ (DUR (A ⊔ B)) = ∅ :=
  fun (A B) =>
    let P₁ := fun (t) => (π₂ t) = ∅
    let P₂ := fun (t) => (π₂ t) = {∅}
    let M := (DUL (A ⊔ B))
    let N := (DUR (A ⊔ B))
    Iff.mp (subs_subs_eq (M ∩ N) (∅)) (
      And.intro (
        fun (x hx) =>
          False.elim (
            let u₀ := Iff.mp (intersect_2sets_prop M N x) hx
            let u₁ := And.right (Iff.mp (spec_is_spec P₁ (A ⊔ B) x) (And.left u₀))
            let u₂ := And.right (Iff.mp (spec_is_spec P₂ (A ⊔ B) x) (And.right u₀))
            let u₃ := Eq.trans (Eq.symm u₁) (u₂)
            let u₄ := elem_in_singl ∅
            let u₅ := eq_subst (fun (t) => ∅ ∈ t) ({∅}) (∅) (Eq.symm u₃) (u₄)

            empty_set_is_empty ∅ (u₅)
          )
      ) (empty_set_is_subset_any (M ∩ N))
    )




-- tuple syntax
declare_syntax_cat pair_comprehension
syntax  pair_comprehension "; " term : pair_comprehension
syntax term : pair_comprehension
syntax "⁅" pair_comprehension "⁆" : term
macro_rules
| `(⁅ $term1:term⁆) => `($term1)
| `(⁅ $term1:term; $term2:term⁆) => `(ordered_pair_set $term1 $term2)
| `(⁅ $rest:pair_comprehension; $elem:term⁆) => `(ordered_pair_set ⁅$rest:pair_comprehension⁆ $elem:term)




noncomputable def binary_relation (R : Set) : Prop := ∀ z ∈ R; ∃ a, ∃ b, z = (a, b)
noncomputable def binary_relation_between (A B R : Set) : Prop := R ⊆ A × B
noncomputable def binary_relation_on (A R : Set) : Prop := R ⊆ A × A

syntax "BinRel" term : term
macro_rules
|  `(BinRel $R:term) => `(binary_relation $R)
syntax term "BinRelOn" term : term
macro_rules
| `($R:term BinRelOn $A:term) => `(binary_relation_on $A $R)
syntax term "BinRelBtw" term "AND" term : term
macro_rules
| `($R:term BinRelBtw $A:term AND $B:term) => `(binary_relation_between $A $B $R)


macro_rules
| `(($x:term . $P:term . $y:term)) => `(($x, $y) ∈ $P)


theorem binary_relation_elements_set: ∀ R x y, (x . R . y) → (x ∈ ⋃ (⋃ R) ∧ y ∈ ⋃ (⋃ R)) :=
  fun (R : Set) => fun (x : Set) => fun (y : Set) =>
    fun (h : (x . R . y)) =>
      let first: {x, y} ∈ (x, y) := right_unordered_pair {x} {x, y}
      let second: {x, y} ∈ ⋃ R := Iff.mpr (union_set_is_union R {x, y}) (Exists.intro (x, y) (And.intro (h) (first)))
      let third := right_unordered_pair x y
      let fourth := left_unordered_pair x y
      let fifth := Iff.mpr (union_set_is_union (⋃ R) x) (Exists.intro {x, y} (And.intro (second) (fourth)))
      let sixth := Iff.mpr (union_set_is_union (⋃ R) y) (Exists.intro {x, y} (And.intro (second) (third)))
      And.intro fifth sixth





noncomputable def dom (R : Set) := {x ∈ ⋃ (⋃ R) | ∃ y, (x . R . y)}
noncomputable def rng (R : Set) := {y ∈ ⋃ (⋃ R) | ∃ x, (x . R . y)}


theorem dom_rng_rel_prop: ∀ R, (BinRel R) → (dom R ∪ rng R = ⋃ (⋃ R)) :=
    fun (R : Set) =>
      fun (h : (BinRel R)) =>
        subset_then_equality (dom R ∪ rng R) (⋃ (⋃ R)) (
          And.intro
          (
            fun (x) =>
              fun (g : x ∈ (dom R ∪ rng R)) =>
                let first:= Iff.mp (union2_sets_prop (dom R) (rng R) x) g
                Or.elim first
                (
                  fun (f : x ∈ dom R) =>
                    And.left (Iff.mp (spec_is_spec (fun (t) => ∃ y, (t . R . y)) (⋃ (⋃ R)) x) f)
                )
                (
                  fun (f : x ∈ rng R) =>
                    And.left (Iff.mp (spec_is_spec (fun (t) => ∃ x, (x . R . t)) (⋃ (⋃ R)) x) f)
                )

          )
          (
            fun (coor) =>
              fun (g : coor ∈ ⋃ (⋃ R)) =>
                let first := (Iff.mp (union_set_is_union (⋃ R) coor) g)
                Exists.elim first
                (
                  fun (w) =>
                    fun (hw : w ∈ ⋃ R ∧ coor ∈ w) =>
                      let second := Iff.mp ((union_set_is_union R w)) (And.left hw)
                      Exists.elim second
                      (
                        fun (u) =>
                          fun (hu : u ∈ R ∧ w ∈ u) =>
                            let third := h u (And.left hu)
                            Exists.elim third (
                              fun (a) =>
                                fun (ha : ∃ b, u = (a, b)) =>
                                  Exists.elim ha
                                  (
                                    fun (b) =>
                                      fun (hb : u = (a, b)) =>
                                        let fourth := Iff.mp (unordered_pair_set_is_unordered_pair {a} {a, b} w) (
                                          eq_subst (fun (t) => w ∈ t) u (a, b) (hb) (And.right hu)
                                          )
                                        Or.elim (fourth)
                                        (
                                          fun (s : w = {a}) =>
                                            let fifth := eq_subst (fun (t) => coor ∈ t) w {a} s (And.right hw)
                                            let sixth := in_singl_elem a coor fifth
                                            let seventh := eq_subst (fun (t) => t ∈ R) u (a, b) hb (And.left hu)
                                            let eight := eq_subst (fun (t) => (t . R . b)) a coor (Eq.symm sixth) (seventh)
                                            let nineth: ∃ y, (coor . R . y) := Exists.intro b eight
                                            let tenth: coor ∈ dom R
                                            := Iff.mpr (spec_is_spec (fun (t) => ∃ y, (t . R . y)) (⋃ (⋃ R)) coor) (And.intro (g) (nineth))
                                            let eleventh := (Or.inl : coor ∈ dom R → coor ∈ dom R ∨ coor ∈ rng R) tenth
                                            Iff.mpr (union2_sets_prop (dom R) (rng R) coor) eleventh


                                        )
                                        (
                                          fun (s : w = {a, b}) =>
                                            let fifth := eq_subst (fun (t) => coor ∈ t) w {a, b} s (And.right hw)
                                            let h₁ := Iff.mp (unordered_pair_set_is_unordered_pair a b coor) fifth
                                            Or.elim (h₁)
                                            (
                                              fun (sixth : coor = a) =>
                                                let seventh := eq_subst (fun (t) => t ∈ R) u (a, b) hb (And.left hu)
                                                let eight := eq_subst (fun (t) => (t . R . b)) a coor (Eq.symm sixth) (seventh)
                                                let nineth: ∃ y, (coor . R . y) := Exists.intro b eight
                                                let tenth: coor ∈ dom R
                                                := Iff.mpr (spec_is_spec (fun (t) => ∃ y, (t . R . y)) (⋃ (⋃ R)) coor) (And.intro (g) (nineth))
                                                let eleventh := (Or.inl : coor ∈ dom R → coor ∈ dom R ∨ coor ∈ rng R) tenth
                                                Iff.mpr (union2_sets_prop (dom R) (rng R) coor) eleventh
                                            )
                                            (
                                              fun (sixth : coor = b) =>
                                                let seventh := eq_subst (fun (t) => t ∈ R) u (a, b) hb (And.left hu)
                                                let eight := eq_subst (fun (t) => (a . R . t)) b coor (Eq.symm sixth) (seventh)
                                                let nineth: ∃ x, (x . R . coor) := Exists.intro a eight
                                                let tenth: coor ∈ rng R
                                                := Iff.mpr (spec_is_spec (fun (t) => ∃ x, (x . R . t)) (⋃ (⋃ R)) coor) (And.intro (g) (nineth))
                                                let eleventh := (Or.inr : coor ∈ rng R → coor ∈ dom R ∨ coor ∈ rng R) tenth
                                                Iff.mpr (union2_sets_prop (dom R) (rng R) coor) eleventh

                                            )
                                        )
                                  )
                            )
                      )
                )
         )
        )



theorem dom_prop : ∀ R x, x ∈ dom R ↔ ∃ y, (x . R . y) :=
  fun (R) =>
    fun (x) =>
      Iff.intro
      (
        fun (s : x ∈ dom R) =>
          And.right (Iff.mp (spec_is_spec (fun (t) => ∃ y, (t . R . y)) (⋃ (⋃ R)) x) s)

      )
      (
        fun (s : ∃ y, (x . R . y)) =>
          Exists.elim (s)
          (
            fun (w) =>
              fun (hw : (x . R . w)) =>
              let first := And.left (binary_relation_elements_set R x w hw)
              Iff.mpr (spec_is_spec (fun (t) => ∃ y, (t . R . y)) (⋃ (⋃ R)) x) (And.intro (first) (s))

          )
      )


theorem rng_prop : ∀ R y, y ∈ rng R ↔ ∃ x, (x . R . y) :=
  fun (R) =>
    fun (y) =>
      Iff.intro
      (
        fun (s : y ∈ rng R) =>
          And.right (Iff.mp (spec_is_spec (fun (t) => ∃ x, (x . R . t)) (⋃ (⋃ R)) y) s)

      )
      (
        fun (s : ∃ x, (x . R . y)) =>
          Exists.elim (s)
          (
            fun (w) =>
              fun (hw : (w . R . y)) =>
              let first := And.right (binary_relation_elements_set R w y hw)
              Iff.mpr (spec_is_spec (fun (t) => ∃ x, (x . R . t)) (⋃ (⋃ R)) y) (And.intro (first) (s))
          )
      )



theorem binary_relation_prop : ∀ R, (BinRel R) → (R BinRelBtw (dom R) AND (rng R)) :=
  fun (R) => fun (h : (BinRel R)) =>
    fun (pr) =>
      fun (g : pr ∈ R) =>
        Exists.elim  (h pr g)
        (
          fun (a) =>
            fun (ha : ∃ b, pr = (a, b)) =>
              Exists.elim (ha)
              (
                fun (b) =>
                  fun (hb : pr = (a, b)) =>
                    let first := eq_subst (fun(t) => t ∈ R) pr (a, b) (hb) g
                    let second := And.left (binary_relation_elements_set R a b first)
                    let third := And.right (binary_relation_elements_set R a b first)
                    let h₁ : ∃ b, (a . R . b) := Exists.intro b (eq_subst (fun (t) => t ∈ R) pr (a, b) (hb) (g))
                    let fourth: a ∈ dom R := Iff.mpr (spec_is_spec (fun (t) => ∃ y, (t . R . y)) (⋃ (⋃ R)) a) (And.intro second h₁)
                    let h₂ : ∃ a, (a . R . b) := Exists.intro a (eq_subst (fun (t) => t ∈ R) pr (a, b) (hb) (g))
                    let fifth: b ∈ rng R := Iff.mpr (spec_is_spec (fun (t) => ∃ x, (x . R . t)) (⋃ (⋃ R)) b) (And.intro third h₂)
                    let sixth := Iff.mpr (cartesian_product_pair_prop (dom R) (rng R) a b)
                    let seventh := And.intro fourth fifth
                    let eighth := sixth seventh
                    eq_subst (fun (t) => t ∈ dom R × rng R) (a, b) pr (Eq.symm hb) (eighth)
              )
        )




theorem prop_then_binary_relation : ∀ A B R, (R BinRelBtw A AND B) → (BinRel R) ∧ dom R ⊆ A ∧ rng R ⊆ B :=
  fun (A B R) => fun (h : R ⊆ A × B) =>
    let first : (BinRel R) := fun (z) => fun (g : z ∈ R) =>
      Exists.elim (Iff.mp (cartesian_product_is_cartesian A B z) (h z g))
      (
        fun (a) =>
          fun (ha : a ∈ A ∧ ∃ b ∈ B; z = (a, b)) =>
            Exists.elim (And.right ha)
            (
              fun (b) =>
                fun (hb : b ∈ B ∧ z = (a, b)) =>
                  Exists.intro a (Exists.intro b (And.right hb))
            )
      )

    And.intro (
      first
    ) (
      And.intro
      (
        fun (a) => fun (g : a ∈ dom R) =>

        let second := And.right (Iff.mp (spec_is_spec (fun (t) => ∃ y, (t . R . y)) (⋃ (⋃ R)) a) g)
        Exists.elim second
        (
          fun (b) =>
            fun (hb : (a . R . b)) =>
              And.left (Iff.mp (cartesian_product_pair_prop A B a b) (h (a, b) hb))
        )
      )
      (
        fun (b) => fun (g : b ∈ rng R) =>

        let second := And.right (Iff.mp ((spec_is_spec (fun (t) => ∃ x, (x . R . t)) (⋃ (⋃ R)) b)) g)
        Exists.elim second
        (
          fun (a) =>
            fun (ha : (a . R . b)) =>
              And.right (Iff.mp (cartesian_product_pair_prop A B a b) (h (a, b) ha))
        )
      )
    )


theorem rel_dom_rng_elem : ∀ R, (BinRel R) → ∀ x y, (x . R . y) → x ∈ dom R ∧ y ∈ rng R :=
  fun (R) => fun (h : (BinRel R)) =>
    fun (x) => fun (y) => fun (g : (x . R . y)) =>
    let first := binary_relation_prop R h (x, y) g
    Iff.mp (cartesian_product_pair_prop (dom R) (rng R) x y) first




theorem union2_rel_is_rel : ∀ P Q, (BinRel P) → (BinRel Q) → (BinRel (P ∪ Q)) :=
  fun (P) => fun (Q) => fun (h : (BinRel P)) => fun (g : (BinRel Q)) =>
    fun (z) => fun (h₁ : z ∈ (P ∪ Q)) =>
      let first := Iff.mp (union2_sets_prop P Q z) h₁
      Or.elim first
      (
        fun (s : z ∈ P) =>
          h z s
      )
      (
        fun (s : z ∈ Q) =>
          g z s
      )


theorem intersect2_rel_is_rel : ∀ P Q, (BinRel P) → (BinRel Q) → (BinRel (P ∩ Q)) :=
  fun (P) => fun (Q) => fun (h : (BinRel P)) => fun (_ : (BinRel Q)) =>
    fun (z) => fun (h₁ : z ∈ (P ∩ Q)) =>
      h z ((And.left (intersect_2sets_subset_prop P Q)) z h₁)




noncomputable def comp (A B R : Set) : Set := (A × B) \ R



theorem comp_is_rel : ∀ A B R, (BinRel (comp A B R)) :=
  fun (A B R) => fun (z) => fun (h : z ∈ (comp A B R)) =>
    let first := comp_2sets_subset_prop (A × B) R z h
    let second := (Iff.mp (cartesian_product_is_cartesian A B z) first)
    Exists.elim (second)
    (
      fun (w) =>
        fun (hw : w ∈ A ∧ ∃ u ∈ B; z = (w, u)) =>
          Exists.elim (And.right hw)
          (
            fun (u) =>
              fun (hu : u ∈ B ∧ z = (w, u)) =>
              Exists.intro w (Exists.intro u (And.right hu))
          )
    )




noncomputable def inv (R : Set) : Set := {z ∈ rng R × dom R | ∃ x, ∃ y, (z = (y, x) ∧ (x . R . y))}

syntax term"⁻¹" : term

macro_rules
| `($term1:term⁻¹) => `(inv $term1)



theorem inv_is_rel : ∀ R, (BinRel R) → (BinRel (R⁻¹)) :=
  fun (R) => fun (_ : (BinRel R)) =>
    fun (z) => fun (h : z ∈ R⁻¹) =>
      let first := And.right (Iff.mp (spec_is_spec (fun (t) => ∃ x, ∃ y, (t = (y, x) ∧ (x . R . y)))
        (rng R × dom R) z) h)
      Exists.elim first (
        fun (a) =>
          fun (ha : ∃ b, z = (b, a) ∧ (a . R . b)) =>
            Exists.elim ha
            (
              fun (b) =>
                fun (hb : z = (b, a) ∧ (a . R . b)) =>
                  Exists.intro b (Exists.intro a (And.left hb))
            )
      )


theorem inv_pair_prop_mp : ∀ R, ∀ x y, (x . R . y) → (y . (R⁻¹) . x) :=
  fun (R) => fun (x y) => fun (h₁ : (x . R . y)) =>
    let first: ((y . (rng R × dom R) . x) ∧ ∃ x_1 y_1, (y, x) = (y_1, x_1) ∧ (x_1 . R . y_1)) → (y . (R⁻¹) . x)
          := Iff.mpr (spec_is_spec (fun (t) => ∃ x, ∃ y, (t = (y, x) ∧ (x . R . y))) (rng R × dom R) (y, x))
    let second := Iff.mpr (rng_prop R y) (Exists.intro x (h₁))
    let third := Iff.mpr (dom_prop R x) (Exists.intro y (h₁))
    let fourth := Iff.mpr (cartesian_product_pair_prop (rng R) (dom R) y x) (And.intro second third)
    let fifth : ∃ x_1 y_1, (y, x) = (y_1, x_1) ∧ (x_1 . R . y_1) := Exists.intro x (Exists.intro y (And.intro (Eq.refl (y, x)) (h₁)))
    first (And.intro (fourth) (fifth))


theorem inv_pair_prop: ∀ R, (BinRel R) → ∀ x y, (x . R . y) ↔ (y . (R⁻¹) . x):=
  fun (R) => fun (_ : (BinRel R)) =>
    fun (x) => fun (y) =>
      Iff.intro
      (
       inv_pair_prop_mp R x y
      )
      (
        fun (h₂ : (y . (R⁻¹) . x)) =>
          Exists.elim (And.right (Iff.mp (spec_is_spec (fun (t) => ∃ x, ∃ y, (t = (y, x) ∧ (x . R . y))) (rng R × dom R) (y, x)) h₂))
          (
            fun (x_1) =>
              fun (hx_1 : ∃ y_1, (y, x) = (y_1, x_1) ∧ (x_1 . R . y_1)) =>
                Exists.elim (hx_1)
                (
                  fun (y_1) =>
                    fun (hy_1 : (y, x) = (y_1, x_1) ∧ (x_1 . R . y_1)) =>
                      let first := Iff.mp (ordered_pair_set_prop y_1 x_1 y x) (Eq.symm (And.left hy_1))
                      let second := Iff.mpr (ordered_pair_set_prop x y x_1 y_1) (And.intro (Eq.symm (And.right first)) (Eq.symm (And.left first)))
                      let third := eq_subst (fun (t) => t ∈ R) (x_1, y_1) (x, y) (Eq.symm second) (And.right hy_1)
                      third
                )
          )
      )



theorem inv_prop : ∀ R, (BinRel R) → (R⁻¹)⁻¹ = R :=
  fun (R) => fun (h : (BinRel R)) =>
    extensionality ((R⁻¹)⁻¹) R
    (
      fun (x) =>
      Iff.intro
      (
        fun (s : x ∈ ((R⁻¹)⁻¹)) =>
          let first := inv_is_rel R h
          Exists.elim (inv_is_rel (R⁻¹) first x s)
          (
            fun (a) =>
              fun (ha : ∃ b, x = (a, b) ) =>
              Exists.elim ha
              (
                fun (b) =>
                  fun (hb : x = (a, b)) =>
                    let second := eq_subst (fun (t) => t ∈ ((R⁻¹)⁻¹)) x (a, b) hb s
                    let third := Iff.mpr (inv_pair_prop (R⁻¹) first b a) second
                    let fourth := Iff.mpr (inv_pair_prop R h a b) third
                    eq_subst (fun (t) => t ∈ R) (a, b) x (Eq.symm hb) (fourth)
              )
          )
      )
      (
        fun (s : x ∈ R) =>
          let h₁ := inv_is_rel R h
          Exists.elim (h x s)
          (
            fun (a) =>
              fun (ha : ∃ b, x = (a, b)) =>
                Exists.elim ha
                (
                  fun (b) =>
                    fun (hb : x = (a, b)) =>
                      let first := eq_subst (fun (t) => t ∈ R) x (a, b) hb s
                      let second:= Iff.mp (inv_pair_prop R (h) a b) first
                      let third:= Iff.mp (inv_pair_prop (R⁻¹) (h₁) b a) second
                      eq_subst (fun (t) => t ∈ (R⁻¹)⁻¹) (a, b) x (Eq.symm hb) (third)
                )
          )
      )
    )


theorem inv_between_mp : ∀ A B R, (R BinRelBtw A AND B) → (R⁻¹ BinRelBtw B AND A) :=
  fun (A B R) =>
      (
        fun (h : (R BinRelBtw A AND B)) =>
          fun (s) => fun (h₁ : s ∈ (R⁻¹)) =>
            let h₂ := And.right (Iff.mp (spec_is_spec (fun (u) => ∃ x, ∃ y, (u = (y, x) ∧ (x . R . y))) (rng R × dom R) s) (h₁))
            Exists.elim h₂
            (
              fun (w) =>
                fun (hw : ∃ u, s = (u, w) ∧ (w . R . u)) =>
                  Exists.elim (hw)
                  (
                    fun (u) =>
                      fun (hu : s = (u, w) ∧ (w . R . u)) =>
                        let h₃ := h (w, u) (And.right hu)
                        let h₄ := Iff.mp (cartesian_product_pair_prop A B w u) h₃
                        let h₅ := Iff.mpr (cartesian_product_pair_prop B A u w) (And.intro (And.right h₄) (And.left h₄))
                        eq_subst (fun (p) => p ∈ B × A) (u, w) s (Eq.symm (And.left hu)) (h₅)
                  )
            )

      )




theorem inv_dom: ∀ R, (BinRel R) → dom (R⁻¹) = rng R :=
  fun (R) => fun (h : (BinRel R)) =>
    (
      extensionality (dom (R⁻¹)) (rng R) (
        fun (x) =>
        Iff.intro
        (
          fun (g : x ∈ dom (R⁻¹)) =>
            Exists.elim (Iff.mp (dom_prop (R⁻¹) x) g)
            (
              fun (y) =>
                fun (hy: (x . (R⁻¹) . y)) =>
                  let second:= Iff.mpr (inv_pair_prop R h y x) hy
                  let third: ∃ a, (a . R . x) := Exists.intro y second
                  Iff.mpr (rng_prop R x) third
            )
        )
        (
          fun (g : x ∈ rng R) =>
            Exists.elim (Iff.mp (rng_prop R x) g)
            (
              fun (y) =>
                fun (hy : (y . R . x)) =>
                  let second := Iff.mp (inv_pair_prop R h y x) hy
                  let third: ∃ a, (x . (R⁻¹) . a)  := Exists.intro y second
                  Iff.mpr (dom_prop (R⁻¹) x) third
            )
        )
      )
    )


theorem inv_rng: ∀ R, (BinRel R) → rng (R⁻¹) = dom R :=
  fun (R) => fun (h : (BinRel R)) =>
    let first := inv_is_rel R h
    let second := Eq.symm (inv_dom (R⁻¹) first)
    eq_subst (fun (t) => rng (R⁻¹) = dom t) ((R⁻¹)⁻¹) R (inv_prop R h) second






noncomputable def composition (P Q : Set) : Set := {pr ∈ dom Q × rng P | ∃ x y, (pr = (x, y)) ∧ ∃ z, (x . Q . z) ∧ (z . P . y)}

infix:60 (priority:=high) " ∘ " => composition



theorem composition_is_rel : ∀ P Q, (BinRel (P ∘ Q)) :=
  fun (P) => fun (Q) =>
        fun (z) => fun (r : z ∈ (P ∘ Q)) =>
          let first := specification_set_subset (fun (t) => ∃ x y, (t = (x, y) ∧ ∃ z, (x . Q . z) ∧ (z . P . y) )) (dom Q × rng P) z r
          let second := Iff.mp (cartesian_product_is_cartesian (dom Q) (rng P) z) first
          Exists.elim second
          (
            fun (w) =>
              fun (hw : (w ∈ dom Q ∧ ∃ y ∈ (rng P); z = (w, y))) =>
                Exists.elim (And.right hw)
                (
                  fun (u) =>
                    fun (hu : (u ∈ rng P ∧ z = (w, u))) =>
                      Exists.intro w (Exists.intro u (And.right hu))
                )
          )



theorem composition_pair_prop : ∀ P Q, ∀ x y, (x . (P ∘ Q) . y) ↔ ∃ z, (x . Q . z) ∧ (z . P . y) :=
  fun (P Q x y) =>
    Iff.intro
    (
      fun (h : (x . (P ∘ Q) . y)) =>
        let first := And.right (Iff.mp (spec_is_spec (fun (t) => ∃ x y, (t = (x, y) ∧ ∃ z, (x . Q . z) ∧ (z . P . y) )) (dom Q × rng P) (x, y)) h)
        Exists.elim first
        (
          fun (w) =>
            fun (hw : ∃ y_1, (x, y) = (w, y_1) ∧ ∃ z, (w . Q . z) ∧ (z . P . y_1)) =>
              Exists.elim hw
              (
                fun (u) =>
                  fun (hu : ((x, y) = (w, u)) ∧ ∃ z, (w . Q . z) ∧ (z . P . u)) =>
                    let h₁ := Iff.mp (ordered_pair_set_prop x y w u) (And.left hu)
                    let _ := And.right hu
                    let third := eq_subst (fun (t) => ∃ z, (t . Q . z) ∧ (z . P . u)) (w) (x) (Eq.symm (And.left h₁)) (And.right hu)
                    eq_subst (fun (t) => ∃ z, (x . Q . z) ∧ (z . P . t)) (u) (y) (Eq.symm (And.right h₁)) (third)

              )

        )


    )
    (
      fun (h : ∃ z, (x . Q . z) ∧ (z . P . y) ) =>
        Exists.elim h
        (
          fun (w) =>
            fun (hw : (x . Q . w) ∧ (w . P . y)) =>
              let first := Iff.mpr (spec_is_spec (fun (t) => ∃ x y, (t = (x, y) ∧ ∃ z, (x . Q . z) ∧ (z . P . y) )) (dom Q × rng P) (x, y))

              let second := Iff.mpr (dom_prop Q x) (Exists.intro w (And.left hw))
              let third := Iff.mpr (rng_prop P y) (Exists.intro w (And.right hw))
              let fourth := Iff.mpr (cartesian_product_pair_prop (dom Q) (rng P) x y) (And.intro second third)
              let fifth: ∃ x_1 y_1, (x, y) = (x_1, y_1) ∧ ∃ z, (x_1, z) ∈ Q ∧ (z, y_1) ∈ P := Exists.intro x (Exists.intro y (And.intro (Eq.refl (x, y)) (h)))
              first (And.intro (fourth) (fifth))
        )
    )



theorem rel_subset : (∀ P Q, (BinRel P) → (BinRel Q) → (∀ x y, (x . P . y) → (x . Q . y)) → P ⊆ Q) :=
  fun (P Q) => fun (h : (BinRel P)) => fun (_ : (BinRel Q)) =>
    fun (s : ∀ x y, (x . P . y) → (x . Q . y)) =>
      fun (x) =>
        fun (h₁ : x ∈ P) =>
              let first := h x h₁
              Exists.elim first
              (
                fun (w) =>
                  fun (hw : ∃ u, x = (w, u)) =>
                    Exists.elim hw
                    (
                      fun (u) =>
                        fun (hu: x = (w, u)) =>
                          let second := eq_subst (fun (t) => t ∈ P) x (w, u) (hu) (h₁)
                          let third := s w u second
                          eq_subst (fun (t) => t ∈ Q) (w, u) x (Eq.symm hu) (third)
                    )
              )



theorem relation_equality : (∀ P Q, (BinRel P) → (BinRel Q) → ((∀ x y, (x . P . y) ↔ (x . Q . y)) → P = Q)) :=
    fun (P Q) => fun (h : (BinRel P)) => fun (g : (BinRel Q)) =>
      fun (s : ∀ x y, (x . P . y) ↔ (x . Q . y)) =>
        subset_then_equality P Q (And.intro (rel_subset P Q h g (fun (x) => fun (y) => Iff.mp (s x y))) (rel_subset Q P g h (fun (x) => fun (y) => Iff.mp (iff_comm.mp (s x y)))))


theorem relation_subset_btw : ∀ P Q A B, (P BinRelBtw A AND B) → (∀ x ∈ A; ∀ y ∈ B; (x . P . y) → (x . Q . y)) → (P ⊆ Q) :=
  fun (P Q A B hP h) =>
    fun (z) =>
      fun (hz) =>
        let u₁ := hP z hz
        let u₂ := Iff.mp (cartesian_product_is_cartesian A B z) u₁
        Exists.elim u₂ (
          fun (x) =>
            fun (hx) =>
              Exists.elim (And.right hx) (
                fun (y) =>
                  fun (hy) =>
                    eq_subst (fun (t) => t ∈ Q) (x, y) z (Eq.symm (And.right hy)) (
                      h x (And.left hx) y (And.left hy) (
                        eq_subst (fun (t) => t ∈ P) z (x, y) (And.right hy) (hz)
                      )
                    )
              )
        )


theorem relation_equality_btw : ∀ P Q A B, (P BinRelBtw A AND B) → (Q BinRelBtw A AND B) → (∀ x ∈ A; ∀ y ∈ B; (x . P . y) ↔ (x . Q . y)) → (P = Q) :=
  fun (P Q A B hP hQ h) =>
    subset_then_equality P Q (And.intro (relation_subset_btw P Q A B hP (
      fun (x hx y hy) => Iff.mp (h x hx y hy)
    )) (relation_subset_btw Q P A B hQ (fun (x hx y hy) => Iff.mpr (h x hx y hy))))



theorem composition_pair_assoc: ∀ P Q R x y, (x . ((P ∘ Q) ∘ R) . y) ↔ (x . (P ∘ (Q ∘ R)) . y) :=
  fun (P) => fun (Q) => fun (R) => fun (x) => fun (y) =>
    Iff.intro
    (
      fun (h : (x . ((P ∘ Q) ∘ R) . y)) =>
        let first := Iff.mp (composition_pair_prop (P ∘ Q) R x y) h
        Exists.elim first
        (
          fun (w) =>
            fun (hw : (x . R . w) ∧ (w . (P ∘ Q) . y)) =>
              let second := Iff.mp (composition_pair_prop P Q w y) (And.right hw)
              Exists.elim second
              (
                fun (u) =>
                  fun (hu : (w . Q . u) ∧ (u . P . y)) =>
                    Iff.mpr (composition_pair_prop P (Q ∘ R) x y)
                     (Exists.intro u (And.intro (Iff.mpr (composition_pair_prop Q R x u)
                      (Exists.intro w (And.intro (And.left hw) (And.left hu)))) (And.right hu))
                     )

              )
        )

    )
    (
      fun (h : (x . (P ∘ (Q ∘ R)) . y)) =>
        let first := Iff.mp (composition_pair_prop (P) (Q ∘ R) x y) h
        Exists.elim first
        (
          fun (w) =>
            fun (hw : (x . (Q ∘ R) . w) ∧ (w . P . y)) =>
              let second := Iff.mp (composition_pair_prop Q R x w) (And.left hw)
              Exists.elim second
              (
                fun (u) =>
                  fun (hu : (x . R . u) ∧ (u . Q . w)) =>
                    Iff.mpr (composition_pair_prop (P ∘ Q) R x y)
                    (Exists.intro u (And.intro (And.left hu) (Iff.mpr (composition_pair_prop P Q u y)
                    (Exists.intro w (And.intro (And.right hu) (And.right hw)))))
                    )
              )

        )
    )



theorem composition_assoc : ∀ P Q R, ((P ∘ Q) ∘ R) = (P ∘ (Q ∘ R)) :=
  fun (P) => fun (Q) => fun (R) =>
    relation_equality ((P ∘ Q) ∘ R) (P ∘ (Q ∘ R)) (composition_is_rel (P ∘ Q) (R)) (composition_is_rel (P) (Q ∘ R)) (composition_pair_assoc P Q R)

theorem composition_is_relbtw : ∀ P Q A B C, (P BinRelBtw B AND C) → (Q BinRelBtw A AND B) → ((P ∘ Q) BinRelBtw A AND C) :=
  fun (P Q A B C hP hQ) =>
    let S := fun (pr) => ∃ x y, (pr = (x, y)) ∧ ∃ z, (x . Q . z) ∧ (z . P . y)
    let u₁ : (P ∘ Q) ⊆ ((dom Q) × (rng P)) := specification_set_subset S (dom Q × rng P)
    let u₂ := And.right (And.right (prop_then_binary_relation B C P hP))
    let u₃ := And.left (And.right (prop_then_binary_relation A B Q hQ))
    let u₄ := cartesian_product_subset (dom Q) (rng P) A C (u₃) (u₂)
    fun (x) => fun (hx) => u₄ x (u₁ x hx)


theorem inv_composition_pair_prop : ∀ P Q, (BinRel P) → (BinRel Q) → (∀ x y, (x . ((P ∘ Q)⁻¹) . y) ↔ (x . ((Q⁻¹) ∘ P⁻¹) . y)) :=
  fun (P) => fun (Q) => fun (h : (BinRel P)) => fun (g : (BinRel Q)) =>
    fun (x) => fun (y) =>
      Iff.intro
      (
        fun (h₁ : (x . ((P ∘ Q)⁻¹) . y)) =>
          let first := Iff.mpr (inv_pair_prop (P ∘ Q) (composition_is_rel P Q) y x) h₁
          Exists.elim (Iff.mp (composition_pair_prop P Q y x) first)
          (
            fun (w) =>
              fun (hw : (y . Q . w) ∧ (w . P . x)) =>
                Iff.mpr (composition_pair_prop (Q⁻¹) (P⁻¹) x y) (Exists.intro w (And.intro (Iff.mp (inv_pair_prop P h w x) (And.right hw)) (Iff.mp (inv_pair_prop Q g y w) (And.left hw))))
          )
      )
      (
        fun (h₁ : (x . ((Q⁻¹) ∘ P⁻¹) . y)) =>
          let first := Iff.mp (composition_pair_prop (Q⁻¹) (P⁻¹) x y) h₁
          Exists.elim first
          (
            fun (w) =>
              fun (hw: (x . (P⁻¹) . w) ∧ (w . (Q⁻¹) . y)) =>
                Iff.mp (inv_pair_prop (P ∘ Q) (composition_is_rel P Q) y x)
                 (Iff.mpr (composition_pair_prop P Q y x) (Exists.intro w (And.intro (Iff.mpr (inv_pair_prop Q g y w) (And.right hw)) (Iff.mpr (inv_pair_prop P h w x) (And.left hw)))))
          )
      )



theorem inv_composition_prop : ∀ P Q, (BinRel P) → (BinRel Q) → (P ∘ Q)⁻¹ = ((Q⁻¹) ∘ (P⁻¹)) :=
  fun (P) => fun (Q) => fun (h : (BinRel P)) => fun (g : (BinRel Q)) =>
    relation_equality ((P ∘ Q)⁻¹) ((Q⁻¹) ∘ P⁻¹) (inv_is_rel (P ∘ Q) (composition_is_rel P Q)) (composition_is_rel (Q⁻¹) (P⁻¹)) (inv_composition_pair_prop P Q h g)



theorem inv_union_pair_prop : ∀ P Q, (BinRel P) → (BinRel Q) → ∀ x y, (x . ((P ∪ Q)⁻¹) . y) ↔ (x . (P⁻¹ ∪ Q⁻¹) . y) :=
    fun (P) => fun (Q) => fun (h : (BinRel P)) => fun (g : (BinRel Q)) => fun (x) => fun (y) =>
      Iff.intro
      (
        fun (h₁ : (x . ((P ∪ Q)⁻¹) . y)) =>
          let first := Iff.mpr (inv_pair_prop (P ∪ Q) (union2_rel_is_rel P Q h g) y x) h₁
          let second := Iff.mp (union2_sets_prop P Q (y, x)) first
          Or.elim second
          (
            fun (h₂ : (y . P . x)) =>
              let third := Iff.mp (inv_pair_prop P h y x) h₂
              And.left (union2_sets_subset_prop (P⁻¹) (Q⁻¹)) (x, y) third
          )
          (
            fun (h₂ : (y . Q . x)) =>
              let third := Iff.mp (inv_pair_prop Q g y x) h₂
              And.right (union2_sets_subset_prop (P⁻¹) (Q⁻¹)) (x, y) third
          )
      )
      (
        fun (h₂ : (x . (P⁻¹ ∪ Q⁻¹) . y)) =>
          let first := Iff.mp (union2_sets_prop (P⁻¹) (Q⁻¹) (x, y)) h₂
          Or.elim first
          (
            fun (h₃ : (x . (P⁻¹) . y)) =>
              let second := Iff.mpr (inv_pair_prop P h y x) h₃
              let third := And.left (union2_sets_subset_prop P Q) (y, x) second
              Iff.mp (inv_pair_prop (P ∪ Q) (union2_rel_is_rel P Q h g) y x) (third)
          )
          (
            fun (h₃ : (x . (Q⁻¹) . y)) =>
              let second := Iff.mpr (inv_pair_prop Q g y x) h₃
              let third := And.right (union2_sets_subset_prop P Q) (y, x) second
              Iff.mp (inv_pair_prop (P ∪ Q) (union2_rel_is_rel P Q h g) y x) (third)
          )
      )


theorem inv_union_prop : ∀ P Q, (BinRel P) → (BinRel Q) → (P ∪ Q)⁻¹ = ((P⁻¹) ∪ Q⁻¹) :=
  fun (P) => fun (Q) => fun (h : (BinRel P)) => fun (g : (BinRel Q)) =>
    relation_equality ((P ∪ Q)⁻¹) ((P⁻¹) ∪ Q⁻¹) (inv_is_rel (P ∪ Q) (union2_rel_is_rel P Q h g)) (union2_rel_is_rel (P⁻¹) (Q⁻¹) (inv_is_rel P h) (inv_is_rel Q g)) (inv_union_pair_prop P Q h g)




theorem comp_inv_prop_pair : ∀ P A B, (P BinRelBtw A AND B) → ∀ x y, (x . (comp A B (P⁻¹)) . y) ↔ (x . ((comp B A P)⁻¹) . y) :=
  fun (P) => fun (A) => fun (B) => fun (h : (P BinRelBtw A AND B)) => fun (x) => fun (y) =>
    Iff.intro
    (
      fun (h₁ : (x . (comp A B (P⁻¹)) . y)) =>
        let first := Iff.mp (difference_prop (A × B) (P⁻¹) (x, y)) h₁
        let second := Iff.mpr (cartesian_product_pair_prop B A y x) (Iff.mp (conj_comm (x ∈ A) (y ∈ B)) (Iff.mp (cartesian_product_pair_prop A B x y) (And.left first)))
        let third := Iff.mpr (neg_conj ((y, x) ∈ P) ((x, y) ∈ (P⁻¹)) (inv_pair_prop P (And.left (prop_then_binary_relation A B P h)) y x)) (And.right first)
        let fourth := Iff.mpr (difference_prop (B × A) (P) (y, x)) (And.intro (second) (third))
        Iff.mp (inv_pair_prop (comp B A P) (comp_is_rel B A P) y x) fourth
    )
    (
      fun (h₂ : (x . ((comp B A P)⁻¹) . y)) =>
        let first := Iff.mpr (inv_pair_prop (comp B A P) (comp_is_rel B A P) y x) h₂
        let second := Iff.mp (difference_prop (B × A) (P) (y, x)) first
        let third := Iff.mpr ((cartesian_product_pair_prop A B x y)) ((Iff.mp (conj_comm (y ∈ B) (x ∈ A))) (Iff.mp (cartesian_product_pair_prop B A y x) (And.left second)))
        let fourth := Iff.mp (((neg_conj ((y, x) ∈ P) ((x, y) ∈ (P⁻¹)))) (inv_pair_prop P (And.left ((prop_then_binary_relation A B P h))) y x)) (And.right (second))
        Iff.mpr (difference_prop (A × B) (P⁻¹) (x, y)) (And.intro (third) (fourth))



    )





theorem comp_inv_prop : ∀ P A B, (P BinRelBtw A AND B) → comp A B (P⁻¹) = (comp B A P)⁻¹ :=
  fun (P) => fun (A) => fun (B) => fun (h : (P BinRelBtw A AND B)) =>
    relation_equality (comp A B (P⁻¹)) ((comp B A P)⁻¹) (comp_is_rel A B (P⁻¹)) (inv_is_rel (comp B A P) (comp_is_rel B A P)) (comp_inv_prop_pair P A B h)



theorem union_composition_pair_prop_right : ∀ P Q R, ∀ x y, (x . ((P ∪ Q) ∘ R) . y) ↔ (x . ((P ∘ R) ∪ (Q ∘ R)) . y) :=
  fun (P Q R x y) =>
    let first: (x, y) ∈ (P ∪ Q) ∘ R ↔ ∃ z, (x, z) ∈ R ∧ (z, y) ∈ P ∪ Q  := composition_pair_prop (P ∪ Q) R x y
    let second : (∃ z, (x, z) ∈ R ∧ (z, y) ∈ P ∪ Q) ↔ (∃ z, (x, z) ∈ R ∧ (((z, y) ∈ P) ∨ (z, y) ∈ Q) ) := exists_congr (fun (z) => and_congr_right' (union2_sets_prop P Q (z, y)))
    let third : (x, y) ∈ (P ∪ Q) ∘ R ↔ ∃ z, (x, z) ∈ R ∧ (((z, y) ∈ P) ∨ (z, y) ∈ Q)
      := iff_transitivity ((x, y) ∈ (P ∪ Q) ∘ R) (∃ z, (x, z) ∈ R ∧ (z, y) ∈ P ∪ Q) (∃ z, (x, z) ∈ R ∧ (((z, y) ∈ P) ∨ (z, y) ∈ Q) )
      (first) (second)
    let h₁ : (∃ z, (x, z) ∈ R ∧ ((z, y) ∈ P ∨ (z, y) ∈ Q)) ↔ ∃ z, ((x, z) ∈ R ∧ (z, y) ∈ P) ∨ (x, z) ∈ R ∧ (z, y) ∈ Q := exists_congr (fun (z) => conj_disj_distr_left ((x, z) ∈ R) ((z, y) ∈ P) ((z, y) ∈ Q))
    let fourth : (x, y) ∈ (P ∪ Q) ∘ R ↔ (∃ z, ((x, z) ∈ R ∧ ((z, y) ∈ P)) ∨ ((x, z) ∈ R ∧ (z, y) ∈ Q))
      := iff_transitivity ((x, y) ∈ (P ∪ Q) ∘ R) (∃ z, (x, z) ∈ R ∧ (((z, y) ∈ P) ∨ (z, y) ∈ Q) ) (∃ z, ((x, z) ∈ R ∧ ((z, y) ∈ P)) ∨ ((x, z) ∈ R ∧ (z, y) ∈ Q))
      (third) (h₁)
    let fifth : (x, y) ∈ (P ∪ Q) ∘ R ↔ (∃ z, ((x, z) ∈ R ∧ ((z, y) ∈ P))) ∨ (∃ z, ( (x, z) ∈ R ∧ (z, y) ∈ Q)) :=
      iff_subst_pred_arg (fun (s) => (x, y) ∈ (P ∪ Q) ∘ R ↔ s) (∃ z, ((x, z) ∈ R ∧ ((z, y) ∈ P)) ∨ ((x, z) ∈ R ∧ (z, y) ∈ Q)) ((∃ z, ((x, z) ∈ R ∧ ((z, y) ∈ P))) ∨ (∃ z, ( (x, z) ∈ R ∧ (z, y) ∈ Q)))
      (exits_or_prop (fun (z) => (((x, z) ∈ R) ∧ ((z, y) ∈ P))) (fun (z) =>  ( (x, z) ∈ R ∧ (z, y) ∈ Q))) (fourth)
    let sixth : (x, y) ∈ (P ∪ Q) ∘ R ↔ ((x, y) ∈ (P ∘ R)) ∨ ((x, y) ∈ (Q ∘ R)) :=
      iff_subst_pred_arg (fun (s) => (x, y) ∈ (P ∪ Q) ∘ R ↔ s) ((∃ z, ((x, z) ∈ R ∧ ((z, y) ∈ P))) ∨ (∃ z, ( (x, z) ∈ R ∧ (z, y) ∈ Q))) (((x, y) ∈ (P ∘ R)) ∨ ((x, y) ∈ (Q ∘ R)))
      (disj_congr (∃ z, ((x, z) ∈ R ∧ ((z, y) ∈ P))) ((x, y) ∈ (P ∘ R)) ((∃ z, ( (x, z) ∈ R ∧ (z, y) ∈ Q))) ((x, y) ∈ (Q ∘ R)) (iff_comm.mp (composition_pair_prop P R x y)) (iff_comm.mp (composition_pair_prop Q R x y))) (fifth)

    iff_subst_pred_arg (fun (s) => (x, y) ∈ (P ∪ Q) ∘ R ↔ s) (((x, y) ∈ (P ∘ R)) ∨ ((x, y) ∈ (Q ∘ R))) ((x, y) ∈ ((P ∘ R) ∪ (Q ∘ R))) (iff_comm.mp (union2_sets_prop (P ∘ R) (Q ∘ R) (x, y))) (sixth)


theorem union_composition_prop_right : ∀ P Q R, ((P ∪ Q) ∘ R) = ((P ∘ R) ∪ (Q ∘ R))  :=
  fun (P Q R) =>
    relation_equality ((P ∪ Q) ∘ R) ((P ∘ R) ∪ (Q ∘ R)) (composition_is_rel (P ∪ Q) R) (union2_rel_is_rel (P ∘ R) (Q ∘ R) (composition_is_rel P R) (composition_is_rel Q R)) (union_composition_pair_prop_right P Q R)


theorem union_composition_pair_prop_left : ∀ P Q R, ∀ x y, (x . (P ∘ (Q ∪ R)) . y) ↔ (x . ((P ∘ Q) ∪ (P ∘ R)) . y) :=
  fun (P Q R x y) =>
    let first: (x, y) ∈ P ∘ (Q ∪ R) ↔ ∃ z, (x, z) ∈ Q ∪ R ∧ (z, y) ∈ P  := composition_pair_prop P (Q ∪ R) x y

    let second : (∃ z, (x, z) ∈ (Q ∪ R) ∧ (z, y) ∈ P) ↔ (∃ z, (((x, z) ∈ Q ∨ (x, z) ∈ R) ∧ ((z, y) ∈ P))) := exists_congr (fun (z) => and_congr_left' (union2_sets_prop Q R (x, z)))

    let third : (x, y) ∈ P ∘ (Q ∪ R) ↔ (∃ z, (((x, z) ∈ Q ∨ (x, z) ∈ R) ∧ ((z, y) ∈ P)))
      := iff_transitivity ((x, y) ∈ P ∘ (Q ∪ R)) (∃ z, (x, z) ∈ (Q ∪ R) ∧ (z, y) ∈ P) (∃ z, (((x, z) ∈ Q ∨ (x, z) ∈ R) ∧ ((z, y) ∈ P)))
      (first) (second)

    let h₁ : (∃ z, (((x, z) ∈ Q ∨ (x, z) ∈ R) ∧ ((z, y) ∈ P))) ↔ ∃ z, ((x, z) ∈ Q ∧ (z, y) ∈ P) ∨ ((x, z) ∈ R ∧ (z, y) ∈ P) := exists_congr (fun (z) => conj_disj_distr_right ((z, y) ∈ P) ((x, z) ∈ Q) ((x, z) ∈ R))

    let fourth : (x, y) ∈ P ∘ (Q ∪ R) ↔ ∃ z, ((x, z) ∈ Q ∧ (z, y) ∈ P) ∨ ((x, z) ∈ R ∧ (z, y) ∈ P)
      := iff_transitivity  ((x, y) ∈ P ∘ (Q ∪ R))  (∃ z, (((x, z) ∈ Q ∨ (x, z) ∈ R) ∧ ((z, y) ∈ P))) (∃ z, ((x, z) ∈ Q ∧ (z, y) ∈ P) ∨ ((x, z) ∈ R ∧ (z, y) ∈ P) )
      (third) (h₁)


    let fifth : (x, y) ∈ P ∘ (Q ∪ R) ↔ (∃ z, ((x, z) ∈ Q ∧ (z, y) ∈ P)) ∨ (∃ z, ((x, z) ∈ R ∧ (z, y) ∈ P)) :=
      iff_subst_pred_arg (fun (s) => (x, y) ∈ P ∘ (Q ∪ R) ↔ s) (∃ z, ((x, z) ∈ Q ∧ (z, y) ∈ P) ∨ ((x, z) ∈ R ∧ (z, y) ∈ P))  ((∃ z, ((x, z) ∈ Q ∧ (z, y) ∈ P)) ∨ (∃ z, ((x, z) ∈ R ∧ (z, y) ∈ P)))
      (exits_or_prop (fun (z) => ((x, z) ∈ Q ∧ (z, y) ∈ P)) (fun (z) => ((x, z) ∈ R ∧ (z, y) ∈ P))) (fourth)


    let sixth : (x, y) ∈ P ∘ (Q ∪ R) ↔ ((x, y) ∈ (P ∘ Q)) ∨ ((x, y) ∈ (P ∘ R)) :=
      iff_subst_pred_arg (fun (s) => (x, y) ∈ P ∘ (Q ∪ R) ↔ s) ((∃ z, ((x, z) ∈ Q ∧ (z, y) ∈ P)) ∨ (∃ z, ((x, z) ∈ R ∧ (z, y) ∈ P)))  (((x, y) ∈ (P ∘ Q)) ∨ ((x, y) ∈ (P ∘ R)))
      (disj_congr (∃ z, ((x, z) ∈ Q ∧ (z, y) ∈ P)) ((x, y) ∈ (P ∘ Q)) ((∃ z, ((x, z) ∈ R ∧ (z, y) ∈ P))) ((x, y) ∈ (P ∘ R)) (iff_comm.mp (composition_pair_prop P Q x y)) (iff_comm.mp (composition_pair_prop P R x y))) (fifth)

    iff_subst_pred_arg (fun (s) => (x, y) ∈ P ∘ (Q ∪ R) ↔ s) (((x, y) ∈ (P ∘ Q)) ∨ ((x, y) ∈ (P ∘ R))) ((x, y) ∈ ((P ∘ Q) ∪ (P ∘ R))) (iff_comm.mp (union2_sets_prop (P ∘ Q) (P ∘ R) (x, y))) (sixth)



theorem compostion_union_prop_left : ∀ P Q R, P ∘ (Q ∪ R) = (P ∘ Q) ∪ (P ∘ R) :=
  fun (P Q R) =>
    relation_equality (P ∘ (Q ∪ R)) ((P ∘ Q) ∪ (P ∘ R)) (composition_is_rel (P) (Q ∪ R)) (union2_rel_is_rel (P ∘ Q) (P ∘ R) (composition_is_rel P Q) (composition_is_rel P R)) (union_composition_pair_prop_left P Q R)


theorem monotonic_subset_composition_pair_right : ∀ P Q R, P ⊆ Q → (∀ x y, (x . (P ∘ R) . y) → (x . (Q ∘ R) . y)) :=
  fun (P Q R) => fun (h : P ⊆ Q) =>
    fun (x y) => fun (g : (x . (P ∘ R) . y)) =>
      let first := Iff.mp (composition_pair_prop P R x y) g
      Exists.elim (first)
      (
        fun (w) =>
          fun (hw : (x . R . w) ∧ (w . P . y)) =>
            Iff.mpr (composition_pair_prop Q R x y) (Exists.intro w (And.intro (And.left hw) (h (w, y) (And.right hw))))
      )



theorem monotonic_subset_composition_right : ∀ P Q R, P ⊆ Q → P ∘ R ⊆ Q ∘ R :=
  fun (P Q R) =>
    fun (h : P ⊆ Q) =>
      rel_subset (P ∘ R) (Q ∘ R) (composition_is_rel P R) (composition_is_rel Q R) (
        monotonic_subset_composition_pair_right P Q R h
      )


theorem monotonic_subset_composition_pair_left : ∀ P Q R, P ⊆ Q → (∀ x y, (x . (R ∘ P) . y) → (x . (R ∘ Q) . y)) :=
  fun (P Q R) => fun (h : P ⊆ Q) =>
    fun (x y) => fun (g : (x . (R ∘ P) . y)) =>
      let first := Iff.mp (composition_pair_prop R P x y) g
      Exists.elim (first)
      (
        fun (w) =>
          fun (hw : (x . P . w) ∧ (w . R . y)) =>
            Iff.mpr (composition_pair_prop R Q x y) (Exists.intro w (And.intro (h (x, w) (And.left hw)) (And.right hw)))
      )


theorem monotonic_subset_composition_left : ∀ P Q R, P ⊆ Q → R ∘ P ⊆ R ∘ Q :=
  fun (P Q R) =>
    fun (h : P ⊆ Q) =>
      rel_subset (R ∘ P) (R ∘ Q) (composition_is_rel R P) (composition_is_rel R Q) (
        monotonic_subset_composition_pair_left  P Q R h
      )


theorem intersect2_composition_prop_right: ∀ P Q R, (P ∩ Q) ∘ R ⊆ (P ∘ R) ∩ (Q ∘ R) :=
  fun (P Q R) =>
    fun (x) =>
      fun (h : x ∈ (P ∩ Q) ∘ R) =>
        let first := monotonic_subset_composition_right (P ∩ Q) P R (And.left (intersect_2sets_subset_prop P Q)) x h
        let second := monotonic_subset_composition_right (P ∩ Q) Q R (And.right (intersect_2sets_subset_prop P Q)) x h
        Iff.mpr (intersect_2sets_prop (P ∘ R) (Q ∘ R) x) (And.intro (first) (second))




theorem intersect2_composition_prop_left: ∀ P Q R, P ∘ (Q ∩ R) ⊆ (P ∘ Q) ∩ (P ∘ R) :=
  fun (P Q R) =>
    fun (x) =>
      fun (h : x ∈ (P ∘ (Q ∩ R))) =>
        let first := monotonic_subset_composition_left (Q ∩ R) Q P (And.left (intersect_2sets_subset_prop Q R)) x h
        let second := monotonic_subset_composition_left (Q ∩ R) R P (And.right (intersect_2sets_subset_prop Q R)) x h
        Iff.mpr (intersect_2sets_prop (P ∘ Q) (P ∘ R) x) (And.intro (first) (second))




noncomputable def id_ (A : Set) : Set := {t ∈ (A × A) | ∃ x : Set, t = (x, x)}

theorem id_is_rel : ∀ A, binary_relation (id_ A) :=
  fun (A) =>
    let first := specification_set_subset (fun (u) => ∃ x : Set, u = (x, x)) (A × A)
    And.left (prop_then_binary_relation A A (id_ A) (first))


theorem id_prop : ∀ A x y, (x . (id_ A) . y) → (((x = y) ∧ (x ∈ A)) ∧ (y ∈ A)) :=
  fun (A) => fun (x) => fun (y) => fun (h : (x . (id_ A) . y)) =>
    let first := And.right (Iff.mp (spec_is_spec (fun (u) => ∃ x : Set, u = (x, x)) (A × A) (x, y)) h)
    let second := And.left (Iff.mp (spec_is_spec (fun (u) => ∃ x : Set, u = (x, x)) (A × A) (x, y)) h)
    let third := Iff.mp (cartesian_product_pair_prop A A x y) second
    Exists.elim first
    (
      fun (w) =>
        fun (hw : (x, y) = (w, w)) =>
          let fourth := And.left (Iff.mp (ordered_pair_set_prop x y w w) hw)
          let fifth := And.right (Iff.mp (ordered_pair_set_prop x y w w) hw)
          And.intro (And.intro (eq_subst (fun (u) => u = y) w x (Eq.symm fourth) (Eq.symm fifth)) (And.left third)) (And.right third)
    )



theorem prop_then_id : ∀ A, ∀ x ∈ A; (x . (id_ A) . x) :=
  fun (A) => fun (x) => fun (h : x ∈ A) =>
    Iff.mpr (spec_is_spec (fun (u) => ∃ x : Set, u = (x, x)) (A × A) (x, x))
     (And.intro (Iff.mpr (cartesian_product_pair_prop A A x x) (And.intro h h)) (Exists.intro x (Eq.refl (x, x))))



theorem inv_id : ∀ A, ((id_ A)⁻¹) = (id_ A) :=
  fun (A) =>
    relation_equality ((id_ A)⁻¹) (id_ A) (inv_is_rel (id_ A) (id_is_rel A)) (id_is_rel A) (fun (x) => fun (y) =>
      Iff.intro
      (
        fun (h : (x . ((id_ A)⁻¹) . y) ) =>
          let first := Iff.mpr (inv_pair_prop (id_ A) (id_is_rel A) y x) h
          let second := And.left (And.left (id_prop A y x first))
          eq_subst (fun (u) => (x . (id_ A) . u)) x y (Eq.symm second) (prop_then_id A x (And.right (id_prop A y x first)))
      )
      (
        fun (h : (x . (id_ A) . y)) =>
          let _ := Iff.mp (inv_pair_prop (id_ A) (id_is_rel A) x y) h
          let second := And.left (And.left (id_prop A x y h))
          eq_subst (fun (u) => (u . ((id_ A)⁻¹) . y)) y x (Eq.symm second) (Iff.mp (inv_pair_prop (id_ A) (id_is_rel A) (y) y) (prop_then_id A y (And.right (id_prop A x y h))))

      )
    )



theorem id_rel_composition_right : ∀ A B R, (R BinRelBtw A AND B) → (R ∘ (id_ A)) = R :=
  fun (A B R) => fun (h : (R BinRelBtw A AND B)) =>
    relation_equality (R ∘ id_ A) (R)  (composition_is_rel R (id_ A)) (And.left (prop_then_binary_relation A B R (h)))  (fun (x y) => Iff.intro
    (
      fun (g : ((x . (R ∘ (id_ A)) . y))) =>
        let first := Iff.mp (composition_pair_prop R (id_ A) x y) g
        Exists.elim first
        (
          fun (w) =>
            fun (hw : (x, w) ∈ id_ A ∧ (w, y) ∈ R) =>
              let _ := id_prop A x w (And.left hw)
              eq_subst (fun (u) => (u, y) ∈ R) w x (Eq.symm (And.left (And.left (id_prop A x w (And.left hw))))) (And.right hw)
        )

    )
    (
      fun (g : (x . R . y)) =>

        Iff.mpr (composition_pair_prop R (id_ A) x y) (Exists.intro x (And.intro (prop_then_id A x (And.left (Iff.mp (cartesian_product_pair_prop A B x y) (h (x, y) (g))))) (g)))
    )
    )




theorem id_rel_composition_left : ∀ A B  R, (R BinRelBtw A AND B) → ((id_ B) ∘ R) = R :=
  fun (A B R) => fun (h : (R BinRelBtw A AND B)) =>
    relation_equality (id_ B ∘ R) (R)  (composition_is_rel (id_ B) (R)) (And.left (prop_then_binary_relation A B R (h)))  (fun (x y) => Iff.intro
    (
      fun (g : ((x . (id_ B ∘ R) . y))) =>
        let first := Iff.mp (composition_pair_prop (id_ B) (R) x y) g
        Exists.elim first
        (
          fun (w) =>
            fun (hw : (x, w) ∈ R ∧ (w, y) ∈ id_ B) =>
              eq_subst (fun (u) => (x, u) ∈ R) w y (And.left (And.left (id_prop B w y (And.right hw)))) (And.left hw)
        )

    )
    (
      fun (g : (x . R . y)) =>

        Iff.mpr (composition_pair_prop (id_ B) R x y) (Exists.intro y (And.intro (g) (prop_then_id B y  (
            And.right ( (Iff.mp (cartesian_product_pair_prop A B x y)) (h (x, y) g) )
        ))))
    )
    )



noncomputable def rel_image (X R : Set) := {b ∈ rng R | ∃ a ∈ X; (a . R . b)}

syntax  term ".[" term "]" : term

macro_rules
  | `($R:term .[ $X:term ])  => `(rel_image $X $R)



theorem rng_is_rel_image : ∀ R, (BinRel R) → rng R = R.[dom R] :=
  fun (R) => fun (_ : (BinRel R)) =>
    extensionality (rng R) (R.[dom R]) (
      fun (x) =>
      Iff.intro
      (
        fun (h : x ∈ rng R) =>
          let first := Iff.mp (rng_prop R x) h
          Exists.elim (first) (
            fun (w) =>
              fun (hw : (w . R . x)) =>
                let second := Iff.mpr (dom_prop R w) (Exists.intro x (hw))
                let third: ∃ m ∈ dom R; (m . R . x) := Exists.intro w (And.intro (second) (hw))
                (Iff.mpr (spec_is_spec (fun (u) => ∃ a ∈ (dom R) ; (a . R . u)) (rng R) x)) (And.intro (h) (third))
          )
      )
      (
        fun (h : x ∈ R.[dom R]) =>
        specification_set_subset (fun (u) => ∃ a ∈ (dom R); (a . R . u)) (rng R) x h
      )
    )



theorem rel_pre_image_eq : ∀ Y R, (BinRel R) → R⁻¹.[Y] = {a ∈ dom R | ∃ b ∈ Y; (a . R . b)} :=
  fun (Y) => fun (R) => fun (g : (BinRel R)) =>
    extensionality (R⁻¹.[Y]) ({a ∈ dom R | ∃ b ∈ Y; (a . R . b)}) (
      fun (x) =>
      Iff.intro
      (
        fun (h : x ∈ R⁻¹.[Y]) =>
          let first := inv_rng R g
          let second := And.left (Iff.mp (spec_is_spec (fun (u) => ∃ a ∈ Y; (a . (R⁻¹) . u)) (rng (R⁻¹)) x) h)
          let third := And.right (Iff.mp (spec_is_spec (fun (u) => ∃ a ∈ Y; (a . (R⁻¹) . u)) (rng (R⁻¹)) x) h)
          let fourth := eq_subst (fun (u) => x ∈ u) (rng (R⁻¹)) (dom R) (first) (second)
          Exists.elim third
          (
            fun (w) =>
              fun (hw: w ∈ Y ∧ (w . (R⁻¹) . x)) =>
                let fifth := Iff.mpr (inv_pair_prop R g x w) (And.right hw)
                let sixth: ∃ b ∈ Y; (x . R . b) := Exists.intro w (And.intro (And.left hw) (fifth))
                (Iff.mpr (spec_is_spec (fun (u) => ∃ b ∈ Y; (u . R . b)) (dom R) x)) (And.intro (fourth) (sixth))

          )

      )
      (
        fun (h : x ∈ {a ∈ dom R | ∃ b ∈ Y; (a . R . b)}) =>
          let first := inv_rng R g
          let second := And.left (Iff.mp (spec_is_spec (fun (u) => ∃ b ∈ Y; (u . R . b)) (dom R) x) h)
          let third := And.right (Iff.mp (spec_is_spec (fun (u) => ∃ b ∈ Y; (u . R . b)) (dom R) x) h)
          let fourth := eq_subst (fun (u) => x ∈ u) (dom R) (rng (R⁻¹)) (Eq.symm first) (second)
          Exists.elim third
          (
            fun (w) =>
              fun (hw : w ∈ Y ∧ (x . R . w)) =>
                let fifth := Iff.mp (inv_pair_prop R g x w) (And.right hw)
                let sixth : ∃ a ∈ Y; (a . (R⁻¹) . x) := Exists.intro w (And.intro (And.left hw) (fifth))
                (Iff.mpr (spec_is_spec (fun (u) => ∃ a ∈ Y; (a . (R⁻¹) . u)) (rng (R⁻¹)) x)) (And.intro (fourth) (sixth))
          )
      )
    )



theorem image_prop : ∀ R X y, (y ∈ R.[X] ↔ ∃ x ∈ X; (x . R . y)) :=
  fun (R X) =>
      fun (y) =>
        Iff.intro
        (
          fun (hy : y ∈ R.[X]) =>
            And.right (Iff.mp (spec_is_spec (fun (t) => ∃ x ∈ X; (x . R . t)) (rng R) y) hy)

        )
        (
          fun (hy : ∃ x ∈ X; (x . R . y)) =>
            Exists.elim hy
            (
              fun (x) =>
                fun (hx : x ∈ X ∧ (x . R . y)) =>
                  let t := Iff.mpr (rng_prop R y) (Exists.intro x (And.right hx))

                  Iff.mpr (spec_is_spec (fun (t) => ∃ x ∈ X; (x . R . t)) (rng R) y) (
                    And.intro t (Exists.intro x (And.intro (And.left hx) (And.right hx)))
                  )
            )
        )


theorem preimage_prop : ∀ R Y, (BinRel R) → ∀ x, (x ∈ R⁻¹.[Y] ↔ ∃ y ∈ Y; (x . R . y)) :=
  fun (R Y) =>
    fun (hR : (BinRel R)) =>
      let u := rel_pre_image_eq Y R hR
      let S := {a ∈ dom R | ∃ b ∈ Y; (a . R . b)}
      fun (x) =>
        Iff.intro
        (
          fun (hx : (x ∈ R⁻¹.[Y])) =>
            let v := eq_subst (fun (t) => x ∈ t) (R⁻¹.[Y]) S (u) (hx)
            And.right (Iff.mp (spec_is_spec (fun (t) => ∃ b ∈ Y; (t . R . b)) (dom R) x) (v))
        )
        (
          fun (hx : ∃ y ∈ Y; (x . R . y)) =>
            eq_subst (fun (t) => x ∈ t) S (R⁻¹.[Y]) (Eq.symm (u)) (
              Iff.mpr (spec_is_spec (fun (t) => ∃ b ∈ Y; (t . R . b)) (dom R) x) (
                And.intro (
                  Iff.mpr (dom_prop R x) (
                    Exists.elim hx (
                      fun (y) =>
                        fun (hxp : y ∈ Y ∧ (x . R . y)) =>
                          Exists.intro y (And.right hxp)
                    )
                  )
                ) (hx)
              )
            )
        )



theorem dom_preimage : ∀ A B P, (P BinRelBtw A AND B) → dom P = P⁻¹.[B] :=
  fun (A B P) => fun (h₁ : (P BinRelBtw A AND B)) =>
    extensionality (dom P) (P⁻¹.[B]) (
      fun (x) =>
        Iff.intro
        (
          fun (s : x ∈ dom P) =>
            let first := Iff.mp (dom_prop P x) s
            Exists.elim first
            (
              fun (w) =>
                fun (hw : (x, w) ∈ P) =>
                  let second := rel_pre_image_eq B P (And.left (prop_then_binary_relation A B P h₁))
                  eq_subst (fun (u) => x ∈ u) (({a ∈ dom P | ∃ b ∈ B; (a . P . b)})) (P⁻¹.[B])  (Eq.symm second) (
                    Iff.mpr (spec_is_spec (fun (u) => ∃ b ∈ B; (u . P . b)) (dom P) x) (And.intro (s) (Exists.intro w (And.intro (And.right (Iff.mp (cartesian_product_pair_prop A B x w) (h₁ (x, w) hw))) (hw))))

                  )

            )

        )
        (
          fun (s : x ∈ P⁻¹.[B]) =>
            let first := rel_pre_image_eq B P (And.left (prop_then_binary_relation A B P h₁))
            let second:= eq_subst (fun (u) => x ∈ u) (P⁻¹.[B]) ({a ∈ dom P | ∃ b ∈ B; (a . P . b)})  (first) (s)

            specification_set_subset (fun (u) => ∃ b ∈ B; (u . P . b)) (dom P) x (second)

        )
    )


  theorem rel_image_id : ∀ A X, (X ⊆ A) → (id_ A).[X] = X :=
    fun (A X hX) =>
      extensionality ((id_ A).[X]) X (
        fun (x) =>
          Iff.intro
          (
            fun (hx) =>
              let u₁ := Iff.mp (image_prop (id_ A) X x) hx
              Exists.elim u₁ (
                fun (y) =>
                  fun (hy) =>
                    let u₂ := (id_prop A y x) (And.right hy)

                    eq_subst (fun (t) => t ∈ X) (y) (x) (And.left (And.left u₂)) (And.left hy)
              )

          )
          (
            fun (hx) =>
              Iff.mpr (image_prop (id_ A) X x) (
                Exists.intro x (
                  And.intro (hx) (prop_then_id A x (hX x (hx)))
                )
              )
          )
      )


theorem rel_image_union : ∀ X Y R, (BinRel R) → R.[X ∪ Y] = R.[X] ∪ R.[Y] :=
  fun (X) => fun (Y) => fun (R) => fun (_ : (BinRel R)) =>
    extensionality (R.[X ∪ Y]) (R.[X] ∪ R.[Y])
    (
      fun (b) =>
        let first : b ∈ R.[X ∪ Y] ↔ b ∈ rng R ∧ (∃ s, (s ∈ X ∪ Y) ∧ (s . R . b)) :=
          spec_is_spec (fun (u) => ∃ a ∈ (X ∪ Y); (a . R . u)) (rng R) (b)

        let second : b ∈ R.[X ∪ Y] ↔ b ∈ rng R ∧ (∃ s, (s ∈ X ∨ s ∈ Y) ∧ (s . R . b)) :=
          iff_subst_pred_arg (fun (u) => b ∈ R.[X ∪ Y] ↔ b ∈ rng R ∧ u) (∃ s, (s ∈ X ∪ Y) ∧ (s . R . b)) (∃ s, (s ∈ X ∨ s ∈ Y) ∧ (s . R . b))
          (exists_congr (fun (z) => and_congr_left' (union2_sets_prop X Y z))) (first)

        let third : b ∈ R.[X ∪ Y] ↔ b ∈ rng R ∧ (∃ s, (s ∈ X ∧ (s . R . b)) ∨ (s ∈ Y ∧ (s . R . b))) :=
          iff_subst_pred_arg (fun (u) => b ∈ R.[X ∪ Y] ↔ b ∈ rng R ∧ u) (∃ s, (s ∈ X ∨ s ∈ Y) ∧ (s . R . b)) (∃ s, (s ∈ X ∧ (s . R . b)) ∨ (s ∈ Y ∧ (s . R . b)))
          (exists_congr (fun (z) => conj_disj_distr_right (z . R . b) (z ∈ X) (z ∈ Y))) (second)

        let fourth : b ∈ R.[X ∪ Y] ↔ b ∈ rng R ∧ ((∃ s, (s ∈ X) ∧ (s . R . b)) ∨ (∃ s, (s ∈ Y) ∧ (s . R . b))) :=
          iff_subst_pred_arg (fun (u) => b ∈ R.[X ∪ Y] ↔ b ∈ rng R ∧ u) (∃ s, (s ∈ X ∧ (s . R . b)) ∨ (s ∈ Y ∧ (s . R . b))) ((∃ s, (s ∈ X) ∧ (s . R . b)) ∨ (∃ s, (s ∈ Y) ∧ (s . R . b)))
          (exists_or) (third)

        let fifth : b ∈ R.[X ∪ Y] ↔ (b ∈ rng R ∧ (∃ s, (s ∈ X) ∧ (s . R . b))) ∨ (b ∈ rng R ∧ (∃ s, (s ∈ Y) ∧ (s . R . b))) :=
          iff_subst_pred_arg (fun (u) => b ∈ R.[X ∪ Y] ↔ u) (b ∈ rng R ∧ ((∃ s, (s ∈ X) ∧ (s . R . b)) ∨ (∃ s, (s ∈ Y) ∧ (s . R . b)))) ((b ∈ rng R ∧ (∃ s, (s ∈ X) ∧ (s . R . b))) ∨ (b ∈ rng R ∧ (∃ s, (s ∈ Y) ∧ (s . R . b))))
          (conj_disj_distr_left (b ∈ rng R) ((∃ s, (s ∈ X) ∧ (s . R . b))) ((∃ s, (s ∈ Y) ∧ (s . R . b)))) (fourth)


        let sixth : b ∈ R.[X ∪ Y] ↔ (b ∈ R.[X]) ∨ (b ∈ R.[Y]) :=
          iff_subst_pred_arg (fun (u) => b ∈ R.[X ∪ Y] ↔ u) ((b ∈ rng R ∧ (∃ s, (s ∈ X) ∧ (s . R . b))) ∨ (b ∈ rng R ∧ (∃ s, (s ∈ Y) ∧ (s . R . b)))) ((b ∈ R.[X]) ∨ (b ∈ R.[Y]))
          (disj_congr ((b ∈ rng R ∧ (∃ s, (s ∈ X) ∧ (s . R . b)))) ((b ∈ R.[X])) (b ∈ rng R ∧ (∃ s, (s ∈ Y) ∧ (s . R . b))) (b ∈ R.[Y])
          (iff_comm.mp (spec_is_spec (fun (u) => ∃ s ∈ X; (s . R . u)) (rng R) b)) (iff_comm.mp
          (spec_is_spec (fun (u) => ∃ s ∈ Y; (s . R . u)) (rng R) b))
          ) (fifth)

        iff_subst_pred_arg (fun (u) => b ∈ R.[X ∪ Y] ↔ u) ((b ∈ R.[X]) ∨ (b ∈ R.[Y])) (b ∈ R.[X] ∪ R.[Y])
        (iff_comm.mp (union2_sets_prop (R.[X]) (R.[Y]) b)) (sixth)
    )


theorem rel_preimage_union : ∀ X Y R , (BinRel R) → R⁻¹.[X ∪ Y] = R⁻¹.[X] ∪ R⁻¹.[Y] :=
  fun (X Y R) => fun (h : (BinRel R)) =>
    rel_image_union X Y (R⁻¹) (inv_is_rel R h)



theorem monotonic_rel_image : ∀ X Y R, (BinRel R) → X ⊆ Y → R.[X] ⊆ R.[Y] :=
  fun (X Y R) => fun (_ : (BinRel R)) => fun (g : X ⊆ Y) =>
    fun (x) => fun (s : x ∈ R.[X]) =>
      let first := Iff.mp (spec_is_spec (fun (u) => ∃ a ∈ X; (a . R . u)) (rng R) x) s
      Exists.elim (And.right (first))
      (
        fun (w) =>
          fun (hw : w ∈ X ∧ (w . R . x)) =>
            let second := g w (And.left hw)
            (Iff.mpr (spec_is_spec (fun (u) => ∃ a ∈ Y; (a . R . u)) (rng R) x)) (And.intro (And.left first) (Exists.intro w (And.intro (second) (And.right hw))))
      )



theorem monotonic_rel_preimage : ∀ X Y R, (BinRel R) → X ⊆ Y → R⁻¹.[X] ⊆ R⁻¹.[Y] :=
  fun (X Y R) => fun (h : (BinRel R)) => fun (g : X ⊆ Y) =>
    monotonic_rel_image X Y (R⁻¹) (inv_is_rel R h) g


theorem lemma_subset_intersec : ∀ A B C, A ⊆ B → A ⊆ C → A ⊆ (B ∩ C) :=
  fun (A B C) => fun (h : A ⊆ B) => fun (g : A ⊆ C) =>
    fun (x) => fun (t : x ∈ A) =>
      Iff.mpr (intersect_2sets_prop B C x) (And.intro (h x t) (g x t))


theorem rel_image_inter : ∀ X Y R, (BinRel R) → R.[X ∩ Y] ⊆ (R.[X] ∩ R.[Y]) :=
  fun (X Y R) => fun (h : (BinRel R)) =>
    let first := And.left (intersect_2sets_subset_prop X Y)
    let second := monotonic_rel_image (X ∩ Y) X R h first
    let third := And.right (intersect_2sets_subset_prop X Y)
    let fourth := monotonic_rel_image (X ∩ Y) Y R h third
    lemma_subset_intersec (R.[X ∩ Y]) (R.[X]) (R.[Y]) (second) (fourth)



theorem rel_preimage_inter : ∀ X Y R, (BinRel R) → R⁻¹.[X ∩ Y] ⊆ (R⁻¹.[X] ∩ R⁻¹.[Y]) :=
  fun (X Y R) => fun (h : (BinRel R)) =>
  rel_image_inter X Y (R⁻¹) (inv_is_rel R (h))




theorem rel_image_composition : ∀ P Q X, (P ∘ Q).[X] = P.[Q.[X]] :=
  fun (P Q X) =>
    extensionality ((P ∘ Q).[X]) (P.[Q.[X]]) (
      fun (c) =>

        let first: c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ (∃ a ∈ X; (a . (P ∘ Q) . c))
          := spec_is_spec (fun (u) => ∃ a ∈ X; (a . (P ∘ Q) . u)) (rng (P ∘ Q)) c

        let second : c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ (∃ a ∈ X; (∃ b, (a . Q . b) ∧ (b . P . c))) :=
          iff_subst_pred_arg (fun (u) => c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ u) (∃ a ∈ X; (a . (P ∘ Q) . c))  (∃ a ∈ X; (∃ b, (a . Q . b) ∧ (b . P . c)))
          (exists_congr (fun (a) => and_congr_right' (composition_pair_prop P Q a c))) (first)

        let third : c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ ∃ a, ∃ b, (a ∈ X ∧ (a . Q . b) ∧ (b . P . c)) :=
          iff_subst_pred_arg (fun (u) => c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ u) ((∃ a ∈ X; (∃ b, (a . Q . b) ∧ (b . P . c)))) ( ∃ a, ∃ b, (a ∈ X ∧ (a . Q . b) ∧ (b . P . c)))
          (exists_congr (fun (_) => iff_comm.mp (exists_and_left))) (second)

        let fourth : c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ ∃ b, ∃ a, (a ∈ X ∧ (a . Q . b) ∧ (b . P . c)) :=
          iff_subst_pred_arg (fun (u) => c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ u) ( ∃ a, ∃ b, (a ∈ X ∧ (a . Q . b) ∧ (b . P . c))) (∃ b, ∃ a, (a ∈ X ∧ (a . Q . b) ∧ (b . P . c)))
          (exists_comm) (third)

        let fifth : c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ ∃ b, ∃ a, (((a ∈ X ∧ (a . Q . b))) ∧ (b . P . c)) :=
          iff_subst_pred_arg (fun (u) => c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ u) (∃ b, ∃ a, (a ∈ X ∧ (a . Q . b) ∧ (b . P . c)) ) (∃ b, ∃ a, (((a ∈ X ∧ (a . Q . b))) ∧ (b . P . c)))
          (exists_congr (fun (_) => exists_congr (fun (_) => iff_comm.mp and_assoc))) (fourth)

        let sixth : c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ ∃ b, (∃ a, (a ∈ X ∧ (a . Q . b))) ∧ (b . P . c) :=
          iff_subst_pred_arg (fun (u) => c ∈ (P ∘ Q).[X] ↔ c ∈ rng (P ∘ Q) ∧ u) (∃ b, ∃ a, (((a ∈ X ∧ (a . Q . b))) ∧ (b . P . c))) (∃ b, (∃ a, (a ∈ X ∧ (a . Q . b))) ∧ (b . P . c))
          (exists_congr (fun (_) => exists_and_right)) (fifth)

        Iff.intro
        (
          fun (h : c ∈ (P ∘ Q).[X]) =>
            let h₁ := Iff.mp sixth h
            let _ := And.left h₁
            let h₃ := And.right h₁
            Exists.elim h₃
            (
              fun (w) =>
                fun (hw : (∃ a, (a ∈ X ∧ (a . Q . w))) ∧ (w . P . c)) =>
                  Exists.elim (And.left hw)
                  (
                    fun (u) =>
                      fun (hu : u ∈ X ∧ (u . Q . w)) =>
                        let h₄ := Iff.mpr (rng_prop Q w)  (Exists.intro u (And.right hu))
                        let h₅ : w ∈ Q.[X] := Iff.mpr (spec_is_spec (fun (u) => ∃ a ∈ X; (a . Q . u)) (rng Q) w) (And.intro (h₄) (Exists.intro u (And.intro (And.left hu) (And.right (hu)))))
                        let h₆ := Iff.mpr (rng_prop P c) (Exists.intro w (And.right hw))
                        let h₇ : c ∈ P.[Q.[X]] := (Iff.mpr (spec_is_spec (fun (u) => ∃ a ∈ Q.[X]; (a . P . u)) (rng P) c)) (And.intro (h₆) (Exists.intro w (And.intro (h₅)  (And.right hw))))
                        h₇
                  )


            )

        )
        (
          fun (h : c ∈ P.[Q.[X]]) =>
            let h₁ := Iff.mp (spec_is_spec (fun (u) => ∃ a ∈ Q.[X]; (a . P . u)) (rng P) c) h
            let _ := And.left h₁
            let h₃ := And.right h₁
            Exists.elim h₃
            (
              fun (w) =>
                fun (hw : w ∈ Q.[X] ∧ (w . P . c)) =>
                  let h₄ := Iff.mp (spec_is_spec (fun (u) => ∃ a ∈ X; (a . Q . u)) (rng Q) w) (And.left hw)
                  Exists.elim (And.right h₄)
                  (
                    fun (u) =>
                      fun (hu : u ∈ X ∧ (u . Q . w)) =>
                        (Iff.mpr (sixth)) (And.intro (Iff.mpr (rng_prop (P ∘ Q) c) (Exists.intro u ( (Iff.mpr (composition_pair_prop P Q u c)) (Exists.intro w (And.intro (And.right hu) (And.right hw))))))
                         (Exists.intro w (And.intro (Exists.intro u (hu)) (And.right hw)))
                        )
                  )
            )
        )

    )


theorem rel_preimage_composition : ∀ P Q X, (BinRel P) → (BinRel Q) → (P ∘ Q)⁻¹.[X] = Q⁻¹.[P⁻¹.[X]] :=
  fun (P Q X) => fun (h : (BinRel P)) => fun (g : (BinRel Q)) =>
    let first : (P ∘ Q)⁻¹.[X] = (Q⁻¹ ∘ P⁻¹).[X] :=
      eq_subst (fun (u) => (P ∘ Q)⁻¹.[X] = u.[X]) ((P ∘ Q)⁻¹) (Q⁻¹ ∘ P⁻¹) (inv_composition_prop P Q h g) (Eq.refl ((P ∘ Q)⁻¹.[X]))

    eq_subst (fun (u) => (P ∘ Q)⁻¹.[X] = u) ((Q⁻¹ ∘ P⁻¹).[X]) (Q⁻¹.[P⁻¹.[X]]) (rel_image_composition (Q⁻¹) (P⁻¹) X) (first)




theorem rel_image_diff : ∀ X Y R, (R.[X] \ R.[Y]) ⊆ (R.[X \ Y]) :=
  fun (X Y R) =>
      fun (y) =>
        fun (hy : y ∈ (R.[X] \ R.[Y])) =>
          let u := Iff.mp (difference_prop (R.[X]) (R.[Y]) y) hy
          let v := Iff.mp (image_prop R X y) (And.left u)
          Exists.elim v
          (
            fun (m) =>
              fun (hm : m ∈ X ∧ (m . R . y)) =>
                let s := Iff.mpr (image_prop R Y y)
                let s₂ := Iff.mp (contraposition (∃ x ∈ Y; (x . R . y)) ((y ∈ (R.[Y])))) s (And.right u)
                let s₃ := Iff.mpr (morgan_uni Set (fun (x) => (x ∈ Y ∧ (x . R . y)))) s₂ m
                let s₄ := Iff.mpr (morgan_conj (m ∈ Y) (m . R . y)) s₃
                Or.elim s₄
                (
                  fun (hmy : m ∉ Y) =>
                    Iff.mpr (image_prop R (X \ Y) y) (
                      Exists.intro m (And.intro (
                        Iff.mpr (difference_prop X Y m) (And.intro (And.left hm) (hmy))
                      ) (And.right hm))
                    )
                )
                (
                  fun (hmr : ¬ (m . R . y)) =>
                    False.elim (hmr (And.right hm))
                )




          )


theorem rel_preimage_diff : ∀ X Y R, (R⁻¹.[X] \ R⁻¹.[Y]) ⊆ (R⁻¹.[X \ Y]) :=
  fun (X Y R) =>
      rel_image_diff X Y (R⁻¹)
