theorem uni (α : Type) : ∀ _ : α, True :=
   fun (_ : α) => True.intro


theorem exi_uni_then_uni (α : Type) (P : α → Prop) : (∃ _ : α, ∀ x : α, P x) → (∀ x : α, P x) :=
   fun (h : (∃ _ : α, ∀ x : α, P x)) =>
      Exists.elim h
      (
         fun (_ : α) =>
            fun (hw : ∀ x : α, P x) =>
               hw
      )


theorem exi_exi_then_exi (α : Type) (P : α → Prop) : (∃ _ : α, ∃ x : α, P x) → (∃ x : α, P x) :=
   fun (h : (∃ _ : α, ∃ x : α, P x)) =>
      Exists.elim h
      (
         fun (_ : α) =>
            fun (hw : ∃ x : α, P x) =>
               hw
      )


theorem uni_uni_then_uni (α : Type) (P : α → Prop) : (∀ _ : α, ∀ x : α, P x) → (∀ x : α, P x) :=
   fun (h : (∀ _ : α, ∀ x : α, P x)) =>
      fun (s : α) =>
         (h s s)




theorem change_variable_uni (α : Type) (P: α → Prop) : (∀ x : α, P x) ↔ (∀ y : α, P y) :=
   Iff.intro
   (
      fun (h : (∀ x : α, P x)) =>
         fun (y : α) => h y
   )
   (
      fun (h : (∀ y : α, P y)) =>
         fun (x : α) => h x
   )




theorem change_variable_exi (α : Type) (P: α → Prop) : (∃ x : α, P x) ↔ (∃ y : α, P y) :=
   Iff.intro
   (
      fun (h : (∃ x : α, P x)) =>
         Exists.elim h
         (
            fun (w : α) =>
               fun (hw : P w) =>
                  Exists.intro w hw
         )
   )
   (
      fun (h :(∃ y : α, P y)) =>
         Exists.elim h
         (
            fun (w : α) =>
               fun (hw : P w) =>
                  Exists.intro w hw
         )
   )



theorem uni_congr (α : Type) (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∀ x : α, P x) ↔ (∀ x : α, Q x)) :=
   fun (h : (∀ x : α, (P x ↔ Q x))) =>
      Iff.intro
      (fun (s : (∀ x : α, P x)) =>
         fun (t : α) =>
            (Iff.mp (h t)) (s t)
      )
      (
         fun (s : (∀ x : α, Q x)) =>
            fun (t : α) =>
               (Iff.mpr (h t) (s t))
      )




theorem exi_congr (α : Type) (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∃ x : α, P x) ↔ (∃ x: α, Q x)) :=
   fun (h : (∀ x : α, (P x ↔ Q x))) =>
      Iff.intro
      (
         fun (s : (∃ x : α, P x)) =>
            Exists.elim s
            (
               fun (w : α) =>
                  fun (hw : P w) =>
                     Exists.intro w ((Iff.mp (h w)) hw)
            )
      )
      (
         fun (s : (∃ x : α, Q x)) =>
         Exists.elim s
         (
            fun (w : α) =>
               fun (hw : Q w) =>
                  Exists.intro w ((Iff.mpr (h w) hw))
         )
      )







theorem uni_comm (α : Type) (P : α →  β → Prop) : (∀ x : α, ∀ y : β, P x y) ↔ (∀ y : β, ∀ x : α, P x y) :=
   Iff.intro
   (fun (h : (∀ x : α, ∀ y : β, P x y)) =>
      fun (y : β) =>
         fun (x : α) =>
            h x y
   )
   (fun (h : (∀ y : β, ∀ x : α, P x y)) =>
      fun (x : α) =>
         fun (y : β) =>
            h y x
   )



theorem exi_comm (α : Type) (P : α → β → Prop) : (∃ x : α, ∃ y : β, P x y) ↔ (∃ y : β, ∃ x : α, P x y) :=
Iff.intro
(fun (h : (∃ x : α, ∃ y : β, P x y)) =>
   Exists.elim h
   (
      fun (w : α) =>
         fun (hw : ∃ y : β, P w y) =>
            Exists.elim hw
            (
               fun (u : β) =>
                  fun (hu : P w u) =>
                     Exists.intro u (Exists.intro w hu)
            )
   )
)
(
   fun (h : (∃ y : β, ∃ x : α, P x y)) =>
      Exists.elim h
      (
         fun (u : β) =>
            fun (hu : ∃ x : α, P x u) =>
               Exists.elim hu
               (
                  fun (w : α) =>
                     fun (hw : P w u) =>
                        Exists.intro w (Exists.intro u hw)
               )
      )
)





theorem exi_uni_then_uni_exi (α : Type) (P : α → β → Prop) : (∃ x : α, ∀ y : β, P x y) → (∀ y : β, ∃ x : α, P x y) :=
   (
      fun (h : (∃ x : α, ∀ y : β, P x y)) =>
         Exists.elim h
         (
            fun (w : α) =>
               fun (hw : (∀ y : β, P w y)) =>
                  fun (y : β) =>
                     Exists.intro w (hw y)
         )
   )






theorem uni_conj (α : Type) (P Q: α → Prop) : (∀ x: α, P x ∧ Q x) ↔ (∀ x : α, P x) ∧ (∀ x : α, Q x) :=
   Iff.intro
   (fun (h : ∀ x : α, P x ∧ Q x) =>
      And.intro
         (fun (y : α) => And.left (h y))
         (fun (y : α) => And.right (h y))
   )
   (fun (h : (∀ x: α, P x) ∧ (∀ x : α, Q x)) =>
      fun (y : α) => And.intro
         (And.left h y)
         (And.right h y)
   )



theorem exi_disj (α : Type) (P Q : α → Prop) : (∃ x : α, P x ∨ Q x) ↔ (∃ x : α, P x) ∨ (∃ x: α, Q x) :=
   Iff.intro
   (fun (h : ∃ x: α, P x ∨ Q x) =>
      Exists.elim h
      (fun (w : α) =>
         fun (hw : P w ∨ Q w) =>
            Or.elim hw
            (fun (s : P w) => (Or.inl : (∃ x : α, P x) → (∃ x : α, P x) ∨ (∃ x : α, Q x)) (Exists.intro w s) )
            (fun (t : Q w) => (Or.inr : (∃ x : α, Q x) → (∃ x : α, P x) ∨ (∃ x : α, Q x)) (Exists.intro w t))
      )
   )
   (fun (h : (∃ x : α, P x) ∨ (∃ x : α, Q x)) =>
      Or.elim h
      (fun (s : (∃ x : α, P x)) =>
         Exists.elim s
         (fun (w : α) =>
            fun (hw : P w) =>
               Exists.intro w ((Or.inl : P w → P w ∨ Q w) hw)
         )

      )
      (fun (t : (∃ x : α, Q x)) =>
         Exists.elim t
         (fun (w : α) =>
            fun (hw : Q w) =>
               Exists.intro w ((Or.inr : Q w → P w ∨ Q w) hw)
         )
      )
   )





theorem morgan_uni (α : Type) (P : α → Prop) : (∀ x : α, ¬ P x) ↔ (¬ ∃ x : α, P x) :=
   Iff.intro
   (
      fun (h : (∀ x : α, ¬ P x)) =>
         fun (g : ∃ x : α, P x) =>
            Exists.elim g
            (fun (w : α) =>
               fun (hw : P w) =>
                  (h w) hw
            )
   )
   (fun (h : (¬ ∃ x : α, P x)) =>
      fun (s : α) =>
         fun (t : P s) => h (Exists.intro s t)
   )



theorem morgan_exi_mp (α : Type) (P : α → Prop) : (∃ x : α, ¬ P x) →  (¬ ∀ x : α, P x) :=
   fun (h : (∃ x : α, ¬P x)) =>
      fun (g : ∀ x : α, P x) => Exists.elim h
                                 (fun (w : α) =>
                                    fun (hw : ¬P w) =>
                                       hw (g w)
                                 )




theorem brackets_exi_conj (α : Type) (P : Prop) (Q : α → Prop) : (∃ x : α, P ∧ Q x) ↔ (P ∧ ∃ x : α, Q x) :=
   Iff.intro
   (fun (h : (∃ x : α, P ∧ Q x)) =>
      Exists.elim h
      (
         fun (w : α) =>
            fun (hw : P ∧ Q w) =>
               And.intro (And.left hw) (Exists.intro w (And.right hw))
      ))
   (
      fun (h : (P ∧ ∃ x : α, Q x)) =>
         Exists.elim (And.right h)
         (
            fun (w : α) =>
               fun (hw : Q w) =>
                  Exists.intro w (And.intro (And.left h) (hw))
         )
   )


theorem brackets_uni_conj_mpr (α : Type) (P : Prop) (Q : α → Prop) : (P ∧ ∀ x : α, Q x) → (∀ x : α, P ∧ Q x) :=
(
      fun (h : (P ∧ ∀ x : α, Q x)) =>
         fun (s : α) => And.intro (And.left h) (And.right h s)
)


theorem brackets_exi_disj_mp (α : Type) (P : Prop) (Q : α → Prop) : (∃ x : α, P ∨ Q x) → (P ∨ ∃ x : α, Q x) :=
   fun (h : (∃ x : α, P ∨ Q x)) =>
      Exists.elim h
      (
         fun (w : α) =>
         fun (hw : P ∨ Q w) =>
            Or.elim hw
            (fun (s : P) => (Or.inl : P → (P ∨ ∃ x : α, Q x)) s)
            (fun (s : Q w) => (Or.inr : (∃ x : α, Q x) → (P ∨ ∃ x : α, Q x)) (Exists.intro w s))
      )


theorem brackets_uni_disj_mpr (α : Type) (P : Prop) (Q : α → Prop) : (P ∨ ∀ x : α, Q x) → (∀ x : α, P ∨ Q x) :=

   (
      fun (h : (P ∨ ∀ x : α, Q x)) =>
         fun (s : α) => Or.elim h
                        (fun (r : P) => (Or.inl : P → P ∨ Q s) r)
                        (fun (r : (∀ x : α, Q x)) => (Or.inr : Q s → P ∨ Q s) (r s))
   )




theorem brackets_left_uni_impl (α : Type) (P : Prop) (Q : α → Prop) : (P → ∀ x : α, Q x) ↔ (∀ x : α, (P → Q x)) :=
   Iff.intro
   (
      fun (h : (P → ∀ x : α, Q x)) =>
         fun (s : α) =>
            fun (t : P) => h t s
   )
   (fun (h : (∀ x : α, (P → Q x))) =>
      fun (s : P) =>
         fun (r : α) => h r s
   )


theorem brackets_left_exi_impl_mpr (α : Type) (P : Prop) (Q : α → Prop) : (∃ x : α, (P → Q x)) → (P → ∃ x : α, Q x) :=
   fun (h : (∃ x : α, (P → Q x))) =>
      Exists.elim h
      (
         fun (w : α) =>
            fun (hw : (P → Q w)) =>
               fun (t : P) =>
                  Exists.intro w (hw t)
      )



theorem brackets_right_uni_impl_mpr (α : Type) (P : α → Prop) (Q : Prop) : (∃ x : α, (P x → Q)) → ((∀ x : α, P x) → Q) :=
   (
      fun (h : ∃ x : α, (P x → Q)) =>
         Exists.elim h
         (
            fun (w : α) =>
               fun (hw : (P w → Q)) =>
                  fun (s : (∀ x : α, P x)) =>
                     hw (s w)
         )
   )



theorem brackets_right_exi_impl (α : Type) (P : α → Prop) (Q : Prop) : ((∃ x : α, P x) → Q) ↔ (∀ x : α, (P x → Q)) :=
   Iff.intro
   (
      fun (h : ((∃ x : α, P x) → Q)) =>
         fun (s : α) =>
            fun (t : P s) =>
               h (Exists.intro s t)

   )
   (
      fun (h : (∀ x : α, (P x → Q))) =>
      fun (s : (∃ t : α, P t)) =>
         Exists.elim s
         (
            fun (w : α) =>
               fun (hw : P w) =>
                  h w hw
         )
   )


theorem inh_exi (α : Type) [Inhabited α] : ∃ _ : α, True :=
   Exists.intro (Inhabited.default : α) True.intro


theorem inh_uni_exi_then_exi (α : Type) [Inhabited α] (P : α → Prop) : (∀ _ : α, ∃ x : α, P x) → (∃ x : α, P x) :=
   fun (h : (∀ _ : α, ∃ x : α, P x)) =>
      h (Inhabited.default : α)




theorem inh_uni_then_exi (α : Type) [Inhabited α] (P : α → Prop) : (∀ x : α, P x) → (∃ x : α, P x) :=
   (fun (h : (∀ x : α, P x)) =>
      Exists.intro (Inhabited.default : α) (h (Inhabited.default : α))
   )


theorem inh_brackets_uni_conj (α : Type) [Inhabited α] (P : Prop) (Q : α → Prop) : (∀ x : α, P ∧ Q x) ↔ (P ∧ ∀ x : α, Q x) :=
   Iff.intro
   (fun (h : (∀ x : α, P ∧ Q x)) => And.intro
      (And.left (h (Inhabited.default : α))) (fun (s : α) => And.right (h s))
   )
   (brackets_uni_conj_mpr α P Q)


theorem inh_brackets_exi_disj (α : Type) [Inhabited α] (P : Prop) (Q : α → Prop) : (∃ x : α, P ∨ Q x) ↔ (P ∨ ∃ x : α, Q x) :=
   Iff.intro
   (brackets_exi_disj_mp α P Q)
   (
      fun (h : (P ∨ ∃ x : α, Q x)) =>
         Or.elim h
         (fun (r : P) => Exists.intro (Inhabited.default : α)
            ((Or.inl : P → P ∨ Q (Inhabited.default : α)) r)
         )
         (fun (r : (∃ x : α, Q x)) =>
            Exists.elim r
            (fun (w : α) =>
               fun (hw : Q w) =>
                  Exists.intro w ((Or.inr : Q w → (P ∨ Q w)) hw)
            )
         )
   )






open Classical


theorem brackets_uni_disj (α : Type) (P : Prop) (Q : α → Prop) : (∀ x : α, P ∨ Q x) ↔ (P ∨ ∀ x : α, Q x) :=
   Iff.intro
   (
      fun (h : (∀ x : α, P ∨ Q x)) =>
         Or.elim (em P)
         (fun (g : P) => (Or.inl : (P → P ∨ ∀ x : α, Q x)) g)
         (fun (g : ¬P) => (Or.inr : (∀ x : α, Q x) → P ∨ ∀ x : α, Q x) (fun (s : α) =>
               Or.elim (h s)
               (fun (t : P) => (False.elim : False → Q s) (g t))
               (fun (t : Q s) => t)

               )
         )
   )
   (brackets_uni_disj_mpr α P Q)





theorem morgan_exi (α : Type) (P : α → Prop) : (∃ x : α, ¬ P x) ↔ (¬ ∀ x : α, P x) :=
   Iff.intro
   (morgan_exi_mp α P)
   (
      fun (h : (¬ ∀ x : α, P x)) =>
         byContradiction
         (
            fun (s : ¬ ∃ t : α, ¬ P t) =>
               h (
                  fun (x : α) =>
                     byContradiction
                        (fun (t : ¬ P x) =>
                           s (Exists.intro x t))
               )

         )
   )



theorem inh_brackets_left_exi_impl (α : Type) [Inhabited α] (P : Prop) (Q : α → Prop) : (P → ∃ x : α, Q x) ↔ (∃ x : α, (P → Q x)) :=
   Iff.intro
   (
      fun (h : (P → ∃ x : α, Q x)) =>
         Or.elim (em P)
         (fun (g : P) =>
            Exists.elim (h g)
            (
               fun (w : α) =>
                  fun (hw : Q w) =>
                     Exists.intro w (fun (_ : P) => hw)
            )
         )
         (
            fun (g : ¬P) =>
            Exists.intro Inhabited.default (fun (s : P) => (False.elim : False → Q (Inhabited.default : α)) (g s))
         )
   )
   (brackets_left_exi_impl_mpr α P Q)


theorem inh_brackets_right_uni_impl (α : Type) [Inhabited α] (P: α → Prop)  (Q : Prop) :  ((∀ x : α, P x) → Q) ↔ (∃ x : α, (P x → Q)) :=
   Iff.intro
   (
      fun (h : ((∀ x : α, P x) → Q)) =>
      Or.elim (em Q)
      (fun (t : Q) =>
         Exists.intro
            (Inhabited.default : α)
            (fun (_ : P (Inhabited.default : α)) =>
               t
            )

      )
      (fun (t : ¬Q) =>

        Exists.elim (Iff.mpr (morgan_exi α P) (fun (r : (∀ x : α, P x)) => t (h r)))
        (
         fun (w : α) =>
            fun (hw : ¬P w) =>
               Exists.intro w (fun (m : P w) => (False.elim : False → Q) (hw m))
        )
      )

   )
   (brackets_right_uni_impl_mpr α P Q)



-- In non empty pub there is someone in the pub such that, if he or she is drinking, then everyone in the pub is drinking
theorem drinker_paradox (pub_visitor : Type) (is_drinking : pub_visitor → Prop) [Inhabited pub_visitor]
 : (∃ someone : pub_visitor, (is_drinking someone  → ∀ person : pub_visitor, is_drinking person)) :=


   Iff.mp (inh_brackets_right_uni_impl pub_visitor is_drinking (∀ person : pub_visitor, is_drinking person))
   fun (h : (∀ x : pub_visitor, is_drinking x)) => h
