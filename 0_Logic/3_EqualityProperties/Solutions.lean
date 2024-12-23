axiom syllogism (p q r : Prop) : (p → q) -> (q → r) → (p → r)
axiom iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r)
axiom iff_reflexivity (p : Prop) : (p ↔ p)


theorem eq_refl : (∀ x : α, x = x) :=
   Eq.refl

theorem eq_subst (P : α → Prop) : (∀ (a b : α), a = b → P a → P b) :=
   fun (_ : α) => fun (_ : α) => Eq.subst

theorem eq_symm : (∀ (x y : α), x = y → y = x) :=
   fun (x: α) => fun (y : α) => fun (h : x = y) =>
      eq_subst (fun (t : α) => t = x) x y h (eq_refl x)

theorem eq_substr (P : α → Prop) : (∀ (a b : α), a = b → P b → P a) :=
   fun (a : α) => fun (b : α) => fun (h : a = b) => eq_subst P b a (eq_symm a b h)


def eq_mp (α : Sort u₁) (β : Sort u₁) (h : α = β) (a : α) : β :=
   Eq.mp h a

def eq_mpr (α : Sort u₁) (β : Sort u₁) (h : α = β) (b : β) : α :=
   eq_mp β α (eq_symm α β h) b


theorem eq_trans_curry : (∀ (x y z : α), x = y → y = z → x = z) :=
   fun (x : α) => fun (y : α ) => fun (z : α) => fun (xy : x = y) =>
      eq_subst (fun (t : α) => t = z) y x (eq_symm x y xy)

theorem eq_trans_export : (∀ (x y z : α), x = y ∧ y = z → x = z) :=
   fun (x : α) => fun (y : α ) => fun (z : α) => fun (r : (x = y ∧ y = z)) =>
      eq_trans_curry x y z (And.left r) (And.right r)

theorem eq_congr_func_arg (f : α → β) : (∀ (x y : α), x = y → f x = f y) :=
   fun (x : α) => fun (y : α) => fun (xy : x = y) =>
      eq_subst (fun (t : α) => f x = f t) x y (xy) (eq_refl (f x))


theorem iff_is_eq (p q : Prop) : (p ↔ q) ↔ (p = q) :=
   Iff.intro
   (
      fun (h : p ↔ q) =>
          Eq.propIntro (Iff.mp h) (Iff.mpr h)
   )
   (fun (h : p = q) =>
      eq_subst (fun (t : Prop) => p ↔ t) p q h (iff_reflexivity p)
   )

theorem eq_congr_pred_arg (P : α → Prop) : (∀ (x y : α), x = y → (P x ↔ P y)) :=
   fun (x : α) => fun (y : α) => (syllogism (x = y) (P x = P y) (P x ↔ P y) (eq_congr_func_arg P x y) (Iff.mpr (iff_is_eq (P x) (P y))))

theorem iff_congr_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x ↔ P y)) :=
   fun (x : Prop) => fun (y : Prop) => fun (s : x ↔ y) => eq_congr_pred_arg P x y (Iff.mp (iff_is_eq x y) s)

theorem iff_subst_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x → P y)) :=
   fun (x : Prop) => fun (y : Prop) => fun (s : x ↔ y) => Iff.mp (eq_congr_pred_arg P x y (Iff.mp (iff_is_eq x y) s))


theorem eq_congr_func_symb (f g : α → β) (h : f = g) : (∀ x : α, f x = g x) :=
   fun (x : α) => eq_subst (fun (t : α → β) => f x = t x) f g h (eq_refl (f x))

theorem eq_congr_pred_symb (P Q : α → Prop) (h : P = Q) : (∀ x : α, P x ↔ Q x) :=
   fun (x : α) => (Iff.mpr (iff_is_eq (P x) (Q x))) (eq_subst (fun (t : α → Prop) => P x = t x) P Q h (eq_refl (P x)))


theorem eq_commut : (∀ x : α, ∀ y : α, x = y ↔ y = x) :=
   fun (x : α) => fun (y : α) => (Iff.intro (eq_symm x y) (eq_symm y x))





theorem eq_congr_func_arg_symb (f₁ f₂ : α → β) : ∀ (a₁ a₂ : α), (f₁ = f₂) → (a₁ = a₂) → (f₁ a₁ = f₂ a₂) :=
   fun (a₁ : α) => fun (a₂ : α) => fun (h : f₁ = f₂) => fun (g : a₁ = a₂) =>
      eq_trans_curry
      (f₁ a₁)
      (f₁ a₂)
      (f₂ a₂)
      (eq_congr_func_arg f₁ a₁ a₂ g)
      (eq_congr_func_symb f₁ f₂ h a₂)


theorem eq_congr_pred_arg_symb (P₁ P₂ : α → Prop) : ∀ (a₁ a₂ : α), (P₁ = P₂) → (a₁ = a₂) → (P₁ a₁ ↔ P₂ a₂) :=
   fun (a₁ : α) => fun (a₂ : α) => fun (h : P₁ = P₂) => fun (g : a₁ = a₂) =>
      iff_transitivity
      (P₁ a₁)
      (P₁ a₂)
      (P₂ a₂)
      (eq_congr_pred_arg P₁ a₁ a₂ g)
      (eq_congr_pred_symb P₁ P₂ h a₂)


-- ≠ is a symbol, x ≠ y is parsed as ¬ (x = y)
-- prove trivial theorem for that
theorem neq_symbol : (∀ (x y : α), ¬ (x = y) ↔ x ≠ y) :=
   fun (x : α) => fun (y : α) =>
      Iff.intro
      (fun (h : ¬ (x = y)) => h)
      (fun (h : x ≠ y) => h)



theorem exists_eq_C_PC_then_P (P : α → Prop) : (∃ x : α, x = C) → (P C) → (∃ x : α, P x) :=
   fun (h : (∃ x : α, x = C)) => fun (g : P C) =>
      Exists.elim h
      (fun (w : α) =>
         fun (hw : w = C) =>
            Exists.intro w (eq_subst P C w (eq_symm w C hw) g)
      )


theorem forall_eq_C_PC_then_P (P : α → Prop) : (∀ x : α, x = C) → (P C) → (∀ x : α, P x) :=
   fun (h : (∀ x : α, x = C)) => fun (g : P C) =>
      fun (s : α) => eq_subst P C s ((eq_symm s C) (h s)) g





theorem uni_eq_partition (P : α → α → Prop) : (∀ x : α, ∀ y : α, P x y) ↔ ((∀ x : α, P x x) ∧ ∀ x : α, ∀ y : α, (x ≠ y → P x y)) :=
   Iff.intro
   (
      fun (h : ((∀ x : α, ∀ y : α, P x y))) =>
         And.intro (fun (x : α) => h x x) (fun (x : α) => fun (y : α) => fun (_ : x ≠ y) => h x y)
   )
   (
      fun (h : ((∀ x : α, P x x) ∧ ∀ x : α, ∀ y : α, (x ≠ y → P x y))) =>
         fun (x : α) => fun (y : α) =>
            Or.elim (Classical.em (x = y))
            (fun (g : x = y) =>
               eq_subst (fun (t : α) => P x t) x y g (And.left h x)
            )
            (fun (g : x ≠ y) =>
               And.right h x y g
            )
   )



theorem exi_eq_partition (P : α → α → Prop) : (∃ x : α, ∃ y : α, P x y) ↔ ((∃ x : α, P x x) ∨ ∃ x : α, ∃ y : α, (x ≠ y ∧ P x y)) :=
   Iff.intro
   (
      fun (h : (∃ x : α, ∃ y : α, P x y)) =>
         Exists.elim h
         (
            fun (w : α) =>
               fun (hw : ∃ y : α, P w y) =>
                  Exists.elim hw
                  (
                     fun (u : α) =>
                        fun (hu : P w u) =>
                           Or.elim (Classical.em (w = u))
                              (fun (g : (w = u)) =>
                                 (Or.inl : (∃ x : α, P x x) → (∃ x : α, P x x) ∨ ∃ x : α, ∃ y : α, (x ≠ y ∧  P x y))
                                 (Exists.intro u (eq_subst (fun (t : α) => P t u) w u g hu))
                              )
                              (fun (g : (w ≠ u)) =>
                                 (Or.inr : (∃ x : α, ∃ y : α, (x ≠ y ∧  P x y)) → (∃ x : α, P x x) ∨ ∃ x : α, ∃ y : α, (x ≠ y ∧  P x y))
                                 (Exists.intro w  ( Exists.intro u (And.intro g hu)))
                              )
                  )
         )
   )
   (
      fun (h : ((∃ x : α, P x x) ∨ ∃ x : α, ∃ y : α, (x ≠ y ∧ P x y))) =>
         Or.elim h
         (fun (g : (∃ x : α, P x x)) =>
            Exists.elim g
            (
               fun (w : α) =>
                  fun (hw : P w w) =>
                     Exists.intro w (Exists.intro w hw)
            )
         )
         (fun (g : ∃ x : α, ∃ y : α, (x ≠ y ∧ P x y)) =>
            Exists.elim g
            (
               fun (w : α) =>
                  fun (hw : ∃ y : α, (w ≠ y) ∧ P w y) =>
                     Exists.elim hw
                        (
                           fun (u : α) =>
                              fun (hu : (w ≠ u) ∧ P w u) =>
                                 Exists.intro w (Exists.intro u (And.right hu))
                        )
            )
         )
   )



def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))


open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b


@[app_unexpander exists_unique] def unexpandexists_unique: Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident ↦ ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()



theorem exists_unique_intro (P : α → Prop) (w : α) (h : P w) (g : ∀ y : α, P y → w = y) : ∃! (x : α), P x :=
   Exists.intro w (And.intro h g)




theorem exists_unique_elim (q : Prop) (P : α → Prop) (h : ∃! (x : α), P x) (g : ∀ w : α, ∀ _ : P w, ((∀ y : α, P y → w = y) → q)) : q :=
   Exists.elim h
   (
      fun (w : α) =>
         fun (hw : P w ∧ (∀ y : α, (P y → w = y))) =>
            g w (And.left hw) (And.right hw)
   )



theorem exists_unique_expansion_export (P : α → Prop) : (∃! (x : α), P x) ↔ (∃ (x : α), P x) ∧ (∀ (x y : α), (P x ∧ P y → x = y)) :=
   Iff.intro
   (
      fun (h : (∃! (x : α), P x)) =>
         Exists.elim h
         (
            fun (w : α) =>
               fun (hw : P w ∧ (∀ y : α, (P y → w = y))) =>
                  And.intro (Exists.intro w (And.left hw))
                   (
                     fun (x : α) => fun (y : α) =>
                        fun (t : P x ∧ P y) =>
                           eq_trans_curry x w y
                           (eq_symm w x (And.right hw x (And.left t)))
                           (And.right hw y (And.right t))
                  )
         )
   )
   (
      fun (h : (∃ (x : α), P x) ∧ (∀ (x y : α), (P x ∧ P y → x = y))) =>
         Exists.elim (And.left h)
         (
            fun (w : α) =>
               fun (hw : P w) =>
                  Exists.intro w
                  (And.intro (hw) (fun (y : α) =>
                     fun (g : P y) =>
                        And.right h w y (And.intro hw g)
                  ))
         )

   )


theorem exists_unique_expansion_curry (P : α → Prop) :
   (∃! (x : α), P x) ↔ (∃ (x : α), P x) ∧ (∀ (x y : α), (P x → P y → x = y)) :=
   Iff.intro
   (
      fun (h : (∃! (x : α), P x)) =>
      And.intro
      (And.left ((Iff.mp (exists_unique_expansion_export P)) h))
      (fun (x : α) => fun (y : α) => fun (g : P x) => fun (t : P y) => And.right ((Iff.mp (exists_unique_expansion_export P)) h) x y (And.intro g t))
   )
   (
      fun (h : (∃ (x : α), P x) ∧ (∀ (x y : α), (P x → P y → x = y))) =>
         Iff.mpr (exists_unique_expansion_export P)
         (And.intro (And.left h) (fun (x : α) => fun (y : α) => fun (g : P x ∧ P y) => And.right h x y (And.left g) (And.right g)))

   )




theorem exists_unique_then_exists (P : α → Prop) (h : ∃! (x : α), P x) : (∃ (x : α), P x) :=
   And.left ((Iff.mp (exists_unique_expansion_curry P)) h)


theorem exists_unique_then_unique (P : α → Prop)  (h : ∃! (x : α), P x) (x : α) (y : α) (h₁ : P x) (h₂ : P y) : x = y :=
   And.right ((Iff.mp (exists_unique_expansion_curry P)) h) x y h₁ h₂




theorem exists_unique_congr (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∃! (x : α), P x) ↔ (∃! (x : α), Q x)) :=
   fun (h : (∀ x : α, (P x ↔ Q x))) =>
      Iff.intro
      (
         fun (g : ∃! (x : α), P x) =>
            exists_unique_elim (∃! (x : α), Q x) P g
            (
               fun (w : α) =>
                  fun (hw : P w) =>
                     fun (hwy : ∀ y : α, P y → w = y) =>
                        exists_unique_intro Q w (Iff.mp (h w) hw)
                        (fun (y : α) => fun (h₁ : Q y) =>
                           hwy y (Iff.mpr (h y) h₁)
                        )
            )
      )
      (
         fun (g : ∃! (x : α), Q x) =>
            exists_unique_elim (∃! (x : α), P x) Q g
            (
               fun (w : α) =>
                  fun (hw : Q w) =>
                     fun (hwy : ∀ y : α, Q y → w = y) =>
                        exists_unique_intro P w (Iff.mpr (h w) hw) (fun (y : α) => fun (h₁ : P y) =>
                           hwy y (Iff.mp (h y) h₁)
                        )
            )
      )
