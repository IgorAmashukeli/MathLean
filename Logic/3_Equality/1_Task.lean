
-- 1) Reflexivity, symmetry, commutativity and transitivity of equality
theorem eq_refl : (∀ x : α, x = x) := sorry
theorem eq_symm : (∀ (x y : α), x = y → y = x) := sorry
theorem eq_commut : (∀ x : α, ∀ y : α, x = y ↔ y = x) := sorry
theorem eq_trans_curry : (∀ (x y z : α), x = y → y = z → x = z) := sorry
theorem eq_trans_export : (∀ (x y z : α), x = y ∧ y = z → x = z) := sorry


-- 2) Congruence of equality
theorem eq_subst (P : α → Prop) : (∀ (a b : α), a = b → P a → P b) := sorry
theorem eq_substr (P : α → Prop) : (∀ (a b : α), a = b → P b → P a) := sorry
theorem eq_congr_func_arg (f : α → β) : (∀ (x y : α), x = y → f x = f y) := sorry
theorem eq_congr_pred_arg (P : α → Prop) : (∀ (x y : α), x = y → (P x ↔ P y)) := sorry
theorem iff_congr_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x ↔ P y)) := sorry
theorem iff_subst_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x → P y)) := sorry
theorem eq_congr_func_symb (f g : α → β) (h : f = g) : (∀ x : α, f x = g x) := sorry
theorem eq_congr_pred_symb (P Q : α → Prop) (h : P = Q) : (∀ x : α, P x ↔ Q x) := sorry
theorem eq_congr_func_arg_symb (f₁ f₂ : α → β) : ∀ (a₁ a₂ : α), (f₁ = f₂) → (a₁ = a₂) → (f₁ a₁ = f₂ a₂) := sorry
theorem eq_congr_pred_arg_symb (P₁ P₂ : α → Prop) : ∀ (a₁ a₂ : α), (P₁ = P₂) → (a₁ = a₂) → (P₁ a₁ ↔ P₂ a₂) := sorry


-- 3) Retrieval of element of the same type
def eq_mp (α : Sort u₁) (β : Sort u₁) (h : α = β) (a : α) : β := sorry
def eq_mpr (α : Sort u₁) (β : Sort u₁) (h : α = β) (b : β) : α := sorry


-- 4) Equality of Prop
theorem iff_is_eq (p q : Prop) : (p ↔ q) ↔ (p = q) := sorry


-- 5) ≠ is a symbol, x ≠ y is parsed as ¬ (x = y)
-- prove trivial theorem for that
theorem neq_symbol : (∀ (x y : α), ¬ (x = y) ↔ x ≠ y) := sorry


-- 6) Equal to constant quantifier
theorem exists_eq_C_PC_then_P (P : α → Prop) : (∃ x : α, x = C) → (P C) → (∃ x : α, P x) := sorry
theorem forall_eq_C_PC_then_P (P : α → Prop) : (∀ x : α, x = C) → (P C) → (∀ x : α, P x) := sorry


-- 7) Paritition of quantifier by equality
theorem uni_eq_partition (P : α → α → Prop) :
 (∀ x : α, ∀ y : α, P x y) ↔ ((∀ x : α, P x x) ∧ ∀ x : α, ∀ y : α, (x ≠ y → P x y)) := sorry
theorem exi_eq_partition (P : α → α → Prop) :
 (∃ x : α, ∃ y : α, P x y) ↔ ((∃ x : α, P x x) ∨ ∃ x : α, ∃ y : α, (x ≠ y ∧ P x y)) := sorry


-- 8) Exists unique formula definition
def exists_unique (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b


-- 9) Exists unique properties
theorem exists_unique_intro (P : α → Prop) (w : α) (h : P w) (g : ∀ y : α, P y → w = y) : ∃! (x : α), P x := sorry
theorem exists_unique_elim (q : Prop) (P : α → Prop) (h : ∃! (x : α), P x) (g : ∀ w : α, ∀ _ : P w, ((∀ y : α, P y → w = y) → q)) : q := sorry
theorem exists_unique_expansion_export (P : α → Prop) : (∃! (x : α), P x) ↔ (∃ (x : α), P x) ∧ (∀ (x y : α), (P x ∧ P y → x = y)) := sorry
theorem exists_unique_expansion_curry (P : α → Prop) :
   (∃! (x : α), P x) ↔ (∃ (x : α), P x) ∧ (∀ (x y : α), (P x → P y → x = y)) := sorry
theorem exists_unique_then_exists (P : α → Prop) (h : ∃! (x : α), P x) : (∃ (x : α), P x) := sorry
theorem exists_unique_then_unique (P : α → Prop)  (h : ∃! (x : α), P x) (x : α) (y : α) (h₁ : P x) (h₂ : P y) : x = y := sorry
theorem exists_unique_congr (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∃! (x : α), P x) ↔ (∃! (x : α), Q x)) := sorry
