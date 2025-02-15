
-- 1) Reflexivity, symmetry, commutativity and transitivity of equality
theorem eq_refl (α : Type) : (∀ x : α, x = x) := sorry
theorem eq_symm (α : Type) : (∀ (x y : α), x = y → y = x) := sorry
theorem eq_commut (α : Type) : (∀ x : α, ∀ y : α, x = y ↔ y = x) := sorry
theorem eq_trans_curry (α : Type) : (∀ (x y z : α), x = y → y = z → x = z) := sorry
theorem eq_trans_export (α : Type) : (∀ (x y z : α), x = y ∧ y = z → x = z) := sorry


-- 2) Congruence of equality
theorem eq_subst (α : Type) (P : α → Prop) : (∀ (a b : α), a = b → P a → P b) := sorry
theorem eq_substr (α : Type) (P : α → Prop) : (∀ (a b : α), a = b → P b → P a) := sorry
theorem eq_congr_func_arg (α : Type) (β : Type) (f : α → β) : (∀ (x y : α), x = y → f x = f y) := sorry
theorem eq_congr_pred_arg (α : Type) (P : α → Prop) : (∀ (x y : α), x = y → (P x ↔ P y)) := sorry
theorem iff_congr_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x ↔ P y)) := sorry
theorem iff_subst_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x → P y)) := sorry
theorem eq_congr_func_symb (α : Type) (β : Type) (f g : α → β) (h : f = g) : (∀ x : α, f x = g x) := sorry
theorem eq_congr_pred_symb (α : Type) (P Q : α → Prop) (h : P = Q) : (∀ x : α, P x ↔ Q x) := sorry
theorem eq_congr_func_arg_symb (α : Type) (β : Type) (f₁ f₂ : α → β) : ∀ (a₁ a₂ : α), (f₁ = f₂) → (a₁ = a₂) → (f₁ a₁ = f₂ a₂) := sorry
theorem eq_congr_pred_arg_symb (α : Type) (P₁ P₂ : α → Prop) : ∀ (a₁ a₂ : α), (P₁ = P₂) → (a₁ = a₂) → (P₁ a₁ ↔ P₂ a₂) := sorry


-- 3) Retrieval of element of the same type
def eq_mp (α : Sort u₁) (β : Sort u₁) (h : α = β) (a : α) : β := sorry
def eq_mpr (α : Sort u₁) (β : Sort u₁) (h : α = β) (b : β) : α := sorry


-- 4) Equality of Prop
theorem iff_is_eq (p q : Prop) : (p ↔ q) ↔ (p = q) := sorry


-- 5) ≠ is a symbol, x ≠ y is parsed as ¬ (x = y)
-- prove trivial theorem for that
theorem neq_symbol (α : Type) : (∀ (x y : α), ¬ (x = y) ↔ x ≠ y) := sorry


-- 6) Equal to constant quantifier
theorem exists_eq_C_PC_then_P (α : Type) (P : α → Prop) (C : α) : (∃ x : α, x = C) → (P C) → (∃ x : α, P x) := sorry
theorem forall_eq_C_PC_then_P (α : Type) (P : α → Prop) (C : α) : (∀ x : α, x = C) → (P C) → (∀ x : α, P x) := sorry


-- 7) Paritition of quantifier by equality
theorem uni_eq_partition (α : Type) (P : α → α → Prop) :
 (∀ x : α, ∀ y : α, P x y) ↔ ((∀ x : α, P x x) ∧ ∀ x : α, ∀ y : α, (x ≠ y → P x y)) := sorry
theorem exi_eq_partition (α : Type) (P : α → α → Prop) :
 (∃ x : α, ∃ y : α, P x y) ↔ ((∃ x : α, P x x) ∨ ∃ x : α, ∃ y : α, (x ≠ y ∧ P x y)) := sorry


-- 8) Exists unique formula definition
def exists_unique {α : Type} (P : α → Prop) : Prop := (∃ (x : α), P x ∧ (∀ y : α, (P y → x = y)))
open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b


-- 9) Exists unique properties
theorem exists_unique_intro (α : Type) (P : α → Prop) (w : α) (h : P w) (g : ∀ y : α, P y → w = y) : ∃! (x : α), P x := sorry
theorem exists_unique_elim (α : Type) (q : Prop) (P : α → Prop) (h : ∃! (x : α), P x) (g : ∀ w : α, ∀ _ : P w, ((∀ y : α, P y → w = y) → q)) : q := sorry
theorem exists_unique_expansion_export (α : Type) (P : α → Prop) : (∃! (x : α), P x) ↔ (∃ (x : α), P x) ∧ (∀ (x y : α), (P x ∧ P y → x = y)) := sorry
theorem exists_unique_expansion_curry (α : Type) (P : α → Prop) :
   (∃! (x : α), P x) ↔ (∃ (x : α), P x) ∧ (∀ (x y : α), (P x → P y → x = y)) := sorry
theorem exists_unique_then_exists (α : Type) (P : α → Prop) (h : ∃! (x : α), P x) : (∃ (x : α), P x) := sorry
theorem exists_unique_then_unique (α : Type) (P : α → Prop)  (h : ∃! (x : α), P x) (x : α) (y : α) (h₁ : P x) (h₂ : P y) : x = y := sorry
theorem exists_unique_congr (α : Type) (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∃! (x : α), P x) ↔ (∃! (x : α), Q x)) := sorry
