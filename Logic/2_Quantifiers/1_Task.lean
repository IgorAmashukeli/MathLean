-- 1) True is true for every element
theorem uni (α : Type) : ∀ _ : α, True := sorry

-- 2) Fictitious quantifier
theorem exi_uni_then_uni (α : Type) (P : α → Prop) : (∃ _ : α, ∀ x : α, P x) → (∀ x : α, P x) := sorry
theorem exi_exi_then_exi (α : Type) (P : α → Prop) : (∃ _ : α, ∃ x : α, P x) → (∃ x : α, P x) := sorry
theorem uni_uni_then_uni (α : Type) (P : α → Prop) : (∀ _ : α, ∀ x : α, P x) → (∀ x : α, P x) := sorry


-- 3) Variable changing
theorem change_variable_uni (α : Type) (P: α → Prop) : (∀ x : α, P x) ↔ (∀ y : α, P y) := sorry
theorem change_variable_exi (α : Type) (P: α → Prop) : (∃ x : α, P x) ↔ (∃ y : α, P y) := sorry


-- 4) Quantifier congruence
theorem uni_congr (α : Type) (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∀ x : α, P x) ↔ (∀ x : α, Q x)) := sorry
theorem exi_congr (α : Type) (P Q : α → Prop) : (∀ x : α, (P x ↔ Q x)) → ((∃ x : α, P x) ↔ (∃ x: α, Q x)) := sorry


-- 5) Quantifier commutativity
theorem uni_comm (α : Type) (P : α →  β → Prop) : (∀ x : α, ∀ y : β, P x y) ↔ (∀ y : β, ∀ x : α, P x y) := sorry
theorem exi_comm (α : Type) (P : α → β → Prop) : (∃ x : α, ∃ y : β, P x y) ↔ (∃ y : β, ∃ x : α, P x y) := sorry


-- 6) Quantifier order change
theorem exi_uni_then_uni_exi (α : Type) (P : α → β → Prop) : (∃ x : α, ∀ y : β, P x y) → (∀ y : β, ∃ x : α, P x y) := sorry


-- 7) Quantifier distributivity
theorem uni_conj (α : Type) (P Q: α → Prop) : (∀ x: α, P x ∧ Q x) ↔ (∀ x : α, P x) ∧ (∀ x : α, Q x) := sorry
theorem exi_disj (α : Type) (P Q : α → Prop) : (∃ x : α, P x ∨ Q x) ↔ (∃ x : α, P x) ∨ (∃ x: α, Q x) := sorry


-- 8) De morgan intutionists quantifier laws
theorem morgan_uni (α : Type) (P : α → Prop) : (∀ x : α, ¬ P x) ↔ (¬ ∃ x : α, P x) := sorry
theorem morgan_exi_mp (α : Type) (P : α → Prop) : (∃ x : α, ¬ P x) →  (¬ ∀ x : α, P x) := sorry


-- 9) Quantifiers intutionists and constant predicates
theorem brackets_exi_conj (α : Type) (P : Prop) (Q : α → Prop) : (∃ x : α, P ∧ Q x) ↔ (P ∧ ∃ x : α, Q x) := sorry
theorem brackets_uni_conj_mpr (α : Type) (P : Prop) (Q : α → Prop) : (P ∧ ∀ x : α, Q x) → (∀ x : α, P ∧ Q x) := sorry
theorem brackets_exi_disj_mp (α : Type) (P : Prop) (Q : α → Prop) : (∃ x : α, P ∨ Q x) → (P ∨ ∃ x : α, Q x) := sorry
theorem brackets_uni_disj_mpr (α : Type) (P : Prop) (Q : α → Prop) : (P ∨ ∀ x : α, Q x) → (∀ x : α, P ∨ Q x) := sorry
theorem brackets_left_uni_impl (α : Type) (P : Prop) (Q : α → Prop) : (P → ∀ x : α, Q x) ↔ (∀ x : α, (P → Q x)) := sorry
theorem brackets_left_exi_impl_mpr (α : Type) (P : Prop) (Q : α → Prop) : (∃ x : α, (P → Q x)) → (P → ∃ x : α, Q x) := sorry
theorem brackets_right_uni_impl_mpr (α : Type) (P : α → Prop) (Q : Prop) : (∃ x : α, (P x → Q)) → ((∀ x : α, P x) → Q) := sorry
theorem brackets_right_exi_impl (α : Type) (P : α → Prop) (Q : Prop) : ((∃ x : α, P x) → Q) ↔ (∀ x : α, (P x → Q)) := sorry

-- 10) Existence because of Inhabitance
theorem inh_exi (α : Type) [Inhabited α] : ∃ _ : α, True := sorry

-- 11) Inhabited fictitious quantifier
theorem inh_uni_exi_then_exi (α : Type) [Inhabited α] (P : α → Prop) : (∀ _ : α, ∃ x : α, P x) → (∃ x : α, P x) := sorry

-- 12) Inhabited quantifier change
theorem inh_uni_then_exi (α : Type) [Inhabited α] (P : α → Prop) : (∀ x : α, P x) → (∃ x : α, P x) := sorry

-- 13) Inhabited intutionists quantifiers and constant predicates
theorem inh_brackets_uni_conj (α : Type) [Inhabited α] (P : Prop) (Q : α → Prop) : (∀ x : α, P ∧ Q x) ↔ (P ∧ ∀ x : α, Q x) := sorry
theorem inh_brackets_exi_disj (α : Type) [Inhabited α] (P : Prop) (Q : α → Prop) : (∃ x : α, P ∨ Q x) ↔ (P ∨ ∃ x : α, Q x) := sorry


-- 14) Classical quantifiers and constant predicates
theorem brackets_uni_disj (α : Type) (P : Prop) (Q : α → Prop) : (∀ x : α, P ∨ Q x) ↔ (P ∨ ∀ x : α, Q x) := sorry


-- 15) Classical de morgan law
theorem morgan_exi (α : Type) (P : α → Prop) : (∃ x : α, ¬ P x) ↔ (¬ ∀ x : α, P x) := sorry


-- 16) Classical inhabited quantifiers and constant predicates
theorem inh_brackets_left_exi_impl (α : Type) [Inhabited α] (P : Prop) (Q : α → Prop) : (P → ∃ x : α, Q x) ↔ (∃ x : α, (P → Q x)) := sorry
theorem inh_brackets_right_uni_impl (α : Type) [Inhabited α] (P: α → Prop)  (Q : Prop) :  ((∀ x : α, P x) → Q) ↔ (∃ x : α, (P x → Q)) := sorry


-- 17) In non empty pub there is someone in the pub such that, if he or she is drinking, then everyone in the pub is drinking
theorem drinker_paradox (pub_visitor : Type) (is_drinking : pub_visitor → Prop) [Inhabited pub_visitor] :
 (∃ someone : pub_visitor, (is_drinking someone  → ∀ person : pub_visitor, is_drinking person)) := sorry
