-- 1) Universal quantifier rules
theorem universal_intro (α : Type) (P : α → Prop) (proof_stub : ∀ x : α, P x) : ∀ x : α, P x :=
   fun (x : α) => proof_stub x
   -- In real examples, proof_stub variable must be removed from context,
   -- and some real proof after fun should be written
theorem universal_elim (α : Type) (P : α → Prop) (h : ∀ x, P x) (t : α) : P t :=
   h t


-- 2) Existential quantifier rules
theorem existential_intro (α : Type) (P : α → Prop) (x₀ : α) (hx₀ : P x₀) : ∃ x : α, P x :=
   Exists.intro x₀ hx₀
theorem existential_elim (α : Type) (P : α → Prop) (q : Prop) (h : ∃ x : α, P x) (hxq : ∀ x : α, P x → q) : q :=
   Exists.elim h hxq


-- 3) Inhabited type property
theorem inh_property (α : Type) [Inhabited α] : α := Inhabited.default
