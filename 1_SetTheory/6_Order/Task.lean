import «Header»

-- Now we again consider arbitrary binary relations between A and B
-- But let A = B
-- (We consider binary relations on one set A)

-- 1) properties of binary relations on one set
def rel_reflexive (A R : Set) : Prop := ∀ x ∈ A; (x . R . x)
def rel_irreflexive (R : Set) : Prop := ∀ x, ¬ (x . R . x)
def rel_symmetric (R : Set) : Prop := ∀ x y, ((x . R . y) → (y . R . x))
def rel_antisymmetric (R : Set) : Prop := ∀ x y, ((x . R . y) ∧ (y . R . x) → (x = y))
def rel_asymmetric (R : Set) : Prop := ∀ x y, ((x . R . y) → ¬ (y . R . x))
def rel_transitive (R : Set) : Prop := ∀ x y z, (x . R . y) ∧ (y . R . z) → (x . R . z)
def rel_strongly_connected (R A : Set) : Prop := ∀ x y ∈ A; ((x . R . y) ∨ (y . R . x))
def rel_weakly_connected (R A : Set) : Prop := ∀ x y ∈ A; ((x ≠ y) → (x . R . y) ∨ (y . R . x))



-- 2) Criteria of the properties of binary relations on one sets
theorem reflex_crit : ∀ A R, binary_relation_on A R → ((rel_reflexive A R) ↔ ((id_ A) ⊆ R)) := sorry
theorem irreflex_crit : ∀ A R, binary_relation_on A R → ((rel_irreflexive R) ↔ (R ∩ (id_ A) = ∅)) := sorry
theorem symmetric_crit_sub_left : ∀ A R, binary_relation_on A R → ((rel_symmetric R) ↔ (R ⊆ R⁻¹)) := sorry
theorem symmetric_crit_sub_right : ∀ A R, binary_relation_on A R → ((rel_symmetric R) ↔ (R⁻¹ ⊆ R)) := sorry
theorem symmetric_crit_eq : ∀ A R, binary_relation_on A R → ((rel_symmetric R) ↔ (R = R⁻¹)) := sorry
theorem antisymmetric_crit : ∀ A R, binary_relation_on A R → ((rel_antisymmetric R) ↔ (R ∩ R⁻¹ ⊆ (id_ A))) := sorry
theorem asymmetric_crit : ∀ A R, binary_relation_on A R → ((rel_asymmetric R) ↔ (R ∩ R⁻¹ = ∅)) := sorry
theorem transitive_crit : ∀ A R, binary_relation_on A R → ((rel_transitive R) ↔ (R ∘ R ⊆ R)) := sorry
theorem strongly_connected_crit : ∀ A R, binary_relation_on A R → ((rel_strongly_connected R A) ↔ ((A × A) ⊆ (R ∪ R⁻¹))) := sorry
theorem weakly_connected_crit : ∀ A R, binary_relation_on A R → ((rel_weakly_connected R A) ↔ (((A × A) \ (id_ A)) ⊆ (R ∪ R⁻¹))) := sorry



-- 3) Relations between properties






-- 4) Strict partial order definition
def is_strict_partial_order (R A : Set) := binary_relation_on A R ∧ rel_irreflexive R ∧ rel_transitive R
syntax term "SPO" term : term
macro_rules
| `($R:term SPO $A:term) => `(is_strict_partial_order $R $A)
def is_nonstrict_partial_order (R A : Set) := binary_relation_on A R ∧ rel_reflexive A R ∧ rel_antisymmetric R ∧ rel_transitive R
syntax term "NSPO" term : term
macro_rules
| `($R:term NSPO $A:term) => `(is_nonstrict_partial_order $R $A)
