import «Header»


def rel_reflexive (R A : Set) : Prop := ∀ x ∈ A; (x . R . x)
def rel_irreflexive (R : Set) : Prop := ∀ x, ¬ (x . R . x)
def rel_symmetric (R : Set) : Prop := ∀ x y, ((x . R . y) → (y . R . x))
def rel_antisymmetric (R : Set) : Prop := ∀ x y, ((x . R . y) ∧ (y . R . x) → (x = y))
def rel_asymmetric (R : Set) : Prop := ∀ x y, ((x . R . y) → ¬ (y . R . x))
def rel_transitive (R : Set) : Prop := ∀ x y z, (x . R . y) ∧ (y . R . z) → (x . R . z)
def rel_strongly_connected (R : Set) : Prop := ∀ x y, ((x . R . y) ∨ (y . R . x))
def rel_weakly_connected (R : Set) : Prop := ∀ x y, ((x ≠ y) → (x . R . y) ∨ (y . R . x))
def rel_trichotomic (R : Set) : Prop := ∀ x y,
 (((x . R . y) ∧ (¬ (y . R . x)) ∧ (x ≠ y)))
 ∨ ((¬ (x . R . y)) ∧ (y . R . x) ∧ (x ≠ y))
∨ ((¬ (x . R . y)) ∧ (¬ (y . R . x)) ∧ (x = y))


theorem reflex_crit : ∀ A R, binary_relation_on A R → ((rel_reflexive A R) ↔ ((id_ A) ⊆ R)) := sorry
theorem irreflex_crit : ∀ A R, binary_relation_on A R → ((rel_irreflexive R) ↔ (R ∩ (id_ A) = ∅)) := sorry
theorem symmetric_crit_sub_left : ∀ A R, binary_relation_on A R → ((rel_symmetric R) ↔ (R ⊆ R⁻¹)) := sorry
theorem symmetric_crit_sub_right : ∀ A R, binary_relation_on A R → ((rel_symmetric R) ↔ (R⁻¹ ⊆ R)) := sorry
theorem symmetric_crit_eq : ∀ A R, binary_relation_on A R → ((rel_symmetric R) ↔ (R = R⁻¹)) := sorry
theorem antisymmetric_crit : ∀ A R, binary_relation_on A R → ((rel_antisymmetric R) ↔ (R ∩ R⁻¹ ⊆ (id_ A))) := sorry
theorem asymmetric_crit : ∀ A R, binary_relation_on A R → ((rel_asymmetric R) ↔ (R ∩ R⁻¹ = ∅)) := sorry
theorem transitive_crit : ∀ A R, binary_relation_on A R → ((rel_transitive R) ↔ (R ∘ R ⊆ R)) := sorry
theorem strongly_connected_crit : ∀ A R, binary_relation_on A R → ((rel_strongly_connected R) ↔ (R ∪ R⁻¹ ≠ ∅)) := sorry
theorem weakly_connected_crit : ∀ A R, binary_relation_on A R → ((rel_weakly_connected R) ↔ (((A × A) \ (R ∪ R⁻¹)) ⊆ (id_ A))) := sorry
