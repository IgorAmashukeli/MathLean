import «Header»

-- Now we again consider arbitrary binary relations between A and B
-- But let A = B
-- (We consider binary relations on one set A)

-- 1) properties of binary relations on one set
def refl (R A : Set) : Prop := ∀ x ∈ A; (x . R . x)
def irrefl (R : Set) : Prop := ∀ x, ¬ (x . R . x)
def symm (R : Set) : Prop := ∀ x y, ((x . R . y) → (y . R . x))
def antisymm (R : Set) : Prop := ∀ x y, ((x . R . y) ∧ (y . R . x) → (x = y))
def asymm (R : Set) : Prop := ∀ x y, ((x . R . y) → ¬ (y . R . x))
def transit(R : Set) : Prop := ∀ x y z, (x . R . y) ∧ (y . R . z) → (x . R . z)
def str_conn (R A : Set) : Prop := ∀ x y ∈ A; ((x . R . y) ∨ (y . R . x))
def wkl_conn (R A : Set) : Prop := ∀ x y ∈ A; ((x ≠ y) → (x . R . y) ∨ (y . R . x))


-- 2) Criteria of the properties of binary relations on one sets
theorem refl_crit : ∀ A R, (R BinOn A) → ((refl R A) ↔ ((id_ A) ⊆ R)) := sorry
theorem irrefl_crit : ∀ A R, (R BinOn A) → ((irrefl R) ↔ (R ∩ (id_ A) = ∅)) := sorry
theorem symmetric_crit_sub_left : ∀ A R, (R BinOn A) → ((symm R) ↔ (R ⊆ R⁻¹)) := sorry
theorem symmetric_crit_sub_right : ∀ A R, (R BinOn A) → ((symm R) ↔ (R⁻¹ ⊆ R)) := sorry
theorem symmetric_crit_eq : ∀ A R, (R BinOn A) → ((symm R) ↔ (R = R⁻¹)) := sorry
theorem antisymmetric_crit : ∀ A R, (R BinOn A) → ((antisymm R) ↔ (R ∩ R⁻¹ ⊆ (id_ A))) := sorry
theorem asymmetric_crit : ∀ A R, (R BinOn A) → ((asymm R) ↔ (R ∩ R⁻¹ = ∅)) := sorry
theorem transitive_crit : ∀ A R, (R BinOn A) → ((transitR) ↔ (R ∘ R ⊆ R)) := sorry
theorem strongly_connected_crit : ∀ A R, (R BinOn A) → ((str_conn R A) ↔ ((A × A) ⊆ (R ∪ R⁻¹))) := sorry
theorem weakly_connected_crit : ∀ A R, (R BinOn A) → ((wkl_conn R A) ↔ (((A × A) \ (id_ A)) ⊆ (R ∪ R⁻¹))) := sorry


-- 3) Relations between properties
theorem assym_iff_antisymm_irrefl : ∀ A R, (R BinOn A) → ((asymm R) ↔ (antisymm R ∧ irrefl R)) := sorry
theorem strcon_iff_wkcon_refl : ∀ A R, (R BinOn A) → ((str_conn R A) ↔ (wkl_conn R A ∧ refl A R)) := sorry
theorem emp_refl_irrefl : ∀ A R, (R BinOn A) → ((A = ∅) ↔ (refl R A ∧ irrefl R)) := sorry
theorem emp_symm_asymm : ∀ A R, (R BinOn A) → ((R = ∅) ↔ (symm R ∧ asymm R)) := sorry
theorem trans_irrefl_antisymm : ∀ A R, (R BinOn A) → (transit R) → (irrefl R) → (antisymm R) := sorry
theorem trans_irrefl_ansymm : ∀ A R, (R BinOn A) → (transit R) → (irrefl R) → (asymm R) := sorry
theorem refl_symm_antisymm : ∀ A R, (R BinOn A) → (((refl R A) ∧ (symm R) ∧ (antisymm R)) ↔ (R = (id_ A))) := sorry


-- 4) Inverse relation to the properties
theorem refl_inv : ∀ A R, (R BinOn A) → ((refl R A) ↔ (refl (R⁻¹) A)) := sorry
theorem irrefl_inv : ∀ A R, (R BinOn A) → ((irrefl R) ↔ (irrefl (R⁻¹))) := sorry
theorem symm_inv : ∀ A R, (R BinOn A) → ((symm R) ↔ (symm (R⁻¹))) := sorry
theorem antisymm_inv : ∀ A R, (R BinOn A) → ((antisymm R) ↔ (antisymm (R⁻¹))) := sorry
theorem asymm_inv : ∀ A R, (R BinOn A) → ((asymm R) ↔ (asymm (R⁻¹))) := sorry





-- 5) Strict partial order definition
def is_strict_partial_order (R A : Set) := (R BinOn A) ∧ irrefl R ∧ transit R
syntax term "SPO" term : term
macro_rules
| `($R:term SPO $A:term) => `(is_strict_partial_order $R $A)
def is_nonstrict_partial_order (R A : Set) := (R BinOn A) ∧ refl R A ∧ antisymm R ∧ transit R
syntax term "NSPO" term : term
macro_rules
| `($R:term NSPO $A:term) => `(is_nonstrict_partial_order $R $A)
