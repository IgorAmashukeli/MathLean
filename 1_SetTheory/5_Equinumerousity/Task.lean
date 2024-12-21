import «Header»


-- 1) Equinumerousity and its main properties
def equinumerous (A B : Set) : Prop := ∃ f, f Bij A To B
syntax term "~" term : term
syntax term "≁" term : term
macro_rules
  | `($A:term ~ $B:term) => `(equinumerous $A $B)
  | `($A:term ≁ $B:term) => `(¬($A ~ $B))
theorem equinum_refl : ∀ A, A ~ A := sorry
theorem equinum_symm : ∀ A B, (A ~ B) → B ~ A := sorry
theorem equinum_trans : ∀ A B C, (A ~ B) → (B ~ C) → (A ~ C) := sorry


-- 2) Image and partition equinumerousity properties
theorem equinum_image_f : ∀ A B X f, X ⊆ A → (f Inj A To B) → (f ⨡ X) Bij X To (f.[X]) := sorry
theorem equinum_image : ∀ A B X f, X ⊆ A → (f Inj A To B) → X ~ f.[X] := sorry
theorem equinum_partition : ∀ A B X Y, (X ⊆ A) → (Y ⊆ B) → (X ~ Y) → ((A \ X) ~ (B \ Y)) → (A ~ B) := sorry



-- 3) Cartesian and power equinumerousity properties
theorem equinum_cartesian_singl : ∀ A a, A ~ (A × {a}) := sorry
theorem equinum_cartesian_comm : ∀ A B, (A × B) ~ (B × A) := sorry
theorem equinum_cartesian_assoc : ∀ A B C, ((A × B) × C) ~ (A × (B × C)) := sorry
theorem equinum_cartesian_congr_right : ∀ A B C, (A ~ B) → (A × C) ~ (B × C) := sorry
theorem equinum_cartesian_congr_left : ∀ A B C, (A ~ B) → (C × A) ~ (C × B) := sorry
theorem equinum_power_congr_right : ∀ A B C, (A ~ B) → (A ℙow C) ~ (B ℙow C) := sorry
theorem equinum_power_congr_left : ∀ A B C, (A ~ B) → (C ℙow A) ~ (C ℙow B) := sorry
theorem equinum_cartesian_power : ∀ A B C, ((A × B) ℙow C) ~ (A ℙow C) × (B ℙow C) := sorry
theorem equinum_power_cartesian : ∀ A B C, ((A ℙow B) ℙow C) ~ (A ℙow (B × C)) := sorry
theorem equium_2cart_cart : ∀ A B, (A × B) ~ (∏[ i in I2 ] (ind2_fun A B) at i) := sorry


-- 4) Equinumerousity of disjoint unions:

theorem equinum_dul : ∀ A B, A ~ (DUL (A ⊔ B)) := sorry
theorem equinum_dur : ∀ A B, B ~ (DUR (A ⊔ B)) := sorry
theorem equinum_du : ∀ A I i, (A IndxFun I) → (i ∈ I) → (A _ i) ~ (DU A) _ i := sorry
theorem equin_dsu2u : ∀ A B, (A ∩ B) = ∅ → (A ⊔ B) ~ (A ∪ B) := sorry
theorem equinum_disjun_un : ∀ A I, (A IndxFun I) → (∀ i j ∈ I; (i ≠ j) → (A _ i) ∩ (A _ j) = ∅) → (⋃[i in I] A at i) ~ (⨆[i in I] A at i) := sorry


-- 5) Boolean congr. equinumerousity property
theorem equinum_boolean_congr : ∀ A B, (A ~ B) → (𝒫 A ~ 𝒫 B) := sorry


-- 6) Equinumerousity of boolean and power sets
theorem equinum_power_boolean : ∀ A, (I2 ℙow A) ~ 𝒫 A := sorry


-- 7) Include definition and properties
def includes (A B : Set) := ∃ f, f Inj A To B
syntax term "≾" term : term
syntax term "⋨" term : term
syntax term "⋠" term : term
macro_rules
  | `($A:term ≾ $B:term) => `(includes $A $B)
  | `($A:term ⋠ $B:term) => `(¬($A ≾ $B))
  | `($A:term ⋨ $B:term) => `(($A ≾ $B) ∧ ($A ≁ $B))
theorem incl_refl : ∀ A, A ≾ A := sorry
theorem incl_trans : ∀ A B, (A ≾ B) → (B ≾ C) → (A ≾ C) := sorry
theorem equinum_then_incl : ∀ A B, (A ~ B) → A ≾ B := sorry
theorem subs_then_incl : ∀ A B, (A ⊆ B) → (A ≾ B) := sorry
theorem incl_iff_subs_equinum : ∀ A B, (A ≾ B) ↔ ∃ C, (C ⊆ B) ∧ A ~ C := sorry


-- 8) Cover definition and properties
def covers (A B : Set) := ∃ f, f Surj A To B
syntax term "≿" term : term
syntax term "⋩" term : term
syntax term "⋡" term : term
macro_rules
| `($A:term ≿ $B:term) => `(covers $A $B)
| `($A:term ⋩ $B:term) => `(¬ ($A ≿ $B))
| `($A:term ⋡ $B:term) => `(($A ≿ $B) ∧ ($A ≁ $B))
theorem cov_refl : ∀ A, A ≿ A := sorry
theorem cov_trans : ∀ A B, (A ≿ B) → (B ≿ C) → (A ≿ C) := sorry
theorem equinum_then_cov : ∀ A B, (A ~ B) → A ≿ B := sorry
theorem subs_then_cov : ∀ A B, (A ⊆ B) → ((B ≿ A) ∨ (A = ∅ ∧ B ≠ ∅)) := sorry


-- 9) Including and covering relation and another cover property (with Axiom of Choice)
theorem incl_cov_prop_AC : choice_ax → (∀ A B, (A ≾ B) ↔ ((B ≿ A) ∨ (A = ∅ ∧ B ≠ ∅))) := sorry
theorem cov_iff_subs_equinum_AC : choice_ax → ∀ A B, ((A ≿ B) ∨ (B = ∅ ∧ A ≠ ∅)) ↔ (∃ C, (C ⊆ A) ∧ B ~ C) := sorry


-- 10) Cantor theorem
theorem cantor_lemma : ∀ A, A ≾ 𝒫 A := sorry
theorem cantor_theorem : ∀ A, 𝒫 A ⋠ A := sorry
theorem strict_inc_infinite_chain : ∀ A, ∃ B, A ⋨ B := sorry


-- 11) Schroeder - bernstein theorem
theorem schroeder_bernstein_theorem : ∀ A B, (A ~ B) ↔ ((A ≾ B) ∧ (B ≾ A)) := sorry
-- This another theorem version requires axiom of choice:
theorem schroeder_bernstein_inc_cov_AC : choice_ax → (∀ A B, (A ~ B) ↔ ((A ≾ B) ∧ (A ≿ B))) := sorry
