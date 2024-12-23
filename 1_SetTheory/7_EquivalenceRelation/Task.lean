import «Header»

-- 1) Definition of equivalence relation, set of all equivalence relations on one set and their simple properties

def equivalence_relation (A R : Set) := (R BinRelOn A) ∧ (refl R A) ∧ (symm R) ∧ (transit R)
syntax term "EquivRel" term : term
macro_rules
| `($R EquivRel $A) => `(equivalence_relation $A $R)

theorem equivrel_refl : ∀ A R, (R EquivRel A) → (refl R A) := sorry
theorem equivrel_symm : ∀ A R, (R EquivRel A) → (symm R) := sorry
theorem equivrel_trans : ∀ A R, (R EquivRel A) → (transit R) := sorry

noncomputable def eqrelset (A : Set) := {R ∈ 𝒫 (A × A) | R EquivRel A}
syntax "Eq" term : term
macro_rules
| `(Eq $A) => `(eqrelset $A)
theorem eqrel_crit : ∀ A R, (R ∈ Eq A) ↔ (R EquivRel A) := sorry


-- 2) id, A × A and equivalence relations

theorem id_eqrel : ∀ A, ((id_ A) EquivRel A) := sorry
theorem allpairs_eqrel : ∀ A, ((A × A) EquivRel A) := sorry
theorem eq_rel_between : ∀ A R, (R EquivRel A) → (((id_ A) ⊆ (R)) ∧ (R ⊆ (A × A))) := sorry

-- 3) if we have some reflexive, symmetric, transitive predicate specification set on A, then it is equivalence relation

theorem bin_equivrel (φ : Set → Set → Prop) :
∀ A, ((∀ x ∈ A; φ x x) ∧ (∀ x y, φ x y → φ y x) ∧ (∀ x y z, (φ x y ∧ φ y z) → (φ x z))) → ({R ∈ (A × A) | φ (π₁ R) (π₂ R)} EquivRel A) := sorry

-- 4) Another examples of equivalence relation:

noncomputable def equinum_rel (A : Set) := {R ∈ (A × A) | ((π₁ R) ~ (π₂ R))}
syntax "Equin" term : term
macro_rules
| `(Equin $A) => `(equinum_rel $A)

noncomputable def oiso_rel (A : Set) := {R ∈ (A × A) | (π₁ R) ≃O (π₂ R)}
syntax "Oiso" term : term
macro_rules
| `(Oiso $A) => `(oiso_rel $A)

theorem equinum_equivrel : ∀ A, ((Equin A) EquivRel A) := sorry
theorem oiso_equivrel : ∀ A, ((Oiso A) EquivRel A) := sorry

-- 5) Operations on equivalence relation that produce equivalence relation

noncomputable def cart_equiv (A B R S : Set) :=
{pr ∈ ((A × B) × (A × B)) | ((π₁ (π₁ pr)) . R . (π₁ (π₂ pr))) ∧ ((π₂ (π₁ pr)) . S . (π₂ (π₂ pr)))}
syntax term "Cart" term "On" term "And" term : term
macro_rules
| `($R Cart $S On $A And $B) => `(cart_equiv $A $B $R $S)

theorem equivrel_inv : ∀ R A, (R EquivRel A) → (R = (R⁻¹)) := sorry
theorem equivrel_cart : ∀ A B R S, (R EquivRel A) → (S EquivRel B) → ((R Cart S On A And B) EquivRel (A × B)) := sorry
theorem equivrel_int: ∀ X A, (X ≠ ∅) → (∀ R ∈ X; (R EquivRel A)) → ((⋂ X) EquivRel A) := sorry
theorem equivrel_int2 : ∀ R S, (R EquivRel A) → (S EquivRel A) → ((R ∩ S) EquivRel A) := sorry
theorem equivrel_intind : ∀ X I A, (I ≠ ∅) → (X IndxFun I) → (∀ i ∈ I; ((A _ i) EquivRel A)) → ((⋂[ i in I ] X at i) EquivRel A) := sorry


-- 6) Kernel of function is a equivalence relation

noncomputable def kernel_func (f A : Set) := {R ∈ (A × A) | f⦅π₁ R⦆ = f⦅π₂ R⦆}
syntax "ker" term "On" term : term
macro_rules
| `(ker $f On $A) => `(kernel_func $f $A)

theorem kernel_crit : ∀ f A, ∀ x y ∈ A; ((x, y) ∈ (ker f On A)) ↔ (f⦅x⦆ = f⦅y⦆) := sorry
theorem kernel_equivrel : ∀ A f, ((ker f On A) EquivRel A) := sorry
theorem kernel_inj_crit : ∀ A B f, (f Fun A To B) → ((f Inj A To B) ↔ ((ker f On A) = id_ A)) := sorry
theorem kerneleq_cond : ∀ A R f, (R EquivRel A) → ((R = ker f On A) ↔ (∀ x y ∈ A; (x . R . y) ↔ (f⦅x⦆ = f⦅y⦆))) := sorry

-- 7) Equivalence classes and its properties

noncomputable def equiv_class (R A x) := {y ∈ A | (x . R . y)}
syntax "[" term "]" "Of" term "On" term : term
macro_rules
| `([ $x ] Of $R On $A) => `(equiv_class $R $A $x)
theorem equiv_class_sub : ∀ A R x, ([x] Of R On A) ⊆ A := sorry
theorem in_euiv_class₁ : ∀ A R x, ∀ y ∈ A; ((y ∈ ([x] Of R On A)) ↔ (x . R . y)) := sorry
theorem in_euiv_class₂ : ∀ A R x y, ((y ∈ ([x] Of R On A)) ↔ (y ∈ A ∧ (x . R . y))) := sorry

theorem equiv_class_x_in : ∀ A R, ∀ x ∈ A; (R EquivRel A) → (x ∈ ([x] Of R On A)) := sorry
theorem equiv_class_internemp : ∀ A R, ∀ x y ∈ A; (R EquivRel A) →
(((([x] Of R On A) ∩ ([y] Of R On A) ≠ ∅) ↔ (x . R . y)) ∧
((([x] Of R On A) ∩ ([y] Of R On A) ≠ ∅) ↔ (([x] Of R On A) = ([y] Of R On A))) ∧
((x . R . y) ↔ (([x] Of R On A) = ([y] Of R On A)))) := sorry


-- 8) Factor set, its properties

noncomputable def factor_set (R A) := {S ∈ 𝒫 (A) | ∃ x ∈ A; S = ([x] Of R On A)}
syntax term "./" term : term
macro_rules
| `($A ./ $R) => `(factor_set $R $A)

noncomputable def singl_set (A) := {S ∈ 𝒫 (A) | ∃ x ∈ A; S = {x}}

theorem factorset_prop : ∀ A R S, (S ∈ (A ./ R) ↔ (∃ x ∈ A; S = ([x] Of R On A))) := sorry
theorem factor_set_in : ∀ A R, ∀ x ∈ A; ([x] Of R On A) ∈ (A ./ R) := sorry
theorem factor_set_union : ∀ A R, (R EquivRel A) → (⋃ (A ./ R)) = A := sorry

theorem factor_id : ∀ A, (A ./ (id_ A)) = 𝒫₁ A := sorry
theorem factor_allpairnemp : ∀ A, (A ≠ ∅) → (A ./ (A × A)) = {A} := sorry
theorem factor_allpairemp : ∀ A, (A = ∅) → (A ./ (A × A)) = A := sorry

noncomputable def all_preimage_set (A f) := {S ∈ 𝒫 (A) | ∃ z ∈ rng f; S = f⁻¹.[z]}
syntax "PreImAll" term "On" term : term
macro_rules
| `(PreImAll $f On $A) => `(all_preimage_set $A $f)

theorem factor_kernel : ∀ A B f, (f Fun A To B) → (A ./ (ker f On A)) = PreImAll f On A := sorry

-- 9) Natural projection and its properties

noncomputable def natural_projection (A R : Set) := lam_fun A (A ./ R) (fun (x) => [x] Of R On A)
syntax term "ProjFun" term : term
macro_rules
| `($R ProjFun $A) => `(natural_projection $A $R)

theorem natproj_fun : ∀ A R, (R ProjFun A) Fun A To (A ./ R) := sorry
theorem natproj_prop : ∀ A R, ∀ x ∈ A; (R ProjFun A)⦅x⦆ = [x] Of R On A := sorry
theorem equivrel_kernel_natproj : ∀ A R, (R EquivRel A) → (R = ker (R ProjFun A) On A) := sorry
theorem equivrel_kernel : ∀ A R, (R EquivRel A) → (∃ f B, (f Fun A To B) ∧ (R = ker f On A)) := sorry
theorem natproj_surj : ∀ A R, ((R ProjFun A) Surj A To (A ./ R)) := sorry

-- 10) Induced function and its properties

noncomputable def induced_func (A B R f) := {s ∈ (A ./ R) × B | ∃ x ∈ A; s = ([x] Of R On A, f⦅x⦆)}
syntax term "IndFun" term "To" term "Of" term : term
macro_rules
| `($f IndFun $A To $B Of $R) => `(induced_func $A $B $R $f)


theorem kernat_ind : ∀ A B R f, (R EquivRel A) → (f Fun A To B) → (R = (ker f On A)) →
((f IndFun A To B Of R) Fun (A ./ R) To B) ∧ f = (f IndFun A To B Of R) ∘ (R ProjFun A) := sorry
theorem kernat_indval :
∀ A B R f, (R EquivRel A) → (f Fun A To B) → (R = (ker f On A)) → ∀ x ∈ A; (f IndFun A To B Of R)⦅[x] Of R On A⦆ = f⦅x⦆ := sorry
theorem kernatind_uni : ∀ A B R f, (R EquivRel A) → (f Fun A To B) → (R = (ker f On A))
 → (∃! g, (g Fun (A ./ R) To B) ∧ (f = g ∘ (R ProjFun A))) := sorry

theorem factor_kernel_equin : ∀ A B f, (f Fun A To B) → (A ./ (ker f On A)) ~ (rng f) := sorry


-- 11) Compatible relation, function and operation on factorsets

def fac_rel_compat (A R S) := (∀ r₁ r₂ ∈ (A ./ R); (r₁ . (S) . r₂) ↔ (∃ x₁ ∈ r₁; ∃ x₂ ∈ r₂; (x₁ . (R) . x₂)))
syntax term "FacCompRelWith" term "On" term : term
macro_rules
| `($S FacCompRelWith $R On $A) => `(fac_rel_compat $A $R $S)

theorem facrelcompcond : ∀ A R S, (S BinRelOn (A ./ R)) → (R EquivRel A) →
((S FacCompRelWith R On A) ↔ (∀ x₁ x₂ ∈ A; (([x₁] Of R On A) . S . ([x₂] Of R On A)) ↔ (x₁ . R . x₂))) := sorry


-- 11) Other properties of factor sets

theorem facsub_cov : ∀ A R S, (R EquivRel A) → (S EquivRel A) → (R ⊆ S) → (A ./ R) ≿ (A ./ S) := sorry
theorem facsub_incl_ax : choice_ax → ∀ A R S, (R EquivRel A) → (S EquivRel A) → (R ⊆ S) → (A ./ S) ≾ (A ./ R) := sorry





-- 12) Partitioning and equivalence relations
