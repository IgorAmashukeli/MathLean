-- 1) True and False properties
theorem neg_true : ¬ True ↔ False := sorry
theorem neg_false : ¬ False ↔ True := sorry
theorem conj_true (p : Prop) : p ∧ True ↔ p := sorry
theorem conj_false (p : Prop) : p ∧ False ↔ False := sorry
theorem disj_true (p : Prop) : p ∨ True ↔ True := sorry
theorem disj_false (p : Prop) : p ∨ False ↔ p := sorry
theorem impl_true (p : Prop) : p → True ↔ True := sorry
theorem true_impl (p : Prop) : True → p ↔ p := sorry
theorem impl_false (p : Prop) : p → False ↔ ¬ p := sorry
theorem false_impl (p : Prop) : False → p ↔ True := sorry


-- 2) Idempodent properties of propositional logic
theorem axiomatic_rule (p : Prop) : p → p := sorry
theorem trivial_equivalence (p : Prop) : p ↔ p := sorry
theorem conj_idemp (p : Prop) : p ↔ p ∧ p := sorry
theorem disj_idemp (p : Prop) : p ↔ p ∨ p := sorry


-- 3) Absortion properties of propositional logic
theorem absorbtion_disj (p q : Prop) : p ∨ (p ∧ q) ↔ p := sorry
theorem absorbtion_conj (p q : Prop) : p ∧ (p ∨ q) ↔ p := sorry


-- 4) Commutativity properties of propositional logic
theorem conj_comm (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := sorry
theorem disj_comm (p q : Prop) : (p ∨ q) ↔ (q ∨ p) := sorry
theorem impl_comm (p q : Prop) : (p ↔ q) ↔ (q ↔ p) := sorry


-- 5) Associativity properties of propositional logic
theorem conj_assoc (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
theorem disj_assoc (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry


-- 6) Distributivity of propositional logic
theorem conj_disj_distrib (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
theorem disj_conj_distrib (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry


-- 7) De morgan intutionists laws of propositional logic
theorem morgan_disj (p q : Prop) :  ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
theorem morgan_conj_mpr (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q) := sorry


-- 8) Implication and negative implication sufficiencies
theorem neg_to_impl (p q : Prop) : ¬p → (p → q) := sorry
theorem impl_def_mpr (p q : Prop) : (¬p ∨ q) → (p → q) := sorry
theorem neg_imp_def_mpr (p q : Prop) : p ∧ ¬q → ¬(p → q) := sorry


-- 9) Direct contraposition
theorem contraposition_mp (p q : Prop) : (p → q) → (¬q → ¬p) := sorry


-- 10) Exportation (currying) law
theorem exportation_law (p q r : Prop) : (p → (q → r)) ↔ (p ∧ q → r) := sorry


-- 11) Disjunction in implication antecedent
theorem cases_impl_left (p q r : Prop) : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry


-- 12) Syllogism
theorem syllogism (p q r : Prop) : (p → q) → (q → r) → (p → r) := sorry


-- 13) Congruence laws
theorem neg_congr (p q : Prop) : (p ↔ q) → (¬p ↔ ¬q) := sorry
theorem disj_congr (p q r : Prop) : (p ↔ q) → ((p ∨ r) ↔ (q ∨ r)) := sorry
theorem conj_congr (p q r : Prop) : (p ↔ q) → ((p ∧ r) ↔ (q ∧ r)) := sorry
theorem impl_congr_right (p q r : Prop) : (p ↔ q) → ((p → r) ↔ (q → r)) := sorry
theorem impl_congr_left (p q r : Prop) : (p ↔ q) → ((r → p) ↔ (r → q)) := sorry
theorem iff_congr_ (p q r : Prop) : (p ↔ q) → ((p ↔ r) ↔ (q ↔ r)) := sorry


-- 14) Equivalence to both conditions
theorem iff_conj_intro(p q r : Prop) : (p ↔ q) → (p ↔ r) → (p ↔ (q ∧ r)) := sorry

-- 15) Transitivity of equivalence
theorem iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r) := sorry


-- 16) Noncontradiction law
theorem no_contradiction (p : Prop) : ¬ (p ∧ ¬ p) := sorry


-- 17) Direct double negation
theorem double_negation_mp (p : Prop) : p → ¬¬ p := sorry


-- 18) Nonequivalence of opposites
theorem negation_not_equiv (p : Prop) : ¬(p ↔ ¬p) := sorry


-- 19) Classical double negation
theorem double_negation (p : Prop) : p ↔ ¬¬p := sorry


-- 20) Classical tertsium non datur (law of excluded middle)
theorem tnd (p : Prop) : p ∨ ¬ p := sorry


-- 21) Classical cases analysis
theorem cases_analysis (p q : Prop) : (p → q) → (¬p → q) → q := sorry


-- 22) Classical disjunction in implication consequent
theorem cases_impl_right (p q r : Prop) : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry


-- 23) Classical disjunction de morgan law
theorem Morgan_disj (p q : Prop) : ¬ (p ∧ q) ↔ ¬p ∨ ¬q := sorry


-- 24) Implication and Negation of implication laws
theorem imp_def (p q : Prop) : (p → q) ↔ (¬p ∨ q) := sorry
theorem neg_imp_def (p q : Prop) :  ¬ (p → q) ↔ p ∧ ¬ q := sorry


-- 26) Contraposition law
theorem contraposition (p q : Prop) : (p → q) ↔ (¬q → ¬p) := sorry


-- 27) Peirce law
theorem peirce (p q : Prop) : (((p → q) → p) → p) := sorry
