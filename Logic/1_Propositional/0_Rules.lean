-- 1) True and False rules
theorem true_intro : True := True.intro
theorem false_elim (p : Prop) (hFalse : False) : p := False.elim hFalse


-- 2) Conjunction rules
theorem and_intro (p q : Prop) (hp : p) (hq : q) : p ∧ q := And.intro hp hq
theorem and_left (p q : Prop) (hpq : p ∧ q) : p := And.left hpq
theorem and_right (p q : Prop) (hpq : p ∧ q) : q := And.right hpq


-- 3) Disjunction rules
theorem or_introl (p q : Prop) (hp : p) : p ∨ q := Or.inl hp
theorem or_intror (p q : Prop) (hq : q) : p ∨ q := Or.inr hq
theorem or_elim (p q r : Prop) (hpq : p ∨ q) (hpr : p → r) (hqr : q → r) : r := Or.elim hpq hpr hqr


-- 4) Implication rules
theorem deduction_lemma (p q : Prop) (proof_stub : p → q) : p → q :=
   fun (hp : p) => proof_stub hp
   -- In real examples, proof_stub variable must be removed from context,
   -- and some real proof after fun should be written
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := hpq hp



-- 5) Equivalence rules
theorem iff_intro (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := Iff.intro hpq hqp
theorem iff_mp (p q : Prop) (hpq : p ↔ q) : p → q := Iff.mp hpq
theorem iff_mpr (p q : Prop) (hqp : p ↔ q) : q → p := Iff.mpr hqp


-- 6) Negation rules
theorem neg_intro (p : Prop) (hpF : p → False) : ¬p := hpF
theorem neg_elim (p : Prop) (hp : p) (hnp : ¬p) : False := hnp hp


-- 7) Classical rule of contradiction
open Classical
theorem by_contradiction (p : Prop) (hnnp : ¬¬p) : p := byContradiction hnnp
