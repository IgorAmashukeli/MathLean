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
   -- Of course you can say for this exact theorem: deduction_lemma (p q : Prop) (proof_stub : p → q) : p → q := proof_stub
   -- But the task is to
   -- In real examples, obviously, the proof_stub variable will not be included in the context,
   -- and some real proof after fun should be written
   -- you will write: fun (hp : p) => ..... hp
   -- where .... is some (maybe long) proof, consisting of other rules
   -- what is written in this proof dependent on the expression of p and q formulas
   -- for example, the easiest one is to prove p -> p: you just write (hp : p) => p
   -- here in this particular example ..... is actually is just identical transofrmation
   -- more complex, but at the same simple example is to prove p -> (p ∧ p)
   -- for that example, the proof will be (hp : p) => And.Intro hp hp
   -- I think, you got the idea
   -- deduction lemma rule is not one rule.
   -- These are series of proofs, parametrized by what is written instead of .....
   -- Of course, we can't proof p -> q for any p and q
   -- For that purpose, to compile the proof, proof_stub was given here to make it working
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := hpq hp



-- 5) Equivalence rules
theorem iff_intro (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := Iff.intro hpq hqp
theorem iff_mp (p q : Prop) (hpq : p ↔ q) : p → q := Iff.mp hpq
theorem iff_mpr (p q : Prop) (hqp : p ↔ q) : q → p := Iff.mpr hqp


-- 6) Negation rules
-- ¬p is defined in LEAN as p -> False
-- therefore, it is easy to work with ¬p being implication
theorem neg_intro (p : Prop) (hpF : p → False) : ¬p := hpF
theorem neg_elim (p : Prop) (hp : p) (hnp : ¬p) : False := hnp hp


-- 7) Classical rule of contradiction
theorem by_contradiction (p : Prop) (hnnp : ¬¬p) : p := Classical.byContradiction hnnp


-- 8) Universal quantifier rules
theorem universal_intro (α : Type) (P : α → Prop) (proof_stub : ∀ x : α, P x) : ∀ x : α, P x :=
   fun (x : α) => proof_stub x
   -- Again, here, the universal_intro is not a rule, but series of rules
   -- Therefore we had to insert proof_stub
   -- In real examples, proof_stub variable will not be included from context,
   -- and some real proof after fun should be written
   -- For example, if you want to prove ∀ x : α, (¬¬P x -> Px)
   -- you can write: fun (x : α) => (fun (hnnp : ¬¬P x) => Classical.byContradiction hnnp)
   -- the inner proof proves (¬¬P x -> Px) for given P and x
   -- the outer proof proves the whole (∀ x : α, (¬¬P x -> Px)) statement for given P
theorem universal_elim (α : Type) (P : α → Prop) (h : ∀ x, P x) (t : α) : P t :=
   h t


-- 9) Existential quantifier rules
theorem existential_intro (α : Type) (P : α → Prop) (x₀ : α) (hx₀ : P x₀) : ∃ x : α, P x :=
   Exists.intro x₀ hx₀
theorem existential_elim (α : Type) (P : α → Prop) (q : Prop) (h : ∃ x : α, P x) (hxq : ∀ x : α, P x → q) : q :=
   Exists.elim h hxq


-- 10) Inhabited type property
theorem inh_property (α : Type) [Inhabited α] : α := Inhabited.default


-- 11) Equality intro
theorem eq_intro (α : Type) (x : α) : x = x := Eq.refl x


-- 12) Eqiality elimination
theorem eq_elim (α : Type) (P : α → Prop) (a b : α) (heq : a = b) (hpa : P a) : P b :=
   Eq.subst heq hpa


-- 13) Introduction of equality for Prop
theorem eq_prop_intro (p q : Prop) (h₁ : p → q) (h₂ : q → p) : p = q :=
   Eq.propIntro h₁ h₂


-- 14) Get element of the same type
def eq_mp (α : Type) (β : Type) (h : α = β) (a : α) : β :=
   Eq.mp h a
