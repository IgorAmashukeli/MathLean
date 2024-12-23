import «Header»

-- 1) Creation of a new type: Set, it has only one predicate: membership
axiom Set : Type
axiom membership : Set → Set → Prop
infix:50 (priority := high) " ∈ " => membership
infix:50 (priority := high) " ∉ " => (fun (x : Set) => (fun (y : Set) => ¬ membership x y))


-- 2) To construct an actual object of type Set
-- that is characterized by property P,
-- prove that there exists unique x with property P x
axiom set_intro (P : Set → Prop) (h : ∃! x, P x) : Set

-- created set will have the property P and only it will have it property P
axiom set_intro_prop (P : Set → Prop) (h : ∃! x, P x) : P (set_intro P h) ∧ ∀ x, P x → (x = set_intro P h)


-- 3) Creation of new ∀ x ∈ A/∃ x ∈ A/∃! x ∈ A notations
def forall_in_A (P : Set → Prop) (A : Set) : Prop := (∀ x, (x ∈ A → P x))
def exists_in_A (P : Set → Prop) (A : Set) : Prop := (∃ x, (x ∈ A ∧ P x))
def exists_uniq_in_A (P : Set → Prop) (A : Set) : Prop := (∃! x, (x ∈ A ∧ P x))
declare_syntax_cat idents
syntax ident : idents
syntax ident idents : idents
syntax "∀" idents "∈" term ";" term : term
syntax "∃" idents "∈" term ";" term : term
syntax "∃!" idents "∈" term ";" term : term
macro_rules
  | `(∀ $idnt:ident ∈ $A:term; $b:term)  => `(forall_in_A (fun $idnt:ident => $b) $A)
  | `(∀ $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(forall_in_A (fun $idnt:ident => (∀ $idnts:idents ∈ $A; $b)) $A)
  | `(∃ $idnt:ident ∈ $A:term; $b:term)  => `(exists_in_A (fun $idnt:ident => $b) $A)
  | `(∃ $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(exists_in_A (fun $idnt:ident => (∃ $idnts:idents ∈ $A; $b)) $A)
  | `(∃! $idnt:ident ∈ $A:term; $b:term)  => `(exists_uniq_in_A (fun $idnt:ident => $b) $A)
  | `(∃! $idnt:ident $idnts:idents ∈ $A:term; $b:term) => `(exists_uniq_in_A (fun $idnt:ident => (∃ $idnts:idents ∈ $A; $b)) $A)


theorem Russel_paradox : ¬ ∃ A, ∀ x, (x ∈ A ↔ x ∉ x) :=
  fun (h : ∃ A, ∀ x, (x ∈ A ↔ x ∉ x)) =>
    Exists.elim h
    (
      fun (Russel) =>
        fun (hw : ∀ x, (x ∈ Russel ↔ x ∉ x)) =>
          (negation_not_equiv (Russel ∈ Russel)) (hw Russel)
    )

def comprehension_axiom := ∀ P : Set → Prop, ∃ A, ∀ x, (x ∈ A ↔ P x)
theorem comprehension_axiom_is_wrong : ¬(comprehension_axiom) :=
  fun (hcomp) =>
    let badP := fun (x) => x ∉ x
    Russel_paradox (
      hcomp badP
    )
