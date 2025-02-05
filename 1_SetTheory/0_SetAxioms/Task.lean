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



-- 4) The problem of naive set theory
-- comprehension axiom doesn't actually hold
-- you will prove it later
def comprehension_axiom := ∀ P : Set → Prop, ∃ A, ∀ x, (x ∈ A ↔ P x)
theorem comprehension_axiom_is_wrong : ¬(comprehension_axiom) := sorry



-- 5) Empty and non-empty definitions
def empty (A : Set) : Prop := ∀ b, (b ∉ A)
def non_empty (A : Set) : Prop := ∃ b, (b ∈ A)


-- 6) Subset notation
def subset (A B : Set) : Prop := ∀ x ∈ A; x ∈ B
infix:50 (priority := high) " ⊆ " => subset
def neq_subset (A B : Set) : Prop := (A ⊆ B) ∧ (A ≠ B)
infix:50 (priority := high) " ⊊ " => neq_subset
def no_subset (A B : Set) : Prop := ¬ (A ⊆ B)
infix:50 (priority := high) " ⊈ " => no_subset


-- 7) Some useful definitions before listing ZF axioms
def set_equality (A B : Set) := ∀ x, (x ∈ A ↔ x ∈ B)
def functional_predicate (A : Set) (P : Set → Set → Prop) : Prop := ∀ x ∈ A; ∃! y, P x y
def is_successor (m n : Set) : Prop := ∀ x, (x ∈ n ↔ x ∈ m ∨ x = m)


-- 8) ZF axioms
-- set equality implies logical equality of objects of type Set
axiom extensionality : ∀ A B, set_equality A B → (A = B)
-- there exists a set of all subsets of a set
axiom boolean : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ x ⊆ A)
-- there exists a union of a set
axiom union : ∀ A, ∃ B, ∀ x, (x ∈ B ↔ ∃ y ∈ A; x ∈ y)
-- there exists an infinite set with a special structure
axiom infinity : ∃ A, (∃ b, empty b ∧ b ∈ A) ∧ (∀ x ∈ A; ∀ y, is_successor x y → y ∈ A)
-- if P is a functional 2-variable predicate for set A, then there exists an image of this predicate
axiom replacement (P : Set → Set → Prop) : ∀ A, functional_predicate A P → ∃ B, ∀ y, (y ∈ B ↔ ∃ x ∈ A; P x y)
-- in all non-empty set there exists a set, which elements can't be "on the level" of elements of A
axiom regularity : ∀ A, non_empty A → ∃ B ∈ A; ∀ x ∈ B; x ∉ A

-- There is another (rather controversial) - last axiom - axiom of choce
-- It it is very huge to write it right here without all the future constructions and defintions
-- Therefore, it will be defined in the fourth (4_Functions) chapter


-- 9) Also we are introducing another type - Class and theory - NGB set theory
-- Here we are listing its axioms. At some point we will need this
-- Later we will generally use ZFC and NGB will be

-- Class type
axiom Class : Type
axiom cl_membership : Class → Class → Prop
infix:50 (priority := high) " ∈ " => cl_membership
infix:50 (priority := high) " ∉ " => (fun (X : Class) => (fun (Y : Class) => ¬ membership X Y))
axiom class_intro (P : Class → Prop) (h : ∃! X, P X) : Class
axiom class_intro_prop (P : Class → Prop) (h : ∃! X, P X) : P (class_intro P h) ∧ ∀ X, P X → (X = class_intro P h)

def exists_subset : ∃ (A B : Type) [setoid B], ∀ (a : A), ∃ (b : B), a ≈ b
