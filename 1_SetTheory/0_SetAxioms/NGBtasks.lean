import «Header»
import Lean.Meta
import Lean.Elab
import Lean.Elab.Command

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command

-- creation of a new type Class
axiom Class : Type
axiom membership : Class → Class → Prop
infix:50 (priority := high) " ∈ " => membership
infix:50 (priority := high) " ∉ " => (fun (X : Class) => (fun (Y : Class) => ¬ membership X Y))


-- created class will have the property P and only it will have it property P
axiom class_intro (P : Class → Prop) (h : ∃! X, P X) : Class
axiom set_intro_prop (P : Class → Prop) (h : ∃! X, P X) : P (class_intro P h) ∧ ∀ X, P X → (X = class_intro P h)

-- 3) Creation of new ∀ x ∈ A/∃ x ∈ A/∃! x ∈ A notations
def forall_in_A (P : Class → Prop) (A : Class) : Prop := (∀ X, (X ∈ A → P X))
def exists_in_A (P : Class → Prop) (A : Class) : Prop := (∃ X, (X ∈ A ∧ P X))
def exists_uniq_in_A (P : Class → Prop) (A : Class) : Prop := (∃! X, (X ∈ A ∧ P X))
declare_syntax_cat idents
syntax ident : idents
syntax ident idents : idents
syntax "∀" idents "∈" term ";" term : term
syntax "∃" idents "∈" term ";" term : term
syntax "∃!" idents "∈" term ";" term : term
macro_rules
  | `(∀ $idnt:ident ∈ $A:term; $B:term)  => `(forall_in_A (fun $idnt:ident => $B) $A)
  | `(∀ $idnt:ident $idnts:idents ∈ $A:term; $B:term) => `(forall_in_A (fun $idnt:ident => (∀ $idnts:idents ∈ $A; $B)) $A)
  | `(∃ $idnt:ident ∈ $A:term; $B:term)  => `(exists_in_A (fun $idnt:ident => $B) $A)
  | `(∃ $idnt:ident $idnts:idents ∈ $A:term; $B:term) => `(exists_in_A (fun $idnt:ident => (∃ $idnts:idents ∈ $A; $B)) $A)
  | `(∃! $idnt:ident ∈ $A:term; $B:term)  => `(exists_uniq_in_A (fun $idnt:ident => $B) $A)
  | `(∃! $idnt:ident $idnts:idents ∈ $A:term; $B:term) => `(exists_uniq_in_A (fun $idnt:ident => (∃ $idnts:idents ∈ $A; $B)) $A)


-- 5) Empty and non-empty definitions
def empty (A : Class) : Prop := ∀ B, (B ∉ A)
def non_empty (A : Class) : Prop := ∃ B, (B ∈ A)
def class_equality (A B : Class) := ∀ X, (X ∈ A ↔ X ∈ B)

def subset (A B : Class) : Prop := ∀ X ∈ A; X ∈ B
infix:50 (priority := high) " ⊆ " => subset
def neq_subset (A B : Class) : Prop := (A ⊆ B) ∧ (A ≠ B)
infix:50 (priority := high) " ⊊ " => neq_subset
def no_subset (A B : Class) : Prop := ¬ (A ⊆ B)
infix:50 (priority := high) " ⊈ " => no_subset


-- 6) Set and ProperClass definitions

def is_Set : Class → Prop := fun (X : Class) => ∃ Y, X ∈ Y
def is_Proper : Class → Prop := (fun (X : Class) => ¬ is_Set X)
def Set := {x : Class // is_Set x}

def membership_set := fun (x : Set) => fun (y : Set) => (x.val ∈ y.val)
infix:50 (priority := high) " ∈ " => membership_set
infix:50 (priority := high) " ∉ " => (fun (X : Set) => (fun (Y : Set) => ¬ membership X Y))




syntax (name := liftProp) "liftProp " term : term

macro_rules
  | `(liftProp ∀ $x:ident : Class, $body) => `(∀ $x : Set, liftProp ($body $x.val))
  | `(liftProp ∃ $x:ident : Class, $body) => `(∃ $x : Set, liftProp ($body $x.val))
  | `(liftProp ($P ∧ $Q)) => `(liftProp $P ∧ liftProp $Q)
  | `(liftProp ($P ∨ $Q)) => `(liftProp $P ∨ liftProp $Q)
  | `(liftProp ($P → $Q)) =>  `(liftProp $P → liftProp $Q)
  | `(liftProp (¬ $P)) => `(¬ liftProp $P)
  | `(liftProp $P) => -- Base case `($P)



axiom cl_extensionality : ∀ X Y : Class, class_equality X Y → X = Y
axiom st_unpair : ∀ x y : Set, ∃ z : Set, (∀ u : Set, (u ∈ z) ↔ ((u = x) ∨ (u = y)))
