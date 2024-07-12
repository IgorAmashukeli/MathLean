-- 1) Equality intro
theorem eq_intro (α : Type) (x : α) :  x = x := Eq.refl x


-- 2) Eqiality elimination
theorem eq_elim (α : Type) (P : α → Prop) (a b : α) (heq : a = b) (hpa : P a) : P b :=
   Eq.subst heq hpa


-- 3) Introduction of equality for Prop
theorem eq_prop_intro (p q : Prop) (h₁ : p → q) (h₂ : q → p) : p = q :=
   Eq.propIntro h₁ h₂


-- 4) Get element of the same type
def eq_mp (α : Type) (β : Type) (h : α = β) (a : α) : β :=
   Eq.mp h a
