import «Header»

-- 1) Defition of A ∪ B, A ∩ B, A \ B, A △ B
noncomputable def union_2sets (A B : Set) := ⋃ {A, B}
infix:60 (priority:=high) " ∪ " => union_2sets

noncomputable def intersect_2sets (A B : Set) := {x ∈ A | x ∈ B}
infix:60 (priority:=high) " ∩ " => intersect_2sets

noncomputable def difference (A B : Set) := {x ∈ A | x ∉ B}
infix:60 (priority:=high) " \\ " => difference

noncomputable def symmetric_difference (A B : Set) := (A \ B) ∪ (B \ A)
infix:60 (priority:=high) " △ " => symmetric_difference


-- 2) Macros of set comprehension
-- {a, b, c}, {a, b, c, d}, {a, b, c, d, e}, ...
declare_syntax_cat set_comprehension
syntax term "; " set_comprehension : set_comprehension
syntax term : set_comprehension
syntax "{" set_comprehension "}" : term
macro_rules
| `({$term1:term; $term2:term}) => `(unordered_pair_set $term1:term $term2:term)
| `({$elem:term; $rest:set_comprehension}) => `({$rest:set_comprehension} ∪ {$elem:term})




-- 3) A ∪ B, A ∩ B, A \ B, A △ B main properties
theorem union2_sets_prop : (∀ A B x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B) := sorry
theorem intersect_2sets_prop : (∀ A B x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B) := sorry
theorem intersect_2sets_is_intersect : (∀ A B, (⋂ {A, B}) = A ∩ B) := sorry
theorem difference_prop : (∀ A B x, x ∈ A \ B ↔ x ∈ A ∧ x ∉ B) := sorry
theorem symmetric_difference_prop : (∀ A B x, x ∈ A △ B ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A)) := sorry


-- 4) A ∪ B subsets and A ∩ B, A \ B as subsets and their property
theorem union2sets_subset_prop : (∀ A B, (A ⊆ A ∪ B) ∧ (B ⊆ A ∪ B)) := sorry
theorem interset2sets_subset_prop : (∀ A B, (A ∩ B ⊆ A) ∧ (A ∩ B ⊆ B)) := sorry
theorem difference_subset_prop : (∀ A B, A \ B ⊆ A) := sorry
theorem sub_sub_inter_sub : ∀ A B X, (X ⊆ A) → (X ⊆ B) → (X ⊆ (A ∩ B)) := sorry
theorem sub_sub_union_sub : ∀ A B X, (A ⊆ X) → (B ⊆ X) → ((A ∪ B) ⊆ X) := sorry


-- 5) Three equivalent statements about subsets
theorem subset_using_equality : ∀ A B, (A ⊆ B ↔ A ∩ B = A) ∧ (A ⊆ B ↔ A ∪ B = B) ∧ (A ∩ B = A ↔ A ∪ B = B) := sorry



-- 6) Idempodent properties
theorem intersec2_idemp : (∀ A, A ∩ A = A) := sorry
theorem union2_idepm : (∀ A, A ∪ A = A) := sorry


-- 7) Commutativity properties
theorem intersec2_comm : (∀ A B, A ∩ B = B ∩ A) := sorry
theorem union2_comm : (∀ A B, A ∪ B = B ∪ A) := sorry


-- 8) Associativity properties
theorem inter2_assoc : (∀ A B C, (A ∩ B) ∩ C = A ∩ (B ∩ C)) := sorry
theorem union2_assoc : (∀ A B C, (A ∪ B) ∪ C = A ∪ (B ∪ C)) := sorry


-- 9) Absorbtion properties
theorem inter_union_absorbtion : (∀ A B, A ∩ (A ∪ B) = A) := sorry
theorem union_inter_absorbtion : (∀ A B, A ∪ (A ∩ B) = A) := sorry


-- 10) Distributivity properties
theorem inter_union_distribution : (∀ A B C, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)) := sorry
theorem union_inter_distribution : (∀ A B C, A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)) := sorry


-- 11) double complement property
theorem double_compl (U : Set) (A : Set)  (h : A ⊆ U) : (U \ (U \ A)) = A := sorry


-- 12) Demorgan laws
theorem demorgan_inter : ∀ U A B, (U \ (A ∩ B) = (U \ A) ∪ (U \ B)) := sorry
theorem demorgan_union: ∀ U A B, (U \ (A ∪ B) = (U \ A) ∩ (U \ B)) := sorry


-- 13) Intersection of complement sets
theorem inter_to_empty: ∀ U A, (A ∩ (U \ A) = ∅) := sorry


-- 14) Set difference equivalent form
theorem difference_inter_prop (U A B : Set) (h : A ⊆ U) : (A \ B = A ∩ (U \ B)) := sorry


-- 15) Union of complement sets
theorem union_to_universum (U A : Set) (h : A ⊆ U) : (A ∪ (U \ A) = U) := sorry


-- 16) Empty set and operations
theorem intersec2_empty : (∀ A, A ∩ ∅ = ∅) := sorry
theorem union2_empty : (∀ A, A ∪ ∅ = A) := sorry


-- 17) Universum and operations
theorem inter2_universum (U A : Set) (h : A ⊆ U) : A ∩ U = A := sorry
theorem union2_universum (U A : Set) (h : A ⊆ U) : A ∪ U = U := sorry


-- 18) Now, using set algebra properties and eq_subst, it is easy to prove the equality
-- such sets without 'low-level' manipulation with elements

-- use eq_subst and previous properties to prove 2 examples below
-- without manipulation with elements of the sets
theorem example_theorem1  : (∀ A B C, A \ (B \ C) = (A \ B) ∪ (A ∩ C)) := sorry
theorem example_theorem2 : (∀ A B, A △ B = (A ∪ B) \ (A ∩ B)) := sorry


-- 19) Negative monotic property of difference
theorem neg_mon_diff : ∀ A B C, (A ⊆ B) → (C \ B) ⊆ (C \ A) := sorry
