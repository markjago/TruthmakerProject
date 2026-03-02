-- Extensions/Content.lean
-- Truthmaker and falsitymaker sets (content of formulas)
-- Lifted fusion operation on sets of states

import Core.Basic
import Core.Axioms

open Formula


-- TRUTHMAKER AND FALSITYMAKER SETS

-- Truthmaker set: all states that exactly truthmake A
def tm_set (A : Formula) : Set State :=
  { s : State | s ⊩ A }

-- Falsitymaker set: all states that exactly falsitymake A
def fm_set (A : Formula) : Set State :=
  { s : State | s ⫣ A }

-- Note: For notation |A|⁺ and |A|⁻, we use the function names directly
-- as Lean's notation system has difficulty with the vertical bar syntax


-- LIFTED FUSION ON SETS

-- Set fusion: all pairwise fusions of elements from T and U
def set_fusion (T U : Set State) : Set State :=
  { s : State | ∃ t u, t ∈ T ∧ u ∈ U ∧ s = t ⊔ u }

-- Notation for set fusion (distinct from pairwise fusion)
infixl:65 " ⊔ₛ " => set_fusion


-- CONTENT THEOREMS

-- Truthmaker set of conjunction is the set fusion of component truthmaker sets
theorem tm_set_conj : ∀ A B,
  tm_set (A ⋀ B) = set_fusion (tm_set A) (tm_set B) := by
  intro A B
  ext s
  simp only [tm_set, set_fusion, Set.mem_setOf_eq]
  constructor
  · intro h
    rw [tm_conj] at h
    obtain ⟨t, u, heq, ht, hu⟩ := h
    exact ⟨t, u, ht, hu, heq⟩
  · intro ⟨t, u, ht, hu, heq⟩
    rw [tm_conj]
    exact ⟨t, u, heq, ht, hu⟩

-- Falsitymaker set of disjunction is the set fusion of component falsitymaker sets
theorem fm_set_disj : ∀ A B,
  fm_set (A ⋁ B) = set_fusion (fm_set A) (fm_set B) := by
  intro A B
  ext s
  simp only [fm_set, set_fusion, Set.mem_setOf_eq]
  constructor
  · intro h
    rw [fm_disj] at h
    obtain ⟨t, u, heq, ht, hu⟩ := h
    exact ⟨t, u, ht, hu, heq⟩
  · intro ⟨t, u, ht, hu, heq⟩
    rw [fm_disj]
    exact ⟨t, u, heq, ht, hu⟩

-- Truthmaker set of disjunction is the union of component truthmaker sets
theorem tm_set_disj : ∀ A B,
  tm_set (A ⋁ B) = tm_set A ∪ tm_set B := by
  intro A B
  ext s
  simp only [tm_set, Set.mem_setOf_eq, Set.mem_union]
  rw [tm_disj]

-- Falsitymaker set of conjunction is the union of component falsitymaker sets
theorem fm_set_conj : ∀ A B,
  fm_set (A ⋀ B) = fm_set A ∪ fm_set B := by
  intro A B
  ext s
  simp only [fm_set, Set.mem_setOf_eq, Set.mem_union]
  rw [fm_conj]

-- Truthmaker set of negation equals falsitymaker set of negated formula
theorem tm_set_neg : ∀ A,
  tm_set (∼A) = fm_set A := by
  intro A
  ext s
  simp only [tm_set, fm_set, Set.mem_setOf_eq]
  rw [tm_neg]

-- Falsitymaker set of negation equals truthmaker set of negated formula
theorem fm_set_neg : ∀ A,
  fm_set (∼A) = tm_set A := by
  intro A
  ext s
  simp only [tm_set, fm_set, Set.mem_setOf_eq]
  rw [fm_neg]

