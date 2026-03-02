-- Problems/Conjunction.lean
-- Problems and conjectures specifically about conjunction behavior

import Core.Basic
import Core.Axioms
import Core.Theorems

open Formula

-- Problem: Does conjunction distribute over disjunction in truthmaker semantics?
-- In classical logic yes, but what about with exact truthmaking?

theorem conj_dist_disj : ∀ s A B C,
  (s ⊩ (A ⋀ (B ⋁ C))) → (s ⊩ ((A ⋀ B) ⋁ (A ⋀ C))) := by
  sorry

-- Reverse direction
theorem conj_dist_disj_reverse : ∀ s A B C,
  (s ⊩ ((A ⋀ B) ⋁ (A ⋀ C))) → (s ⊩ (A ⋀ (B ⋁ C))) := by
  sorry

-- Add your own conjunction-related problems here

