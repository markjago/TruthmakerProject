-- Problems/Hyperintensionality.lean
-- Conjectures and problems related to hyperintensional distinctions

import Core.Basic
import Core.Axioms
import Core.Theorems
import Core.Entailment

open Formula

-- PROBLEM 1: Example problem structure
-- State your conjecture, then try to prove it

-- Conjecture: Two necessarily equivalent formulas might have different truthmakers
-- (This demonstrates hyperintensionality)

-- Note: The notion of "same truthmakers" is now available as exact_equiv from Core.Entailment
-- exact_equiv A B ≡ (exact_entails A B ∧ exact_entails B A)
--                 ≡ (tm_set A ⊆ tm_set B ∧ tm_set B ⊆ tm_set A)
--                 ≡ (tm_set A = tm_set B)

-- In truthmaker semantics, necessary equivalence doesn't imply same truthmakers
-- (Unlike classical semantics where they would be the same)

-- Example: You might conjecture that (A ⋀ A) and A have the same truthmakers
-- theorem conj_idemp_truthmakers : ∀ A s,
--   (s ⊩ (A ⋀ A)) ↔ (s ⊩ A) := by
--   sorry


-- PROBLEM 2: Add your own conjectures here
-- theorem my_conjecture_1 : ... := by
--   sorry


-- PROBLEM 3: Template for problems you're working on
-- theorem problem_name : statement := by
--   -- Proof sketch or notes
--   sorry

