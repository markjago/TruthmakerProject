-- Problems/BilateralConjectures.lean
-- Conjectures about the bilateral, fusion-closed entailment system.
-- All statements use full-disjunctive entailment (⊨ᶠᵈ) as the default notion
-- of entailment, following the convention of Extensions.BilateralEntailment.
--
-- Within this file, bare ⊨ means ⊨ᶠᵈ (full-disjunctive entailment).

import Core.Axioms
import Extensions.Content
import Extensions.Closure
import Extensions.ClosureEntailment
import Extensions.BilateralEntailment
import Extensions.NormalForms

open Formula

local infix:50 " ⊨ " => full_disj_entails
local infix:50 " ≡ " => full_disj_equiv


-- QUASI-DISTRIBUTION (∧)
--
-- Conjecture: A ⋀ B ⊨ A ⋀ (B ⋁ C)
-- Intuitively: if you have both A and B, you have A together with (B or C).
theorem quasi_distribution_conj : ∀ A B C,
    (A ⋀ B) ⊨ (A ⋀ (B ⋁ C)) := by
  sorry

-- Conjecture (Quasi-distribution ∨): A ⋁ B ⊨ A ⋁ (B ⋀ C)
-- Intuitively: if you have A or B, you have A or (B together with C).
theorem quasi_distribution_disj : ∀ A B C,
    (A ⋁ B) ⊨ (A ⋁ (B ⋀ C)) := by
  sorry


-- BIRKHOFF
--
-- Conjecture: A ⋁ (A ⋀ B) ≡ A ⋀ (A ⋁ B)
-- The absorption identity: the two ways of "mixing" A with (A ∧ B) and (A ∨ B)
-- give the same result.
theorem birkhoff : ∀ A B,
    (A ⋁ (A ⋀ B)) ≡ (A ⋀ (A ⋁ B)) := by
  sorry


-- MONOTONICITY

-- Conjecture (Monotonicity ∧): If A ⊨ B then A ⋀ C ⊨ B ⋀ C
theorem monotonicity_conj : ∀ A B C,
    (A ⊨ B) → (A ⋀ C) ⊨ (B ⋀ C) := by
  sorry

-- Conjecture (Monotonicity ∨): If A ⊨ B then A ⋁ C ⊨ B ⋁ C
theorem monotonicity_disj : ∀ A B C,
    (A ⊨ B) → (A ⋁ C) ⊨ (B ⋁ C) := by
  sorry


-- EQUIVALENCE OF QUASI-DISTRIBUTION AND MONOTONICITY

-- Conjecture: quasi-distribution (∧) and monotonicity (∧) are equivalent schemas.
-- i.e., the schema (A ⋀ B ⊨ A ⋀ (B ⋁ C)) holds for all A, B, C
-- iff the schema (A ⊨ B → A ⋀ C ⊨ B ⋀ C) holds for all A, B, C.
theorem quasi_dist_conj_iff_mono_conj :
    (∀ A B C, (A ⋀ B) ⊨ (A ⋀ (B ⋁ C))) ↔
    (∀ A B C, (A ⊨ B) → (A ⋀ C) ⊨ (B ⋀ C)) := by
  sorry

-- Conjecture: quasi-distribution (∨) and monotonicity (∨) are equivalent schemas.
-- i.e., the schema (A ⋁ B ⊨ A ⋁ (B ⋀ C)) holds for all A, B, C
-- iff the schema (A ⊨ B → A ⋁ C ⊨ B ⋁ C) holds for all A, B, C.
theorem quasi_dist_disj_iff_mono_disj :
    (∀ A B C, (A ⋁ B) ⊨ (A ⋁ (B ⋀ C))) ↔
    (∀ A B C, (A ⊨ B) → (A ⋁ C) ⊨ (B ⋁ C)) := by
  sorry


-- NORMAL FORMS
--
-- toDNF is axiomatised in Extensions.NormalForms: toDNF(A) is a standard DNF
-- formula with the same truthmakers as A. See toDNF_is_dnf and toDNF_equiv.

-- Conjecture: toDNF(A) ⊨ A
theorem dnf_entails : ∀ A, toDNF A ⊨ A := by
  sorry

-- Conjecture: [A]⁺ = [toDNF(A)]⁺
-- A and its standard DNF have the same closed truthmaker content.
theorem dnf_same_pos_content : ∀ A,
    closure (tm_set A) = closure (tm_set (toDNF A)) := by
  sorry
