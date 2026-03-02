-- Extensions/BilateralEntailment.lean
-- Entailment notions for the purely bilateral (full), fusion-closed system.
--
-- Standing assumptions of this file:
--   (1) Bilateral ("full"): entailment and equivalence are defined in terms of
--       both truthmakers and falsitymakers. See Core.Entailment for terminology.
--   (2) Fusion-closed: all content sets are taken under closure (full_equiv_cl),
--       so that A ⋀ A and A ⋁ A are each equivalent to A.
--
-- Within this file, ⊨ abbreviates ⊨ᶠᵈ (full-disjunctive entailment).

import Core.Entailment
import Core.Axioms
import Extensions.Content
import Extensions.ClosureEntailment

open Formula


-- FULL-CONJUNCTIVE ENTAILMENT
--
-- A ⊨ᶠᶜ B when A ⋀ B is fully (bilaterally) equivalent to A under closed content.
-- Intuitively: conjoining B with A adds nothing — B's content is already in A's.
def full_conj_entails (A B : Formula) : Prop :=
  full_equiv_cl (A ⋀ B) A

-- Notation: ⊨ᶠᶜ  (f = full/bilateral, c = conjunctive)
infix:50 " ⊨ᶠᶜ " => full_conj_entails


-- FULL-DISJUNCTIVE ENTAILMENT
--
-- A ⊨ᶠᵈ B when A ⋁ B is fully (bilaterally) equivalent to B under closed content.
-- Intuitively: disjoining A into B adds nothing — B already subsumes A.
def full_disj_entails (A B : Formula) : Prop :=
  full_equiv_cl (A ⋁ B) B

-- Notation: ⊨ᶠᵈ  (f = full/bilateral, d = disjunctive)
infix:50 " ⊨ᶠᵈ " => full_disj_entails

-- Within this file, bare ⊨ means full-disjunctive entailment (⊨ᶠᵈ)
local infix:50 " ⊨ " => full_disj_entails


-- EQUIVALENCE RELATIONS

-- Two formulas are full-conjunctively equivalent when each conjunctively entails the other
def full_conj_equiv (A B : Formula) : Prop :=
  (A ⊨ᶠᶜ B) ∧ (B ⊨ᶠᶜ A)

-- Two formulas are full-disjunctively equivalent when each disjunctively entails the other
def full_disj_equiv (A B : Formula) : Prop :=
  (A ⊨ᶠᵈ B) ∧ (B ⊨ᶠᵈ A)

infix:50 " ≡ᶠᶜ " => full_conj_equiv
infix:50 " ≡ᶠᵈ " => full_disj_equiv


-- BASIC PROPERTIES

-- Full-conjunctive entailment is reflexive: A ⊨ᶠᶜ A
-- Requires: full_equiv_cl (A ⋀ A) A.
-- Truthmakers: closure(set_fusion(tm_set A, tm_set A)) = closure(tm_set A)
--   because closure is closed under lubs, so the fusion of any two elements of
--   closure(tm_set A) remains in closure(tm_set A).
-- Falsitymakers: closure(fm_set A ∪ fm_set A) = closure(fm_set A). ✓
theorem full_conj_entails_refl : ∀ A, A ⊨ᶠᶜ A := by
  sorry

-- Full-disjunctive entailment is reflexive: A ⊨ A
-- Requires: full_equiv_cl (A ⋁ A) A.
-- Truthmakers: closure(tm_set A ∪ tm_set A) = closure(tm_set A). ✓
-- Falsitymakers: closure(set_fusion(fm_set A, fm_set A)) = closure(fm_set A).
--   Same argument as the conjunctive case by symmetry.
theorem full_disj_entails_refl : ∀ A, A ⊨ A := by
  sorry

-- Full-conjunctive entailment is transitive
theorem full_conj_entails_trans : ∀ A B C,
    (A ⊨ᶠᶜ B) → (B ⊨ᶠᶜ C) → (A ⊨ᶠᶜ C) := by
  sorry

-- Full-disjunctive entailment is transitive
theorem full_disj_entails_trans : ∀ A B C,
    (A ⊨ B) → (B ⊨ C) → (A ⊨ C) := by
  sorry
