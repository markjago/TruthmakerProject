-- Core/Entailment.lean
-- Entailment and equivalence relations for truthmaker semantics
-- Provides abstract framework and basic instances for raw set content

import Core.Basic
import Core.Axioms
import Extensions.Content

open Formula


/- ABSTRACT ENTAILMENT FRAMEWORK -/

-- Terminology:
--   "Exact" (unilateral) entailment/equivalence is defined in terms of truthmakers only.
--     A exactly entails B iff every truthmaker of A is a truthmaker of B.
--     A and B are exactly equivalent iff they have the same truthmakers.
--   "Full"  (bilateral)  entailment/equivalence is defined in terms of both truthmakers
--     and falsitymakers.
--     A fully entails B iff every truthmaker of A is a truthmaker of B,
--     AND every falsitymaker of B is a falsitymaker of A.
--     A and B are fully equivalent iff they have the same truthmakers and the same
--     falsitymakers.

-- Generic exact (unilateral) entailment parameterized by content function
-- A exactly entails B when the content of A is included in the content of B
def exact_entails_by (content : Formula → Set State) (A B : Formula) : Prop :=
  content A ⊆ content B

-- Generic full (bilateral) entailment parameterized by positive and negative content functions
-- A fully entails B when:
--   (1) the positive content of A is included in the positive content of B, AND
--   (2) the negative content of B is included in the negative content of A
def full_entails_by (pos neg : Formula → Set State) (A B : Formula) : Prop :=
  (pos A ⊆ pos B) ∧ (neg B ⊆ neg A)


/- BASIC INSTANCES (Raw Sets) -/

-- Exact entailment using raw truthmaker sets
def exact_entails : Formula → Formula → Prop :=
  exact_entails_by tm_set

-- Full entailment using raw truthmaker and falsitymaker sets
def full_entails : Formula → Formula → Prop :=
  full_entails_by tm_set fm_set

-- Notation for basic entailments (using subscripts to distinguish types)
infix:50 " ⊨ₑ " => exact_entails   -- \|= \e
infix:50 " ⊨ᶠ " => full_entails    -- \|= \f


/- EQUIVALENCE RELATIONS -/

-- Exact equivalence: mutual exact entailment
def exact_equiv (A B : Formula) : Prop :=
  exact_entails A B ∧ exact_entails B A

-- Full equivalence: mutual full entailment
def full_equiv (A B : Formula) : Prop :=
  full_entails A B ∧ full_entails B A

-- Notation for equivalences
infix:50 " ≡ₑ " => exact_equiv    -- \equiv \e
infix:50 " ≡ᶠ " => full_equiv     -- \equiv \f


/- BASIC THEOREMS -/

-- Exact entailment is reflexive
theorem exact_entails_refl : ∀ A, exact_entails A A := by
  intro A
  unfold exact_entails exact_entails_by
  -- tm_set A ⊆ tm_set A is trivially true
  exact Set.Subset.refl (tm_set A)

-- Exact entailment is transitive
theorem exact_entails_trans : ∀ A B C,
  exact_entails A B → exact_entails B C → exact_entails A C := by
  intro A B C hab hbc
  unfold exact_entails exact_entails_by at *
  -- Transitivity of ⊆
  exact Set.Subset.trans hab hbc

-- Full entailment is reflexive
theorem full_entails_refl : ∀ A, full_entails A A := by
  intro A
  unfold full_entails full_entails_by
  constructor
  · exact Set.Subset.refl (tm_set A)
  · exact Set.Subset.refl (fm_set A)

-- Full entailment is transitive
theorem full_entails_trans : ∀ A B C,
  full_entails A B → full_entails B C → full_entails A C := by
  intro A B C ⟨hab_pos, hab_neg⟩ ⟨hbc_pos, hbc_neg⟩
  unfold full_entails full_entails_by
  constructor
  · exact Set.Subset.trans hab_pos hbc_pos
  · exact Set.Subset.trans hbc_neg hab_neg

-- Full entailment implies exact entailment
theorem full_implies_exact : ∀ A B, full_entails A B → exact_entails A B := by
  intro A B ⟨hpos, _⟩
  unfold exact_entails exact_entails_by
  exact hpos

-- Exact equivalence is symmetric
theorem exact_equiv_symm : ∀ A B, exact_equiv A B → exact_equiv B A := by
  intro A B ⟨hab, hba⟩
  unfold exact_equiv
  exact ⟨hba, hab⟩

-- Full equivalence is symmetric
theorem full_equiv_symm : ∀ A B, full_equiv A B → full_equiv B A := by
  intro A B ⟨hab, hba⟩
  unfold full_equiv
  exact ⟨hba, hab⟩

-- Exact equivalence is reflexive
theorem exact_equiv_refl : ∀ A, exact_equiv A A := by
  intro A
  unfold exact_equiv
  exact ⟨exact_entails_refl A, exact_entails_refl A⟩

-- Exact equivalence is transitive
theorem exact_equiv_trans : ∀ A B C,
  exact_equiv A B → exact_equiv B C → exact_equiv A C := by
  intro A B C ⟨hab1, hab2⟩ ⟨hbc1, hbc2⟩
  unfold exact_equiv
  constructor
  · exact exact_entails_trans A B C hab1 hbc1
  · exact exact_entails_trans C B A hbc2 hab2

-- Full equivalence is reflexive
theorem full_equiv_refl : ∀ A, full_equiv A A := by
  intro A
  unfold full_equiv
  exact ⟨full_entails_refl A, full_entails_refl A⟩

-- Full equivalence is transitive
theorem full_equiv_trans : ∀ A B C,
  full_equiv A B → full_equiv B C → full_equiv A C := by
  intro A B C ⟨hab1, hab2⟩ ⟨hbc1, hbc2⟩
  unfold full_equiv
  constructor
  · exact full_entails_trans A B C hab1 hbc1
  · exact full_entails_trans C B A hbc2 hab2
