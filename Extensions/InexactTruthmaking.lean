-- Extensions/InexactTruthmaking.lean
-- Inexact truthmaking and falsitymaking relations
-- s inexactly truthmakes A iff some part of s exactly truthmakes A

import Core.Basic
import Core.Axioms

open Formula


-- INEXACT TRUTHMAKING AND FALSITYMAKING

-- Inexact truthmaking: s ⊩ᵢ A iff some part of s exactly truthmakes A
def inexact_truthmakes (s : State) (A : Formula) : Prop :=
  ∃ u, u ⊑ s ∧ u ⊩ A

-- Notation: ⊩ᵢ (subscript i for "inexact")
infix:50 " ⊩ᵢ " => inexact_truthmakes

-- Inexact falsitymaking: s ⫣ᵢ A iff some part of s exactly falsitymakes A
def inexact_falsitymakes (s : State) (A : Formula) : Prop :=
  ∃ u, u ⊑ s ∧ u ⫣ A

-- Notation: ⫣ᵢ (subscript i for "inexact")
infix:50 " ⫣ᵢ " => inexact_falsitymakes


-- EXACT IMPLIES INEXACT

-- If s exactly truthmakes A, then s inexactly truthmakes A
theorem exact_implies_inexact_tm : ∀ s A,
  (s ⊩ A) → (s ⊩ᵢ A) := by
  intro s A h
  exact ⟨s, parthood_refl s, h⟩

-- If s exactly falsitymakes A, then s inexactly falsitymakes A
theorem exact_implies_inexact_fm : ∀ s A,
  (s ⫣ A) → (s ⫣ᵢ A) := by
  intro s A h
  exact ⟨s, parthood_refl s, h⟩


-- INEXACT TRUTHMAKING THEOREMS

-- Inexact conjunction: s ⊩ᵢ A ⋀ B iff s ⊩ᵢ A and s ⊩ᵢ B
theorem inexact_tm_conj : ∀ s A B,
  (s ⊩ᵢ (A ⋀ B)) ↔ ((s ⊩ᵢ A) ∧ (s ⊩ᵢ B)) := by
  sorry

-- Inexact disjunction: s ⊩ᵢ A ⋁ B iff s ⊩ᵢ A or s ⊩ᵢ B
theorem inexact_tm_disj : ∀ s A B,
  (s ⊩ᵢ (A ⋁ B)) ↔ ((s ⊩ᵢ A) ∨ (s ⊩ᵢ B)) := by
  sorry


-- INEXACT FALSITYMAKING THEOREMS

-- Inexact falsitymaking of conjunction: s ⫣ᵢ A ⋀ B iff s ⫣ᵢ A or s ⫣ᵢ B
theorem inexact_fm_conj : ∀ s A B,
  (s ⫣ᵢ (A ⋀ B)) ↔ ((s ⫣ᵢ A) ∨ (s ⫣ᵢ B)) := by
  sorry

-- Inexact falsitymaking of disjunction: s ⫣ᵢ A ⋁ B iff s ⫣ᵢ A and s ⫣ᵢ B
theorem inexact_fm_disj : ∀ s A B,
  (s ⫣ᵢ (A ⋁ B)) ↔ ((s ⫣ᵢ A) ∧ (s ⫣ᵢ B)) := by
  sorry
