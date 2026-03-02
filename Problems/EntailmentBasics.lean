-- Problems/EntailmentBasics.lean
-- Basic theorems about entailment relations
-- Proving fundamental properties and simple entailments

import Core.Basic
import Core.Axioms
import Core.Theorems
import Core.Entailment
import Extensions.Content

open Formula


/- BASIC ENTAILMENT THEOREMS -/

-- A entails A ∨ B (disjunction introduction, left)
theorem disj_intro_left : ∀ A B, A ⊨ₑ (A ⋁ B) := by
  intro A B
  -- unfold the definition of exact_entails to set set-inclusion
  unfold exact_entails exact_entails_by
  -- Need to show: tm_set A ⊆ tm_set (A ⋁ B)
  intro s hs
  -- s ∈ tm_set A, so s ⊩ A
  -- simp only tactic simplifies using only the specified lemma
  simp only [tm_set, Set.mem_setOf_eq] at hs ⊢
  -- Need to show: s ⊩ (A ⋁ B)
  rw [tm_disj]
  -- tm_disj says: s ⊩ (A ⋁ B) ↔ s ⊩ A ∨ s ⊩ B
  left
  exact hs
