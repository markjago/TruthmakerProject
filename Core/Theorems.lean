-- Core/Theorems.lean
-- Theorems that follow from the state space and truthmaking axioms
-- Fusion properties are now provable from lub axioms

import Core.Basic
import Core.Axioms

open Formula


-- FUSION THEOREMS (derived from lub axioms)

-- Fusion is commutative: s ⊔ t = t ⊔ s
-- Proof sketch: {s, t} = {t, s} as sets, so their lubs are equal
theorem fusion_comm : ∀ s t, s ⊔ t = t ⊔ s := by
  sorry

-- Fusion is idempotent: s ⊔ s = s
-- Proof sketch: {s, s} = {s}, and lub of singleton equals the element
theorem fusion_idemp : ∀ s, s ⊔ s = s := by
  sorry

-- Fusion is associative: (s ⊔ t) ⊔ u = s ⊔ (t ⊔ u)
-- Proof sketch: both equal ⨆ {s, t, u}
theorem fusion_assoc : ∀ s t u, (s ⊔ t) ⊔ u = s ⊔ (t ⊔ u) := by
  sorry

-- Null state is left identity for fusion: □ ⊔ s = s
-- Proof sketch: □ = ⨆ ∅ is part of everything, so doesn't add to the lub
theorem fusion_null_left : ∀ s, □ ⊔ s = s := by
  sorry

-- Null state is right identity for fusion: s ⊔ □ = s
theorem fusion_null_right : ∀ s, s ⊔ □ = s := by
  intro s
  rw [fusion_comm]
  exact fusion_null_left s

-- Parthood characterization via fusion: s ⊑ t iff s ⊔ t = t
theorem parthood_iff_fusion : ∀ s t, s ⊑ t ↔ s ⊔ t = t := by
  sorry


-- TRUTHMAKING THEOREMS

-- Conjunction is commutative (with respect to truthmaking)
-- Proof: if s ⊩ A ⋀ B, then s = t ⊔ u with t ⊩ A and u ⊩ B
-- By fusion commutativity, s = u ⊔ t, so s ⊩ B ⋀ A
theorem conj_tm_comm : ∀ s A B,
  (s ⊩ (A ⋀ B)) → (s ⊩ (B ⋀ A)) := by
  intro s A B h
  rw [tm_conj] at h ⊢
  obtain ⟨t, u, heq, ht, hu⟩ := h
  exact ⟨u, t, by rw [fusion_comm]; exact heq, hu, ht⟩

-- Double negation for truthmaking
-- s ⊩ ∼∼A iff s ⫣ ∼A iff s ⊩ A
theorem double_neg_tm : ∀ s A,
  (s ⊩ (∼(∼A))) ↔ (s ⊩ A) := by
  intro s A
  rw [tm_neg, fm_neg]
