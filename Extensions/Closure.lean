-- Extensions/Closure.lean
-- Closure predicates and operators for sets of states
-- Closed, convex, and regular sets

import Core.Basic
import Core.Axioms
import Mathlib.Data.Set.Lattice

open Formula


-- CLOSURE PREDICATES

-- A set P is closed iff it is closed under arbitrary lubs
-- i.e., for any nonempty subset Q ⊆ P, the lub of Q is also in P
def is_closed (P : Set State) : Prop :=
  ∀ Q : Set State, Q ⊆ P → Q.Nonempty → lub Q ∈ P

-- A set P is convex iff it is closed under "betweenness"
-- i.e., if s ⊑ t ⊑ u and s, u ∈ P, then t ∈ P
def is_convex (P : Set State) : Prop :=
  ∀ s t u, s ∈ P → u ∈ P → s ⊑ t → t ⊑ u → t ∈ P

-- A set P is regular iff it is both closed and convex
def is_regular (P : Set State) : Prop :=
  is_closed P ∧ is_convex P


-- CLOSURE OPERATORS

-- Closure of P: the intersection of all closed sets containing P
-- This is the smallest closed set containing P
noncomputable def closure (P : Set State) : Set State :=
  ⋂₀ { Q : Set State | P ⊆ Q ∧ is_closed Q }

-- Convex closure of P: the intersection of all convex sets containing P
-- This is the smallest convex set containing P
noncomputable def convex_closure (P : Set State) : Set State :=
  ⋂₀ { Q : Set State | P ⊆ Q ∧ is_convex Q }

-- Regular closure of P: the intersection of all regular sets containing P
-- This is the smallest regular set containing P
noncomputable def regular_closure (P : Set State) : Set State :=
  ⋂₀ { Q : Set State | P ⊆ Q ∧ is_regular Q }


-- BASIC CLOSURE PROPERTIES

-- P is a subset of its closure
theorem subset_closure : ∀ P, P ⊆ closure P := by
  intro P s hs
  simp only [closure, Set.mem_sInter, Set.mem_setOf_eq]
  intro Q ⟨hPQ, _⟩
  exact hPQ hs

-- P is a subset of its convex closure
theorem subset_convex_closure : ∀ P, P ⊆ convex_closure P := by
  intro P s hs
  simp only [convex_closure, Set.mem_sInter, Set.mem_setOf_eq]
  intro Q ⟨hPQ, _⟩
  exact hPQ hs

-- P is a subset of its regular closure
theorem subset_regular_closure : ∀ P, P ⊆ regular_closure P := by
  intro P s hs
  simp only [regular_closure, Set.mem_sInter, Set.mem_setOf_eq]
  intro Q ⟨hPQ, _⟩
  exact hPQ hs

-- The closure of P is closed
theorem closure_is_closed : ∀ P, is_closed (closure P) := by
  sorry

-- The convex closure of P is convex
theorem convex_closure_is_convex : ∀ P, is_convex (convex_closure P) := by
  sorry

-- The regular closure of P is regular
theorem regular_closure_is_regular : ∀ P, is_regular (regular_closure P) := by
  sorry


-- MONOTONICITY

-- Closure is monotonic: if P ⊆ Q then closure P ⊆ closure Q
theorem closure_mono : ∀ P Q, P ⊆ Q → closure P ⊆ closure Q := by
  intro P Q hPQ s hs
  simp only [closure, Set.mem_sInter, Set.mem_setOf_eq] at hs ⊢
  intro R ⟨hQR, hclosed⟩
  apply hs
  exact ⟨Set.Subset.trans hPQ hQR, hclosed⟩

-- Convex closure is monotonic
theorem convex_closure_mono : ∀ P Q, P ⊆ Q → convex_closure P ⊆ convex_closure Q := by
  intro P Q hPQ s hs
  simp only [convex_closure, Set.mem_sInter, Set.mem_setOf_eq] at hs ⊢
  intro R ⟨hQR, hconvex⟩
  apply hs
  exact ⟨Set.Subset.trans hPQ hQR, hconvex⟩

-- Regular closure is monotonic
theorem regular_closure_mono : ∀ P Q, P ⊆ Q → regular_closure P ⊆ regular_closure Q := by
  intro P Q hPQ s hs
  simp only [regular_closure, Set.mem_sInter, Set.mem_setOf_eq] at hs ⊢
  intro R ⟨hQR, hregular⟩
  apply hs
  exact ⟨Set.Subset.trans hPQ hQR, hregular⟩


-- IDEMPOTENCE

-- Closure is idempotent: closure (closure P) = closure P
theorem closure_idemp : ∀ P, closure (closure P) = closure P := by
  sorry

-- Convex closure is idempotent: convex_closure (convex_closure P) = convex_closure P
theorem convex_closure_idemp : ∀ P, convex_closure (convex_closure P) = convex_closure P := by
  sorry

-- Regular closure is idempotent: regular_closure (regular_closure P) = regular_closure P
theorem regular_closure_idemp : ∀ P, regular_closure (regular_closure P) = regular_closure P := by
  sorry

