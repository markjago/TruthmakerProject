-- Extensions/CanonicalModel.lean
-- The canonical model for truthmaker semantics
-- States are sets of literals, parthood is subset inclusion

import Core.Basic
import Core.Axioms
import Mathlib.Data.Set.Basic

open Formula


-- LITERALS (as a separate type for the canonical model)

-- A Literal is either p or ¬p for some propositional variable
inductive Literal : Type where
  | pos : PropVar → Literal  -- positive literal p
  | neg : PropVar → Literal  -- negative literal ¬p

-- Convert a Literal to a Formula
def Literal.toFormula : Literal → Formula
  | Literal.pos p => Formula.atom p
  | Literal.neg p => Formula.neg (Formula.atom p)


-- CANONICAL STATES

-- Canonical states are sets of literals
-- We use Set Literal directly to get all the set operations
abbrev CanonicalState := Set Literal

-- The empty set of literals (canonical null state)
def canonical_null : CanonicalState := ∅


-- CANONICAL PARTHOOD

-- Canonical parthood is subset inclusion
def canonical_parthood (s t : CanonicalState) : Prop := s ⊆ t

-- Notation for canonical parthood
infix:50 " ⊑ᶜ " => canonical_parthood


-- CANONICAL VALUATIONS

-- Canonical positive valuation: |p|⁺ = {{p}}
-- The only state that truthmakes p is the singleton {p}
def canonical_val_pos (p : PropVar) : Set CanonicalState :=
  { ({Literal.pos p} : Set Literal) }

-- Canonical negative valuation: |p|⁻ = {{¬p}}
-- The only state that falsitymakes p is the singleton {¬p}
def canonical_val_neg (p : PropVar) : Set CanonicalState :=
  { ({Literal.neg p} : Set Literal) }


-- CANONICAL MODEL STRUCTURE

-- The canonical model bundles all components together
structure CanonicalModel where
  states : Type := CanonicalState
  parthood : CanonicalState → CanonicalState → Prop := canonical_parthood
  null : CanonicalState := canonical_null
  val_pos : PropVar → Set CanonicalState := canonical_val_pos
  val_neg : PropVar → Set CanonicalState := canonical_val_neg


-- CANONICAL PARTHOOD PROPERTIES

-- Canonical parthood is reflexive
theorem canonical_parthood_refl : ∀ s : CanonicalState, s ⊑ᶜ s := by
  intro s
  unfold canonical_parthood
  exact Set.Subset.refl s

-- Canonical parthood is transitive
theorem canonical_parthood_trans : ∀ s t u : CanonicalState,
  s ⊑ᶜ t → t ⊑ᶜ u → s ⊑ᶜ u := by
  intro s t u hst htu
  unfold canonical_parthood at *
  exact Set.Subset.trans hst htu

-- Canonical parthood is antisymmetric
theorem canonical_parthood_antisymm : ∀ s t : CanonicalState,
  s ⊑ᶜ t → t ⊑ᶜ s → s = t := by
  intro s t hst hts
  unfold canonical_parthood at *
  exact Set.Subset.antisymm hst hts


-- CANONICAL FUSION

-- Canonical fusion is set union
def canonical_fusion (s t : CanonicalState) : CanonicalState := s ∪ t

-- Notation for canonical fusion
infixl:65 " ⊔ᶜ " => canonical_fusion

-- Fusion is an upper bound
theorem canonical_fusion_upper_left : ∀ s t : CanonicalState, s ⊑ᶜ (s ⊔ᶜ t) := by
  intro s t
  unfold canonical_parthood canonical_fusion
  exact Set.subset_union_left

theorem canonical_fusion_upper_right : ∀ s t : CanonicalState, t ⊑ᶜ (s ⊔ᶜ t) := by
  intro s t
  unfold canonical_parthood canonical_fusion
  exact Set.subset_union_right

-- Fusion is commutative
theorem canonical_fusion_comm : ∀ s t : CanonicalState, s ⊔ᶜ t = t ⊔ᶜ s := by
  intro s t
  unfold canonical_fusion
  exact Set.union_comm s t


-- CANONICAL NULL STATE PROPERTIES

-- The canonical null state is part of every state
theorem canonical_null_part_of_all : ∀ s : CanonicalState, canonical_null ⊑ᶜ s := by
  intro s
  unfold canonical_parthood canonical_null
  exact Set.empty_subset s

-- Fusion with null is identity
theorem canonical_fusion_null_left : ∀ s : CanonicalState, canonical_null ⊔ᶜ s = s := by
  intro s
  unfold canonical_fusion canonical_null
  exact Set.empty_union s

theorem canonical_fusion_null_right : ∀ s : CanonicalState, s ⊔ᶜ canonical_null = s := by
  intro s
  unfold canonical_fusion canonical_null
  exact Set.union_empty s

