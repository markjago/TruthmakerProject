-- Core/StateSpace.lean
-- State space foundations for truthmaker semantics
-- Defines the primitive parthood ordering and lub operation

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

-- States are the primitive objects
axiom State : Type

-- Parthood relation: s ⊑ t means s is part of t
axiom parthood : State → State → Prop

-- Notation for parthood
infix:50 " ⊑ " => parthood


-- LEAST UPPER BOUND

-- Least upper bound operation on sets of states
-- This is total: every set has a lub
axiom lub : Set State → State

-- Notation for lub
prefix:max "⨆ " => lub


-- PARTHOOD AXIOMS (partial order)

-- Reflexivity: every state is part of itself
axiom parthood_refl : ∀ s, s ⊑ s

-- Transitivity: parthood chains
axiom parthood_trans : ∀ s t u, s ⊑ t → t ⊑ u → s ⊑ u

-- Antisymmetry: mutual parthood implies identity
axiom parthood_antisymm : ∀ s t, s ⊑ t → t ⊑ s → s = t


-- LUB AXIOMS (connecting lub to parthood)

-- lub is an upper bound: every element of T is part of ⨆ T
axiom lub_upper_bound : ∀ (T : Set State) (t : State), t ∈ T → t ⊑ ⨆ T

-- lub is the LEAST upper bound: if s is an upper bound of T, then ⨆ T ⊑ s
axiom lub_least : ∀ (T : Set State) (s : State), (∀ t ∈ T, t ⊑ s) → ⨆ T ⊑ s


-- DERIVED DEFINITIONS

-- Null state: the lub of the empty set (least element)
noncomputable def null_state : State := ⨆ (∅ : Set State)

-- Notation for null state
notation "□" => null_state

-- Full state: the lub of all states (greatest element)
noncomputable def full_state : State := ⨆ (Set.univ : Set State)

-- Notation for full state
notation "■" => full_state

-- Pairwise fusion: lub of a two-element set
noncomputable def fusion (s t : State) : State := ⨆ ({s, t} : Set State)

-- Notation for fusion
infixl:65 " ⊔ " => fusion

-- Greatest lower bound: lub of all lower bounds
noncomputable def glb (T : Set State) : State := ⨆ {s : State | ∀ t ∈ T, s ⊑ t}

-- Notation for glb
prefix:max "⨅ " => glb

-- Pairwise meet: glb of a two-element set
noncomputable def meet (s t : State) : State := ⨅ ({s, t} : Set State)

-- Notation for meet
infixl:70 " ⊓ " => meet
