-- Extensions/NullState.lean
-- Properties of the null state and placeholder for modal extensions
-- Import this only when you need these features

import Core.Basic
import Core.Axioms

open Formula


-- NULL STATE PROPERTIES

-- The null state is part of every state
theorem null_part_of_all : ∀ s, □ ⊑ s := by
  intro s
  -- □ = ⨆ ∅, and by lub_least, ⨆ ∅ ⊑ s since there are no elements to check
  unfold null_state
  apply lub_least
  intro t ht
  simp only [Set.mem_empty_iff_false] at ht

-- The null state is the least element
theorem null_least : ∀ s, s ⊑ □ → s = □ := by
  intro s h
  apply parthood_antisymm
  · exact h
  · exact null_part_of_all s


-- TODO: Modal Extensions to Implement
--
-- 1. Possible States
--    - Define which states are "possible" vs "impossible"
--    - Possible states: those compatible with some coherent scenario
--
-- 2. Impossible States
--    - States that cannot obtain (e.g., truthmake contradictions)
--    - Relationship to the null state (which is part of every state)
--    - Note: impossible states are distinct from the null state
--
-- 3. Downward Closure Conditions
--    - If s truthmakes A and t is part of s, does t truthmake A?
--    - Different closure conditions for different formula types
--    - Relationship between exact and inexact truthmaking

-- Placeholder definitions can be added here as the theory develops
