-- Extensions/ConjunctiveParthood.lean
-- Conjunctive parthood relation between sets of states
-- P ≤ Q when P subserves Q and Q subsumes P

import Core.Basic
import Core.Axioms

open Formula


-- SUBSERVES AND SUBSUMES

-- P subserves Q: each state in P is part of some state in Q
def subserves (P Q : Set State) : Prop :=
  ∀ s ∈ P, ∃ u ∈ Q, s ⊑ u

-- Q subsumes P: each state in Q has a part in P
def subsumes (Q P : Set State) : Prop :=
  ∀ s ∈ Q, ∃ u ∈ P, u ⊑ s


-- CONJUNCTIVE PARTHOOD

-- Conjunctive parthood: P ≤ Q iff P subserves Q and Q subsumes P
def conj_parthood (P Q : Set State) : Prop :=
  subserves P Q ∧ subsumes Q P

-- Notation: P ≤ₛ Q for conjunctive parthood (subscript s for "set")
infix:50 " ≤ₛ " => conj_parthood

-- Alternative: Q contains P when P ≤ Q
def contains (Q P : Set State) : Prop := conj_parthood P Q


-- BASIC PROPERTIES

-- Reflexivity: P ≤ₛ P
theorem conj_parthood_refl : ∀ P, P ≤ₛ P := by
  intro P
  constructor
  · -- subserves P P
    intro s hs
    exact ⟨s, hs, parthood_refl s⟩
  · -- subsumes P P
    intro s hs
    exact ⟨s, hs, parthood_refl s⟩

-- Transitivity: P ≤ₛ Q → Q ≤ₛ R → P ≤ₛ R
theorem conj_parthood_trans : ∀ P Q R,
  P ≤ₛ Q → Q ≤ₛ R → P ≤ₛ R := by
  intro P Q R ⟨hPQ_sub, hPQ_sup⟩ ⟨hQR_sub, hQR_sup⟩
  constructor
  · -- subserves P R
    intro s hs
    obtain ⟨t, ht, hst⟩ := hPQ_sub s hs
    obtain ⟨u, hu, htu⟩ := hQR_sub t ht
    exact ⟨u, hu, parthood_trans s t u hst htu⟩
  · -- subsumes R P
    intro s hs
    obtain ⟨t, ht, hts⟩ := hQR_sup s hs
    obtain ⟨u, hu, hut⟩ := hPQ_sup t ht
    exact ⟨u, hu, parthood_trans u t s hut hts⟩


-- PROPERTIES OF SUBSERVES AND SUBSUMES

-- Subserves is reflexive
theorem subserves_refl : ∀ P, subserves P P := by
  intro P s hs
  exact ⟨s, hs, parthood_refl s⟩

-- Subsumes is reflexive
theorem subsumes_refl : ∀ P, subsumes P P := by
  intro P s hs
  exact ⟨s, hs, parthood_refl s⟩

-- Subserves is transitive
theorem subserves_trans : ∀ P Q R,
  subserves P Q → subserves Q R → subserves P R := by
  intro P Q R hPQ hQR s hs
  obtain ⟨t, ht, hst⟩ := hPQ s hs
  obtain ⟨u, hu, htu⟩ := hQR t ht
  exact ⟨u, hu, parthood_trans s t u hst htu⟩

-- Subsumes is transitive
theorem subsumes_trans : ∀ P Q R,
  subsumes P Q → subsumes Q R → subsumes P R := by
  intro P Q R hPQ hQR s hs
  obtain ⟨t, ht, hts⟩ := hPQ s hs
  obtain ⟨u, hu, hut⟩ := hQR t ht
  exact ⟨u, hu, parthood_trans u t s hut hts⟩

