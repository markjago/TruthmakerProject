-- Core/Axioms.lean
-- Axioms for exact truthmaking and falsitymaking
-- Fusion properties are now theorems (proved in Theorems.lean)

import Core.Basic

open Formula


-- TRUTHMAKING AXIOMS

-- Atoms: s truthmakes p iff s is in the positive valuation of p
axiom tm_atom : ∀ s p,
  (s ⊩ (atom p)) ↔ s ∈ V⁺ p

-- Top (⊤): only the null state truthmakes top
axiom tm_top : ∀ s,
  (s ⊩ ⊤) ↔ s = □

-- Bottom (⊥): nothing truthmakes bottom
axiom tm_bot : ∀ s,
  ¬(s ⊩ ⊥)

-- Negation: s truthmakes ∼A iff s falsitymakes A
axiom tm_neg : ∀ s A,
  (s ⊩ (∼A)) ↔ (s ⫣ A)

-- Conjunction: s truthmakes A ⋀ B iff s is the fusion of parts truthmaking A and B
axiom tm_conj : ∀ s A B,
  (s ⊩ (A ⋀ B)) ↔ (∃ t u, s = t ⊔ u ∧ (t ⊩ A) ∧ (u ⊩ B))

-- Disjunction: s truthmakes A ⋁ B iff s truthmakes A or s truthmakes B
axiom tm_disj : ∀ s A B,
  (s ⊩ (A ⋁ B)) ↔ ((s ⊩ A) ∨ (s ⊩ B))


-- FALSITYMAKING AXIOMS

-- Atoms: s falsitymakes p iff s is in the negative valuation of p
axiom fm_atom : ∀ s p,
  (s ⫣ (atom p)) ↔ s ∈ V⁻ p

-- Top (⊤): nothing falsitymakes top
axiom fm_top : ∀ s,
  ¬(s ⫣ ⊤)

-- Bottom (⊥): only the null state falsitymakes bottom
axiom fm_bot : ∀ s,
  (s ⫣ ⊥) ↔ s = □

-- Negation: s falsitymakes ∼A iff s truthmakes A
axiom fm_neg : ∀ s A,
  (s ⫣ (∼A)) ↔ (s ⊩ A)

-- Conjunction: s falsitymakes A ⋀ B iff s falsitymakes A or s falsitymakes B
axiom fm_conj : ∀ s A B,
  (s ⫣ (A ⋀ B)) ↔ ((s ⫣ A) ∨ (s ⫣ B))

-- Disjunction: s falsitymakes A ⋁ B iff s is the fusion of parts falsitymaking A and B
axiom fm_disj : ∀ s A B,
  (s ⫣ (A ⋁ B)) ↔ (∃ t u, s = t ⊔ u ∧ (t ⫣ A) ∧ (u ⫣ B))
