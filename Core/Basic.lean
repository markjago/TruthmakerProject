-- Core/Basic.lean
-- Fundamental definitions for truthmaker semantics
-- These are the minimal primitives that everything else builds on

import Core.StateSpace

-- Propositional variables (atoms)
axiom PropVar : Type

-- Valuations: assign sets of states to propositional variables
-- V⁺(p) = states that truthmake p
-- V⁻(p) = states that falsitymake p
axiom val_pos : PropVar → Set State
axiom val_neg : PropVar → Set State

-- Notation for valuations
notation "V⁺" => val_pos
notation "V⁻" => val_neg

-- Formula language
inductive Formula : Type where
  | atom : PropVar → Formula
  | top : Formula                       -- verum (⊤)
  | bot : Formula                       -- falsum (⊥)
  | conj : Formula → Formula → Formula  -- conjunction
  | disj : Formula → Formula → Formula  -- disjunction
  | neg : Formula → Formula             -- negation

-- Open the Formula namespace for convenience
open Formula

-- Notation for formulas (use different symbols to avoid conflict with Prop)
notation "⊤" => Formula.top       -- \top
notation "⊥" => Formula.bot       -- \bot
infixl:50 " ⋀ " => Formula.conj   -- \And or \bigwedge
infixl:40 " ⋁ " => Formula.disj   -- \Or or \bigvee

-- Primary negation notation: ∼ (\sim) - unambiguous, no conflict with Prop
prefix:75 "∼" => Formula.neg      -- \sim (recommended)

-- Alternative notations for convenience:
prefix:75 "~" => Formula.neg      -- ASCII tilde (easy to type)

-- Exact truthmaking relation
axiom truthmakes : State → Formula → Prop

-- Notation for truthmaking: ⊩ (\Vdash)
infix:50 " ⊩ " => truthmakes

-- Exact falsitymaking relation
axiom falsitymakes : State → Formula → Prop

-- Notation for falsitymaking: ⫣ (\dashV or similar)
infix:50 " ⫣ " => falsitymakes
