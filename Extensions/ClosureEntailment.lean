-- Extensions/ClosureEntailment.lean
-- Entailment and equivalence relations using closed, convex, and regular content
-- Instantiates the abstract framework from Core.Entailment with closure operators
-- "Exact" variants are unilateral (truthmakers only); "full" variants are bilateral
-- (truthmakers and falsitymakers). See Core.Entailment for full terminology notes.

import Core.Entailment
import Extensions.Closure

open Formula


/- CLOSED CONTENT ENTAILMENTS -/

-- Exact entailment using closed truthmaker sets
def exact_entails_cl : Formula → Formula → Prop :=
  exact_entails_by (fun A => closure (tm_set A))

-- Full entailment using closed truthmaker and falsitymaker sets
def full_entails_cl : Formula → Formula → Prop :=
  full_entails_by (fun A => closure (tm_set A)) (fun A => closure (fm_set A))

-- Equivalence relations for closed content
def exact_equiv_cl (A B : Formula) : Prop :=
  exact_entails_cl A B ∧ exact_entails_cl B A

def full_equiv_cl (A B : Formula) : Prop :=
  full_entails_cl A B ∧ full_entails_cl B A

-- Notation (subscript for exact/full, superscript for closure type)
infix:50 " ⊨ₑᶜˡ " => exact_entails_cl   -- \|= \e ^cl
infix:50 " ⊨ᶠᶜˡ " => full_entails_cl    -- \|= \f ^cl
infix:50 " ≡ₑᶜˡ " => exact_equiv_cl    -- \equiv \e ^cl
infix:50 " ≡ᶠᶜˡ " => full_equiv_cl     -- \equiv \f ^cl


/- CONVEX CONTENT ENTAILMENTS -/

-- Exact entailment using convex truthmaker sets
def exact_entails_cv : Formula → Formula → Prop :=
  exact_entails_by (fun A => convex_closure (tm_set A))

-- Full entailment using convex truthmaker and falsitymaker sets
def full_entails_cv : Formula → Formula → Prop :=
  full_entails_by (fun A => convex_closure (tm_set A)) (fun A => convex_closure (fm_set A))

-- Equivalence relations for convex content
def exact_equiv_cv (A B : Formula) : Prop :=
  exact_entails_cv A B ∧ exact_entails_cv B A

def full_equiv_cv (A B : Formula) : Prop :=
  full_entails_cv A B ∧ full_entails_cv B A

-- Notation (subscript for exact/full, superscript for closure type)
infix:50 " ⊨ₑᶜᵛ " => exact_entails_cv   -- \|= \e ^cv
infix:50 " ⊨ᶠᶜᵛ " => full_entails_cv    -- \|= \f ^cv
infix:50 " ≡ₑᶜᵛ " => exact_equiv_cv    -- \equiv \e ^cv
infix:50 " ≡ᶠᶜᵛ " => full_equiv_cv     -- \equiv \f ^cv


/- REGULAR CONTENT ENTAILMENTS -/

-- Exact entailment using regular (closed and convex) truthmaker sets
def exact_entails_reg : Formula → Formula → Prop :=
  exact_entails_by (fun A => regular_closure (tm_set A))

-- Full entailment using regular truthmaker and falsitymaker sets
def full_entails_reg : Formula → Formula → Prop :=
  full_entails_by (fun A => regular_closure (tm_set A)) (fun A => regular_closure (fm_set A))

-- Equivalence relations for regular content
def exact_equiv_reg (A B : Formula) : Prop :=
  exact_entails_reg A B ∧ exact_entails_reg B A

def full_equiv_reg (A B : Formula) : Prop :=
  full_entails_reg A B ∧ full_entails_reg B A

-- Notation (subscript for exact/full, superscript for closure type)
infix:50 " ⊨ₑʳᵉᵍ " => exact_entails_reg   -- \|= \e ^reg
infix:50 " ⊨ᶠʳᵉᵍ " => full_entails_reg    -- \|= \f ^reg
infix:50 " ≡ₑʳᵉᵍ " => exact_equiv_reg    -- \equiv \e ^reg
infix:50 " ≡ᶠʳᵉᵍ " => full_equiv_reg     -- \equiv \f ^reg


/- RELATIONSHIPS BETWEEN VARIANTS -/

-- Note: The hierarchy of closure operators suggests possible relationships:
--   Raw ⊆ Closed, Convex (incomparable), Regular = Closed ∩ Convex
-- These relationships may lead to implications between entailment notions,
-- but such theorems depend on properties of the closure operators and
-- will be explored in future work.

-- Example theorem stub: raw exact entailment implies closed exact entailment
-- theorem raw_implies_closed : ∀ A B, exact_entails A B → exact_entails_cl A B := by
--   intro A B h
--   unfold exact_entails exact_entails_cl exact_entails_by
--   -- Would need: tm_set A ⊆ tm_set B implies closure (tm_set A) ⊆ closure (tm_set B)
--   -- This follows from monotonicity of closure (closure_mono in Extensions.Closure)
--   sorry
