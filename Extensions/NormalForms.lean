-- Extensions/NormalForms.lean
-- Literals, normal forms (DNF/CNF), and standard normal forms
-- Standard forms use an arbitrary total order on formulas for uniqueness

import Core.Basic
import Core.Axioms

open Formula


-- LITERALS

-- A formula is a positive literal (an atom)
def is_pos_literal : Formula → Prop
  | atom _ => True
  | _ => False

-- A formula is a negative literal (negated atom)
def is_neg_literal : Formula → Prop
  | neg (atom _) => True
  | _ => False

-- A formula is a literal (positive or negative)
def is_literal (A : Formula) : Prop :=
  is_pos_literal A ∨ is_neg_literal A


-- LIST CONJUNCTION AND DISJUNCTION

-- Conjunction of a list of formulas (⊤ for empty list)
def conj_list : List Formula → Formula
  | [] => ⊤
  | [A] => A
  | A :: As => A ⋀ conj_list As

-- Disjunction of a list of formulas (⊥ for empty list)
def disj_list : List Formula → Formula
  | [] => ⊥
  | [A] => A
  | A :: As => A ⋁ disj_list As


-- CONJUNCTIONS AND DISJUNCTIONS OF LITERALS

-- A formula is a conjunction of literals (including ⊤ for empty conjunction)
inductive is_conj_of_literals : Formula → Prop where
  | lit : is_literal A → is_conj_of_literals A
  | top : is_conj_of_literals ⊤
  | conj : is_conj_of_literals A → is_conj_of_literals B →
           is_conj_of_literals (A ⋀ B)

-- A formula is a disjunction of literals (including ⊥ for empty disjunction)
inductive is_disj_of_literals : Formula → Prop where
  | lit : is_literal A → is_disj_of_literals A
  | bot : is_disj_of_literals ⊥
  | disj : is_disj_of_literals A → is_disj_of_literals B →
           is_disj_of_literals (A ⋁ B)


-- DISJUNCTIVE AND CONJUNCTIVE NORMAL FORMS

-- DNF: disjunction of conjunctions of literals
inductive is_DNF : Formula → Prop where
  | conj : is_conj_of_literals A → is_DNF A
  | bot : is_DNF ⊥
  | disj : is_DNF A → is_DNF B → is_DNF (A ⋁ B)

-- CNF: conjunction of disjunctions of literals
inductive is_CNF : Formula → Prop where
  | disj : is_disj_of_literals A → is_CNF A
  | top : is_CNF ⊤
  | conj : is_CNF A → is_CNF B → is_CNF (A ⋀ B)


-- TOTAL ORDER ON FORMULAS (for standard forms)

-- Axiomatize a total order on Formula
axiom formula_le : Formula → Formula → Prop
axiom formula_le_refl : ∀ A, formula_le A A
axiom formula_le_trans : ∀ A B C, formula_le A B → formula_le B C → formula_le A C
axiom formula_le_antisymm : ∀ A B, formula_le A B → formula_le B A → A = B
axiom formula_le_total : ∀ A B, formula_le A B ∨ formula_le B A

-- Notation: A ≤ᶠ B (subscript f for "formula")
infix:50 " ≤ᶠ " => formula_le


-- SORTED CONJUNCTIONS AND DISJUNCTIONS

-- A conjunction is sorted if conjuncts are in non-decreasing order
inductive is_sorted_conj : Formula → Prop where
  | single : is_sorted_conj A
  | conj : A ≤ᶠ B → is_sorted_conj B → is_sorted_conj (A ⋀ B)

-- A disjunction is sorted if disjuncts are in non-decreasing order
inductive is_sorted_disj : Formula → Prop where
  | single : is_sorted_disj A
  | disj : A ≤ᶠ B → is_sorted_disj B → is_sorted_disj (A ⋁ B)


-- IMMEDIATE CONJUNCTS AND DISJUNCTS

-- B is an immediate disjunct of A (top-level disjunct in a disjunction)
def is_immediate_disjunct : Formula → Formula → Prop
  | B, disj C D => B = C ∨ is_immediate_disjunct B D
  | B, A => B = A  -- For non-disjunctions, the formula is its own sole disjunct

-- B is an immediate conjunct of A (top-level conjunct in a conjunction)
def is_immediate_conjunct : Formula → Formula → Prop
  | B, conj C D => B = C ∨ is_immediate_conjunct B D
  | B, A => B = A  -- For non-conjunctions, the formula is its own sole conjunct


-- STANDARD NORMAL FORMS (unique representatives)

-- Standard DNF: DNF with sorted structure at both levels
-- Each conjunction of literals is sorted, and the disjuncts are sorted
def is_standard_DNF (A : Formula) : Prop :=
  is_DNF A ∧ is_sorted_disj A ∧
  (∀ B, is_immediate_disjunct B A → is_sorted_conj B)

-- Standard CNF: CNF with sorted structure at both levels
-- Each disjunction of literals is sorted, and the conjuncts are sorted
def is_standard_CNF (A : Formula) : Prop :=
  is_CNF A ∧ is_sorted_conj A ∧
  (∀ B, is_immediate_conjunct B A → is_sorted_disj B)


-- BASIC THEOREMS

-- Every literal is a conjunction of literals
theorem literal_is_conj_of_literals : ∀ A,
  is_literal A → is_conj_of_literals A := by
  intro A h
  exact is_conj_of_literals.lit h

-- Every literal is a disjunction of literals
theorem literal_is_disj_of_literals : ∀ A,
  is_literal A → is_disj_of_literals A := by
  intro A h
  exact is_disj_of_literals.lit h

-- Every conjunction of literals is a DNF
theorem conj_of_literals_is_DNF : ∀ A,
  is_conj_of_literals A → is_DNF A := by
  intro A h
  exact is_DNF.conj h

-- Every disjunction of literals is a CNF
theorem disj_of_literals_is_CNF : ∀ A,
  is_disj_of_literals A → is_CNF A := by
  intro A h
  exact is_CNF.disj h


-- NORMAL FORM FUNCTIONS

-- toDNF asserts the existence of a standard DNF equivalent to A.
-- It does not compute the DNF; rather, it axiomatically provides a choice of
-- standard DNF for each formula, with the two correctness properties below.
axiom toDNF : Formula → Formula

-- toDNF(A) is in standard DNF
axiom toDNF_is_dnf : ∀ A, is_standard_DNF (toDNF A)

-- toDNF(A) has the same truthmakers as A
axiom toDNF_equiv : ∀ A s, (s ⊩ toDNF A) ↔ (s ⊩ A)

-- Similarly for CNF
axiom toCNF : Formula → Formula

-- toCNF(A) is in standard CNF
axiom toCNF_is_cnf : ∀ A, is_standard_CNF (toCNF A)

-- toCNF(A) has the same truthmakers as A
axiom toCNF_equiv : ∀ A s, (s ⊩ toCNF A) ↔ (s ⊩ A)


-- UNIQUENESS THEOREM (to prove)

-- For any formula A, its standard DNF is unique (if it exists)
theorem standard_DNF_unique : ∀ A B C,
  is_standard_DNF B → is_standard_DNF C →
  (∀ s, s ⊩ A ↔ s ⊩ B) → (∀ s, s ⊩ A ↔ s ⊩ C) →
  B = C := by
  sorry

-- For any formula A, its standard CNF is unique (if it exists)
theorem standard_CNF_unique : ∀ A B C,
  is_standard_CNF B → is_standard_CNF C →
  (∀ s, s ⊩ A ↔ s ⊩ B) → (∀ s, s ⊩ A ↔ s ⊩ C) →
  B = C := by
  sorry

