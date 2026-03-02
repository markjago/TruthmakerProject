# TruthmakerProject — Notes

A Lean 4 / Mathlib formalisation of **exact truthmaker semantics** (in the style of Kit Fine).

---

## Structure

```
Core/          — primitive definitions and axioms
Extensions/    — derived concepts and closure operators
Problems/      — open problems and conjectures
Experiments/   — scratch space
```

---

## Core

### `Core/StateSpace.lean`
The ground-level ontology.

- **`State`** — axiomatic type of states.
- **`parthood : State → State → Prop`** (`⊑`) — partial order (reflexivity, transitivity, antisymmetry axiomatised).
- **`lub : Set State → State`** (`⨆`) — total least-upper-bound operation (upper-bound and least-upper-bound axioms).
- Derived: `null_state` (`□` = `⨆ ∅`), `full_state` (`■` = `⨆ Set.univ`), `fusion` (`s ⊔ t` = `⨆ {s, t}`), `glb`/`meet`.

### `Core/Basic.lean`
The semantic language.

- **`PropVar`** — axiomatic type of propositional variables.
- **`val_pos / val_neg : PropVar → Set State`** (`V⁺` / `V⁻`) — positive and negative valuations.
- **`Formula`** — inductive type: `atom`, `⊤`, `⊥`, `⋀`, `⋁`, `∼`.
- **`truthmakes : State → Formula → Prop`** (`s ⊩ A`) and **`falsitymakes`** (`s ⫣ A`) — axiomatic exact relations.

### `Core/Axioms.lean`
Recursive clauses for `⊩` and `⫣`:

| Connective | Truthmaking | Falsitymaking |
|---|---|---|
| atom `p` | `s ∈ V⁺ p` | `s ∈ V⁻ p` |
| `⊤` | `s = □` | ⊥ (nothing) |
| `⊥` | ⊥ (nothing) | `s = □` |
| `∼A` | `s ⫣ A` | `s ⊩ A` |
| `A ⋀ B` | `∃ t u, s = t ⊔ u ∧ t ⊩ A ∧ u ⊩ B` | `s ⫣ A ∨ s ⫣ B` |
| `A ⋁ B` | `s ⊩ A ∨ s ⊩ B` | `∃ t u, s = t ⊔ u ∧ t ⫣ A ∧ u ⫣ B` |

### `Core/Theorems.lean`
Theorems derived from the axioms. Several are proved; several carry `sorry`:

- `fusion_comm`, `fusion_idemp`, `fusion_assoc`, `fusion_null_left/right` — **sorry** (sketches given).
- `parthood_iff_fusion` — **sorry**.
- `conj_tm_comm` — **proved** (uses `fusion_comm`).
- `double_neg_tm` — **proved**.

### `Core/Entailment.lean`
Abstract entailment framework parameterised by content functions.

**Terminology**: *exact* means **unilateral** (truthmakers only); *full* means **bilateral** (both truthmakers and falsitymakers).

- `exact_entails_by content A B` ≔ `content A ⊆ content B`. (unilateral)
- `full_entails_by pos neg A B` ≔ `pos A ⊆ pos B ∧ neg B ⊆ neg A`. (bilateral)
- Concrete instances `exact_entails` (`⊨ₑ`) and `full_entails` (`⊨ᶠ`) using raw `tm_set`/`fm_set`.
- Equivalences `exact_equiv` (`≡ₑ`) and `full_equiv` (`≡ᶠ`).
- All four relations proved to be preorders (reflexive, transitive); equivalences proved symmetric; `full_implies_exact` proved.

---

## Extensions

### `Extensions/Content.lean`
- `tm_set A` = `{ s | s ⊩ A }`, `fm_set A` = `{ s | s ⫣ A }`.
- `set_fusion T U` (`⊔ₛ`) = pairwise fusions.
- Proved: `tm_set (A ⋀ B) = tm_set A ⊔ₛ tm_set B`, `fm_set (A ⋁ B) = fm_set A ⊔ₛ fm_set B`, union laws for `⋁`/`⋀`, negation swap laws.

### `Extensions/Closure.lean`
Three closure predicates and their operators (all as intersection of all supersets satisfying the predicate):

- `is_closed P` — P closed under arbitrary lubs.
- `is_convex P` — P closed under betweenness.
- `is_regular P` — closed ∧ convex.
- Operators: `closure`, `convex_closure`, `regular_closure`.
- Proved: `P ⊆ closure P` (and convex/regular analogues), monotonicity of all three.
- **Sorry**: `closure_is_closed`, `convex_closure_is_convex`, `regular_closure_is_regular`, all three idempotence theorems.

### `Extensions/ClosureEntailment.lean`
Instantiates the abstract entailment framework three times using closed (`ᶜˡ`), convex (`ᶜᵛ`), and regular (`ʳᵉᵍ`) content. Notations: `⊨ₑᶜˡ`, `⊨ᶠᶜˡ`, etc. "Exact" variants are unilateral; "full" variants are bilateral. No theorems proved yet.

### `Extensions/InexactTruthmaking.lean`
- `inexact_truthmakes s A` (`s ⊩ᵢ A`) ≔ `∃ u ⊑ s, u ⊩ A`; similarly `s ⫣ᵢ A`.
- Proved: exact implies inexact (both directions).
- **Sorry**: `inexact_tm_conj/disj`, `inexact_fm_conj/disj`.

### `Extensions/ConjunctiveParthood.lean`
Order on sets of states: `P ≤ₛ Q` iff `subserves P Q ∧ subsumes Q P`.

- `subserves P Q` — every `s ∈ P` has a part in `Q`.
- `subsumes Q P` — every `s ∈ Q` has a part in `P`.
- Proved: reflexivity and transitivity of `≤ₛ`, `subserves`, `subsumes`.

### `Extensions/NullState.lean`
- Proved: `□ ⊑ s` for all `s` (null is least element), `null_least`.
- Contains a TODO list for future modal extensions (possible/impossible states, downward closure).

### `Extensions/NormalForms.lean`
Predicates and axiomatised functions for DNF/CNF and *standard* (sorted, unique) normal forms.

- Literals, `conj_list`/`disj_list`, `is_conj_of_literals`, `is_DNF`, `is_CNF`.
- Total order on `Formula` axiomatised (`≤ᶠ`); `is_sorted_conj/disj`; `is_standard_DNF/CNF`.
- Proved: four trivial inclusion lemmas.
- **Sorry**: `standard_DNF_unique`, `standard_CNF_unique`.
- **`toDNF : Formula → Formula`** — axiomatised choice function: does not compute the DNF, but asserts that `toDNF A` is a standard DNF formula with the same truthmakers as `A`. Two axioms:
  - `toDNF_is_dnf : ∀ A, is_standard_DNF (toDNF A)`
  - `toDNF_equiv : ∀ A s, (s ⊩ toDNF A) ↔ (s ⊩ A)`
- **`toCNF : Formula → Formula`** — parallel axiomatised choice function for standard CNF, with `toCNF_is_cnf` and `toCNF_equiv`.

### `Extensions/CanonicalModel.lean`
Concrete model where states are sets of literals.

- `Literal` — `pos p` or `neg p`.
- `CanonicalState = Set Literal`; `canonical_parthood` = `⊆`; `canonical_fusion` = `∪`; `canonical_null` = `∅`.
- Atomic valuations: `canonical_val_pos p = { {pos p} }`, `canonical_val_neg p = { {neg p} }`.
- Proved: reflexivity/transitivity/antisymmetry of `⊑ᶜ`, upper-bound properties and commutativity of `⊔ᶜ`, null-state identity laws.
- **Missing**: extension of valuations to complex formulas; proof that the model satisfies the axioms of `Core.Axioms`; proof that `⊔ᶜ` is the *least* upper bound (only the upper bound half is done); completeness/soundness results.

### `Extensions/BilateralEntailment.lean`
Entailment notions for the purely **bilateral** (full), **fusion-closed** system. All content uses `full_equiv_cl` (closed content) throughout, so that `A ⋀ A ≡ A` and `A ⋁ A ≡ A` hold. Within this file (and `Problems/BilateralConjectures.lean`), bare `⊨` means `⊨ᶠᵈ` and bare `≡` means `≡ᶠᵈ`.

- **`full_conj_entails` (`⊨ᶠᶜ`)**: `A ⊨ᶠᶜ B` iff `full_equiv_cl (A ⋀ B) A` — conjoining B adds nothing to A.
- **`full_disj_entails` (`⊨ᶠᵈ`)**: `A ⊨ᶠᵈ B` iff `full_equiv_cl (A ⋁ B) B` — disjoining A adds nothing to B.
- Corresponding equivalences `≡ᶠᶜ`, `≡ᶠᵈ`.
- **Sorry**: reflexivity and transitivity of both (reflexivity depends on `closure_is_closed`).

---

## Problems

### `Problems/EntailmentBasics.lean`
- Proved: `A ⊨ₑ (A ⋁ B)` (disjunction introduction, left).

### `Problems/Conjunction.lean`
- **Sorry**: `conj_dist_disj` and its converse (distribution of `⋀` over `⋁`).

### `Problems/Hyperintensionality.lean`
- Scaffold for conjectures about hyperintensionality (no theorems proved yet).
- Notes the key distinction: exact equivalence (`≡ₑ`) is finer than classical necessary equivalence.

### `Problems/BilateralConjectures.lean`
Conjectures about the bilateral, fusion-closed system. Uses bare `⊨` (`⊨ᶠᵈ`) and `≡` (`≡ᶠᵈ`) throughout.

- **Quasi-distribution (∧)**: `A ⋀ B ⊨ A ⋀ (B ⋁ C)`
- **Quasi-distribution (∨)**: `A ⋁ B ⊨ A ⋁ (B ⋀ C)`
- **Birkhoff**: `A ⋁ (A ⋀ B) ≡ A ⋀ (A ⋁ B)`
- **Monotonicity (∧)**: `A ⊨ B → A ⋀ C ⊨ B ⋀ C`
- **Monotonicity (∨)**: `A ⊨ B → A ⋁ C ⊨ B ⋁ C`
- **Equivalence of schemas**: quasi-distribution (∧) ↔ monotonicity (∧); quasi-distribution (∨) ↔ monotonicity (∨)
- **DNF entails**: `toDNF A ⊨ A`
- **DNF content**: `closure (tm_set A) = closure (tm_set (toDNF A))`

All conjectures carry `sorry`.

---

## Overall status

| Area | Status |
|---|---|
| Core state space & formula language | Complete (axiomatised) |
| Truthmaking/falsitymaking axioms | Complete |
| Fusion theorems (`comm`, `assoc`, etc.) | Mostly `sorry` |
| Entailment framework | Proved |
| Content theorems | Proved |
| Closure operators | Defined; key properties `sorry` |
| Closure-based entailments | Defined; theorems pending |
| Inexact truthmaking | Defined; main theorems `sorry` |
| Conjunctive parthood | Proved |
| Normal forms (predicates) | Defined; uniqueness `sorry` |
| Normal forms (`toDNF`/`toCNF`) | Axiomatised (non-computational) |
| Bilateral entailment (`⊨ᶠᶜ`, `⊨ᶠᵈ`) | Defined; reflexivity/transitivity `sorry` |
| Canonical model | Partial — valuations not extended to complex formulas, no verification against axioms |
| Bilateral conjectures | All `sorry` |
| Other problems files | Mostly `sorry` / scaffold |
