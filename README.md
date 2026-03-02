# Truthmaker Semantics in Lean 4

A formalisation of **exact truthmaker semantics** in the style of Kit Fine, built on Lean 4 and Mathlib.

## What this project formalises

Truthmaker semantics assigns to each formula both a set of *verifiers* (states that exactly make it true) and a set of *falsifiers* (states that exactly make it false). This is a **hyperintensional** framework: two formulas can be necessarily equivalent yet differ in content, because they are verified or falsified by different states.

The core semantic clauses are:

| Connective | Truthmaking | Falsitymaking |
|---|---|---|
| atom `p` | `s ∈ V⁺(p)` | `s ∈ V⁻(p)` |
| `∼A` | `s` falsifies `A` | `s` verifies `A` |
| `A ∧ B` | `s = t ⊔ u`, `t` verifies `A`, `u` verifies `B` | `s` falsifies `A` or `s` falsifies `B` |
| `A ∨ B` | `s` verifies `A` or `s` verifies `B` | `s = t ⊔ u`, `t` falsifies `A`, `u` falsifies `B` |

where `⊔` is the fusion (join) of two states in a partial order.

## Dependencies

- [Lean 4](https://leanprover.github.io/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)

## Building

```bash
git clone https://github.com/markjago/TruthmakerProject
cd TruthmakerProject
lake update    # downloads Mathlib (large; may take a while first time)
lake build
```

## Module structure

```
Core/               foundational axioms and language
  StateSpace.lean     states, parthood, fusion, lub
  Basic.lean          Formula type, valuations, truthmakes/falsitymakes
  Axioms.lean         recursive clauses for ⊩ and ⫣
  Theorems.lean       derived theorems (fusion properties, etc.)
  Entailment.lean     abstract entailment framework (unilateral and bilateral)

Extensions/         optional derived concepts
  Content.lean        truthmaker/falsitymaker sets; set fusion
  Closure.lean        closed, convex, and regular sets of states
  ClosureEntailment.lean  entailment variants using closed content
  BilateralEntailment.lean  full-conjunctive and full-disjunctive entailment
  InexactTruthmaking.lean   inexact (downward-closed) verification
  ConjunctiveParthood.lean  conjunctive parthood on sets of states
  NormalForms.lean    DNF/CNF predicates; toDNF and toCNF functions
  NullState.lean      properties of the null state
  CanonicalModel.lean canonical model (states = sets of literals)

Problems/           open conjectures
  EntailmentBasics.lean
  Conjunction.lean
  Hyperintensionality.lean
  BilateralConjectures.lean

Experiments/        scratch space
```

## Key terminology

- **Exact** entailment/equivalence (notation `⊨ₑ`, `≡ₑ`): **unilateral** — defined in terms of truthmakers only.
- **Full** entailment/equivalence (notation `⊨ᶠ`, `≡ᶠ`): **bilateral** — defined in terms of both truthmakers and falsitymakers.
- **Full-conjunctive** (`⊨ᶠᶜ`): `A ⊨ᶠᶜ B` iff `A ∧ B ≡ A` (under closed content).
- **Full-disjunctive** (`⊨ᶠᵈ`): `A ⊨ᶠᵈ B` iff `A ∨ B ≡ B` (under closed content).

## Status and working notes

See [`NOTES.md`](NOTES.md) for a detailed file-by-file description of what is defined, what is proved, and what remains as `sorry`.

## Contributing

New problems and extensions are welcome. The typical workflow is:

1. Add a new file in `Problems/` with your conjecture stated as a `theorem ... := by sorry`.
2. Import only what you need (`Core.Basic`, `Core.Axioms`, and whichever `Extensions` are relevant).
3. Register it in `TruthmakerProject.lean`.
4. Attempt the proof, or leave it as a conjecture for others.
