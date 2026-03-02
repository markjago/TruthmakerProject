# Truthmaker Semantics in Lean4

A formalization of Kit Fine's truthmaker semantics with support for hyperintensional reasoning.

## Project Structure

### Core/
The foundational definitions and axioms - **always import these**.

- **Basic.lean**: Primitive types (State, Formula, etc.) and basic relations (verification, fusion)
- **Axioms.lean**: Standard Fine axioms for how verification works with connectives
- **Theorems.lean**: Proven results that follow from the core axioms

**When to edit Core/**: Only when you need to change fundamental definitions or add proven theorems that should be available everywhere.

### Extensions/
Optional semantic features - **import only what you need**.

Each file in Extensions/ adds additional axioms or definitions for optional features:
- **NullState.lean**: Adds an impossible/null state
- **PartialVerification.lean**: Adds partial (inexact) verification alongside exact verification

**When to create new extensions**: When you want to explore variants of the framework (e.g., adding a part-of relation, alternative negation, etc.) without changing the core.

**How to use**: Import specific extension files only in the problems/experiments where you need them.

### Problems/
Your conjectures and theorems to prove - **this is where you do your research**.

- **Hyperintensionality.lean**: Problems about hyperintensional distinctions
- **Conjunction.lean**: Problems about conjunction behavior
- (Add more as needed)

**How to use**: 
1. State your conjecture as a theorem with `sorry` as the proof
2. Try to prove it
3. Move successful proofs to Core/Theorems.lean if they're fundamental

### Experiments/
Sandbox for trying things out - **safe to delete and recreate**.

- **Scratch.lean**: Test ideas without committing to the main codebase

**How to use**: Experiment freely here. Try different formulations, test proof strategies, etc.

## Workflow

### Starting a new problem:
1. Create a new file in Problems/ or add to an existing one
2. Import Core.Basic and Core.Axioms
3. Import any Extensions you need for this specific problem
4. State your theorem with `sorry` as the proof
5. Iterate on the proof with Claude Code

### Adding a new extension:
1. Create a new file in Extensions/
2. Import Core files
3. Add your new axioms/definitions
4. Document what the extension does at the top of the file

### Proving a fundamental theorem:
1. Start in Problems/ or Experiments/
2. Once proven, move it to Core/Theorems.lean
3. It's now available throughout the project

## Import Strategy

**Minimal imports**: Only import what you need for each file. This keeps dependencies clear and makes it easy to swap extensions in and out.

**Example**:
```lean
-- For standard truthmaker work:
import Core.Basic
import Core.Axioms

-- If you need null states for this problem:
import Extensions.NullState

-- If you need partial verification:
import Extensions.PartialVerification
```

## Next Steps

1. Start with a simple theorem in Problems/
2. Try to state it formally
3. Attempt a proof
4. Ask Claude/Claude Code for help when stuck
5. Iterate!
