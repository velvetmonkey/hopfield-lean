# hopfield-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-pending-lightgrey)](Hopfield)

Lean 4 formal proofs of Hopfield network energy descent and attractor convergence.

**Zero sorry statements.** Discrete Hopfield networks over arbitrary finite state spaces.

## Why it matters

Hopfield networks are among the oldest and most studied models of associative memory. Their convergence guarantee -- that asynchronous updates always decrease a Lyapunov energy function and therefore terminate at a fixed-point attractor -- is a foundational result connecting neural dynamics, statistical physics, and optimisation.

This result is well-known but rarely stated with full precision: symmetry hypotheses, zero-diagonal constraints, update rule side conditions, and the finite-descent argument all hide details that matter when building on top of them. This library machine-checks every step in Lean 4, giving a verified proof spine importable by future work on attractor networks, memory models, and AI safety.

The convergence proof uses no ODE machinery -- the finite state space argument closes it directly. This makes hopfield-lean one of the most self-contained libraries in the series.

## Relationship to kuramoto-lean and gradient-descent-lean

This library is part of a programme of AI-assisted Lean 4 formalisation of dynamical systems mathematics:

- [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) -- Kuramoto synchronisation, gradient identities, Lyapunov descent
- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) -- O(1/k) and geometric convergence for smooth convex optimisation
- **hopfield-lean** -- Hopfield energy descent and attractor convergence (this repo)

All three share the same proof discipline: zero sorry, zero admit, no project-specific axioms, every Mathlib lemma name `#check`ed before use.

## Planned project structure

```
Hopfield/
├── Defs.lean         — State space, weight matrix, energy function, async update rule
├── Descent.lean      — Single-unit flip decreases or maintains energy
├── FixedPoints.lean  — Fixed point iff no flip decreases energy
└── Convergence.lean  — Asynchronous updates reach a fixed point in finite steps
```

## Planned theorem inventory

### Layer 1 — Foundations

| # | Theorem | Statement |
|---|---------|-----------|
| 1 | `hopfieldEnergy_def` | E(s) = -1/2 sᵀ W s + θᵀ s |
| 2 | `weights_symmetric` | Weight matrix symmetry hypothesis |
| 3 | `weights_zero_diagonal` | W i i = 0 for all i |
| 4 | `energy_bounded_below` | E(s) is bounded below over the finite state space |

### Layer 2 — Descent and Fixed Points

| # | Theorem | Statement |
|---|---------|-----------|
| 5 | `energy_nonincreasing_async_update` | Single-unit async flip: E(s') ≤ E(s) |
| 6 | `energy_strict_decrease_iff` | Flip strictly decreases energy iff the unit changes state |
| 7 | `fixed_point_iff_no_decrease` | s is a fixed point iff no flip decreases energy |
| 8 | `fixed_point_local_field_sign` | At a fixed point, the local field has consistent sign with state |

### Layer 3 — Convergence

| # | Theorem | Statement |
|---|---------|-----------|
| 9  | `energy_sequence_nonincreasing` | Energy sequence is non-increasing under repeated updates |
| 10 | `convergence_to_fixed_point` | Asynchronous updates terminate at a fixed-point attractor |

## Key technical highlights

- Convergence proof uses no ODE or LaSalle machinery -- finite state space + bounded energy closes it directly
- Works over `Fin N → ℝ` with states in `{-1, +1}`, weight matrix `Matrix (Fin N) (Fin N) ℝ`
- Standard axioms only: `propext`, `Classical.choice`, `Quot.sound`
- Zero `sorry`, zero `admit`

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Usage

Add to your `lakefile.toml`:

```toml
[[require]]
name = "Hopfield"
scope = "velvetmonkey"
rev = "main"
```

Then import:

```lean
import Hopfield.Convergence  -- attractor convergence
import Hopfield.Descent      -- energy descent lemma
import Hopfield.FixedPoints  -- fixed point characterisation
import Hopfield.Defs         -- core definitions
```

## Paper

Companion paper forthcoming. To be published on Zenodo.

## Cite

Zenodo DOI forthcoming.

## Related work

- [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) — Lean 4 formalisation of Kuramoto synchronisation. Zenodo: https://doi.org/10.5281/zenodo.20468619
- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence. Zenodo: https://doi.org/10.5281/zenodo.20472996
- [flywheel-universe](https://zenodo.org/doi/10.5281/zenodo.20469680) — Budgeted Hebbian Kuramoto dynamics companion paper

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
