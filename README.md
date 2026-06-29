# hopfield-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-7%20theorems%20%2F%200%20sorry-brightgreen)](Hopfield)
[![Paper](https://img.shields.io/badge/Zenodo-20474169-blue)](https://zenodo.org/records/20474169)

Lean 4 formal proofs of Hopfield network energy descent and attractor convergence.

**Zero sorry statements.** Discrete Hopfield networks over finite state spaces.

## Why it matters

Hopfield networks are among the oldest and most studied models of associative memory. Their convergence guarantee -- that asynchronous updates always decrease a Lyapunov energy function and therefore terminate at a fixed-point attractor -- is a foundational result connecting neural dynamics, statistical physics, and optimisation.

This result is well-known but rarely stated with full precision: symmetry hypotheses, zero-diagonal constraints, update rule side conditions, and the finite-descent argument all hide details that matter when building on top of them. This library machine-checks every step in Lean 4, giving a verified proof spine importable by future work on attractor networks, memory models, and AI safety.

The convergence proof uses no ODE or LaSalle machinery -- it encodes valid states as `Fin N → Bool` and applies the pigeonhole principle: ℕ cannot inject into a finite type, so strict energy decrease implies termination.

## Project structure

```
Hopfield/
├── Defs.lean         — ValidState, energy, localField, asyncUpdate, flipUnit, IsFixedPoint, encodeState
├── ValidState.lean   — ±1 arithmetic lemmas, preservation under updates, encoding injectivity
├── Energy.lean       — energy_diff identity, energy_descent (Theorem 1)
├── FixedPoint.lean   — fixed_point_iff (Theorem 2)
└── Convergence.lean  — convergence / no infinite descent (Theorem 3)
Hopfield.lean         — Root module importing all five
```

## Definitions

- **States:** `Fin N → ℝ` with `ValidState s` requiring each `s i ∈ {-1, +1}`
- **Weight matrix:** `Matrix (Fin N) (Fin N) ℝ` with `W.IsSymm` and `∀ i, W i i = 0`
- **Energy:** E(s) = -(1/2) Σᵢⱼ sᵢ Wᵢⱼ sⱼ + Σᵢ θᵢ sᵢ
- **Local field:** hᵢ = Σⱼ Wᵢⱼ sⱼ − θᵢ
- **Async update:** sets sᵢ to +1 if hᵢ > 0, −1 if hᵢ < 0, preserves sᵢ on ties

## Theorem inventory

### Layer 1 — Energy mechanics

| # | Name | Statement |
|---|------|-----------|
| 1 | `energy_diff` | ΔE = -(s'ᵢ − sᵢ) · hᵢ for single-unit modifications |
| 2 | `quadratic_diff` | Quadratic form change under single-unit update (uses symmetry + zero diagonal) |
| 3 | `energy_flip_eq` | Flip energy change = 2·sᵢ·hᵢ |

### Layer 2 — Main theorems

| # | Name | Statement |
|---|------|-----------|
| 4 | `energy_descent` | energy W θ (asyncUpdate W θ s i) ≤ energy W θ s |
| 5 | `energy_strict_descent` | State changes implies strict energy decrease |
| 6 | `fixed_point_iff` | IsFixedPoint W θ s ↔ ∀ i, energy W θ s ≤ energy W θ (flipUnit s i) |
| 7 | `convergence` | No infinite sequence of state-changing async updates exists |

## Key technical highlights

- `convergence` encodes valid states as `Fin N → Bool` and uses pigeonhole: strict energy decrease implies injectivity of the state sequence, which contradicts injection into a finite type
- No ODE machinery, no LaSalle, no Barbalat -- the finite state space closes it directly
- `energy_diff` master identity cleanly separates linear and quadratic terms
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
import Hopfield.FixedPoint   -- fixed point characterisation
import Hopfield.Energy       -- energy descent
import Hopfield.ValidState   -- state arithmetic
import Hopfield.Defs         -- core definitions
```

## Paper

**hopfield-lean: Formal Proofs of Hopfield Network Energy Descent and Attractor Convergence in Lean 4**  
Ben Cassie (2026). Zenodo.  
https://zenodo.org/records/20474169

## Cite

Cassie, B. (2026). *hopfield-lean: Formal Proofs of Hopfield Network Energy Descent and Attractor Convergence in Lean 4*. Zenodo. https://zenodo.org/records/20474169.

## Related work

- [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) — Lean 4 Kuramoto synchronisation. Zenodo: https://doi.org/10.5281/zenodo.20468619
- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence. Zenodo: https://doi.org/10.5281/zenodo.20472996
- [contraction-lean](https://github.com/velvetmonkey/contraction-lean) — Lean 4 contraction theory
- [lotka-volterra-lean](https://github.com/velvetmonkey/lotka-volterra-lean) — Lean 4 Lotka-Volterra Hamiltonian conservation
- [nesterov-lean](https://github.com/velvetmonkey/nesterov-lean) — Lean 4 Nesterov accelerated gradient descent

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline -- zero sorry, every Mathlib lemma name `#check`ed before use -- was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
