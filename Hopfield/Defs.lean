import Mathlib

/-!
# Hopfield Network Definitions

Core definitions for a Hopfield network with `N` binary (±1) units.

* `ValidState` — each component is +1 or −1
* `energy`     — E(s) = −½ sᵀWs + θᵀs
* `localField` — hᵢ = Σⱼ Wᵢⱼ sⱼ − θᵢ
* `asyncUpdate`— asynchronous single-unit update rule
* `flipUnit`   — negate one component
* `IsFixedPoint`— no async update changes the state
-/

namespace Hopfield

open Finset Function

variable {N : ℕ}

/-! ## Core Definitions -/

/-- A valid Hopfield state: every component is ±1. -/
def ValidState (s : Fin N → ℝ) : Prop :=
  ∀ i, s i = 1 ∨ s i = -1

/-- Hopfield energy: E(s) = −(1/2) Σᵢⱼ sᵢ Wᵢⱼ sⱼ + Σᵢ θᵢ sᵢ -/
noncomputable def energy (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, s i * W i j * s j +
  ∑ i : Fin N, θ i * s i

/-- Local field at unit i: hᵢ = Σⱼ Wᵢⱼ sⱼ − θᵢ -/
noncomputable def localField (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin N, W i j * s j - θ i

/-- Asynchronous update at unit i.
    s′ᵢ = +1  if  hᵢ > 0,
    s′ᵢ = −1  if  hᵢ < 0,
    s′ᵢ = sᵢ  if  hᵢ = 0   (tie-breaking preserves current value). -/
noncomputable def asyncUpdate (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) (i : Fin N) : Fin N → ℝ :=
  Function.update s i
    (if 0 < localField W θ s i then 1
     else if localField W θ s i < 0 then -1
     else s i)

/-- Flip unit i: negate the i-th component. -/
def flipUnit (s : Fin N → ℝ) (i : Fin N) : Fin N → ℝ :=
  Function.update s i (-(s i))

/-- A state is a fixed point iff every async update is a no-op. -/
def IsFixedPoint (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) : Prop :=
  ∀ i, asyncUpdate W θ s i = s

/-- Encode a ±1 vector as a Bool vector (for finiteness arguments). -/
noncomputable def encodeState (s : Fin N → ℝ) : Fin N → Bool :=
  fun i => decide (s i = 1)

end Hopfield
