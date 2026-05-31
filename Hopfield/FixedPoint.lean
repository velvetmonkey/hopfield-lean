import RequestProject.Hopfield.Energy

/-!
# Fixed-Point Characterisation

A state is a fixed point of the Hopfield dynamics iff no single-unit flip
decreases the energy.
-/

namespace Hopfield

open Finset Function

variable {N : ℕ}

/-
Energy change from flipping unit i equals 2·sᵢ·hᵢ.
-/
lemma energy_flip_eq (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) (hW_symm : W.IsSymm) (hW_diag : ∀ k, W k k = 0)
    (i : Fin N) :
    energy W θ (flipUnit s i) - energy W θ s =
    2 * s i * localField W θ s i := by
  grind +suggestions

/-
**Fixed-point characterisation**: s is a fixed point iff no single-unit flip
    decreases energy.
-/
theorem fixed_point_iff (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) (hW_symm : W.IsSymm) (hW_diag : ∀ k, W k k = 0)
    (hs : ValidState s) :
    IsFixedPoint W θ s ↔ ∀ i, energy W θ s ≤ energy W θ (flipUnit s i) := by
  constructor <;> intro h;
  · intro i;
    have := @energy_flip_eq N W θ s hW_symm hW_diag i;
    have := h i;
    replace this := congr_fun this i; simp_all +decide [ asyncUpdate ] ;
    cases hs i <;> split_ifs at this <;> nlinarith;
  · intro i
    have h_localField : s i * localField W θ s i ≥ 0 := by
      linarith [ energy_flip_eq W θ s hW_symm hW_diag i, h i ];
    cases hs i <;> simp_all +decide [ asyncUpdate ]

end Hopfield