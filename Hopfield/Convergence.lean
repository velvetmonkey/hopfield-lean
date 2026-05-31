import RequestProject.Hopfield.FixedPoint

/-!
# Convergence

There is no infinite sequence of non-trivial asynchronous updates.

The state space {±1}^N is finite, each non-trivial update strictly decreases energy,
so any chain of actual state changes must terminate in at most 2^N steps.
-/

namespace Hopfield

open Finset Function

variable {N : ℕ}

/-
**Convergence**: no infinite sequence of state-changing asynchronous updates exists.
    The proof uses finiteness of {±1}^N and strict energy decrease.
-/
theorem convergence (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (hW_symm : W.IsSymm) (hW_diag : ∀ k, W k k = 0)
    (f : ℕ → Fin N → ℝ) (units : ℕ → Fin N)
    (hvalid : ∀ n, ValidState (f n))
    (hstep : ∀ n, f (n + 1) = asyncUpdate W θ (f n) (units n))
    (hchange : ∀ n, f (n + 1) ≠ f n) : False := by
  -- By energy_strict_descent and hchange, for all n, energy(f(n+1)) < energy(f(n)).
  -- This means fun n => energy W (f n) is StrictAnti (strictly decreasing).
  have h_strict : ∀ n, energy W θ (f (n + 1)) < energy W θ (f n) := by
    grind +suggestions;
  -- Since the state space {±1}^N is finite, the function f must be injective.
  have h_inj : Function.Injective f := by
    -- Since energy is strictly decreasing, if f(m) = � f�(n), then energy(f(m)) = � energy�(f(n)), which contradicts the strict decrease unless m = n.
    have h_inj : ∀ m n, m < n → energy W θ (f m) > energy W θ (f n) := by
      exact fun m n mn => by induction mn <;> [ tauto; linarith [ h_strict ‹_› ] ] ;
    exact fun m n hmn => le_antisymm ( le_of_not_gt fun hmn' => by have := h_inj _ _ hmn'; aesop ) ( le_of_not_gt fun hmn' => by have := h_inj _ _ hmn'; aesop );
  -- Since the state space {±1}^N is finite, the function f must be injective. This contradicts the assumption that there is an infinite sequence of non-trivial asynchronous updates.
  have h_contradiction : Set.Infinite (Set.range f) → False := by
    exact Set.not_infinite.mpr ( Set.Finite.subset ( Set.toFinite ( Set.range ( fun s : Fin N → Bool => fun i => if s i = Bool.true then 1 else -1 ) ) ) <| Set.range_subset_iff.mpr fun n => by rcases hvalid n with h; exact ⟨ fun i => f n i = 1, by ext i; specialize h i; aesop ⟩ );
  exact h_contradiction <| Set.infinite_range_of_injective h_inj

end Hopfield