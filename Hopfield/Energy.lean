import RequestProject.Hopfield.ValidState

/-!
# Energy Descent Lemma

The key result: energy never increases under a single asynchronous unit update,
and strictly decreases when the state actually changes.
-/

namespace Hopfield

open Finset Function

variable {N : ℕ}

/-! ## Energy Change Formula -/

/-
When only unit i changes, the linear part θᵀs changes by θᵢ·(s′ᵢ − sᵢ).
-/
lemma linear_diff (θ : Fin N → ℝ) (s s' : Fin N → ℝ) (i : Fin N)
    (heq : ∀ j, j ≠ i → s' j = s j) :
    (∑ j, θ j * s' j) - (∑ j, θ j * s j) = θ i * (s' i - s i) := by
  rw [ ← Finset.sum_sub_distrib ];
  rw [ Finset.sum_eq_single i ] <;> ring <;> aesop

/-
When only unit i changes and W is symmetric with zero diagonal,
    the quadratic form sᵀWs changes by 2·(s′ᵢ − sᵢ)·Σⱼ Wᵢⱼ sⱼ.
-/
lemma quadratic_diff (W : Matrix (Fin N) (Fin N) ℝ) (s s' : Fin N → ℝ)
    (i : Fin N) (hW_symm : W.IsSymm) (hW_diag : ∀ k, W k k = 0)
    (heq : ∀ j, j ≠ i → s' j = s j) :
    (∑ a, ∑ b, s' a * W a b * s' b) - (∑ a, ∑ b, s a * W a b * s b) =
    2 * (s' i - s i) * ∑ j, W i j * s j := by
  simp +decide only [← sum_sub_distrib, Finset.mul_sum];
  rw [ Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_ ];
  rotate_left;
  use fun x y => if x = i then if y = i then 0 else ( s' i - s i ) * W i y * s y else if y = i then ( s' i - s i ) * s x * W x i else 0;
  · by_cases hi : x = i <;> by_cases hj : y = i <;> simp_all +decide [ sub_mul ];
    ring;
  · simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ] ; ring;
    rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; rw [ ← hW_symm.apply ] ; ring;

/-
Master energy-change identity: ΔE = −(s′ᵢ − sᵢ) · hᵢ
-/
theorem energy_diff (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s s' : Fin N → ℝ) (i : Fin N)
    (hW_symm : W.IsSymm) (hW_diag : ∀ k, W k k = 0)
    (heq : ∀ j, j ≠ i → s' j = s j) :
    energy W θ s' - energy W θ s = -(s' i - s i) * localField W θ s i := by
  convert congr_arg₂ ( fun x y => - ( 1 / 2 : ℝ ) * x + y ) ( quadratic_diff W s s' i hW_symm hW_diag heq ) ( linear_diff θ s s' i heq ) using 1 ; ring_nf!;
  · unfold energy; ring;
  · unfold localField; ring;

/-! ## Theorem 1: Energy Descent -/

/-
**Key descent lemma**: energy never increases under a single asynchronous update.
-/
theorem energy_descent (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) (hW_symm : W.IsSymm) (hW_diag : ∀ k, W k k = 0)
    (hs : ValidState s) (i : Fin N) :
    energy W θ (asyncUpdate W θ s i) ≤ energy W θ s := by
  have := @energy_diff;
  specialize @this N W θ s ( asyncUpdate W θ s i ) i hW_symm hW_diag;
  simp_all +decide [ sub_eq_iff_eq_add, asyncUpdate ];
  cases hs i <;> split_ifs <;> nlinarith

/-
When an async update actually changes the state, energy **strictly** decreases.
-/
theorem energy_strict_descent (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) (hW_symm : W.IsSymm) (hW_diag : ∀ k, W k k = 0)
    (hs : ValidState s) (i : Fin N) (hne : asyncUpdate W θ s i ≠ s) :
    energy W θ (asyncUpdate W θ s i) < energy W θ s := by
  -- Apply energy_diff with s' = asyncUpdate W� s i. heq follows from asyncUpdate_ne.
  have h_diff : energy W θ (asyncUpdate W θ s i) - energy W θ s = -( (asyncUpdate W θ s i i) - (s i) ) * (localField W θ s i) := by
    convert energy_diff W θ s ( asyncUpdate W θ s i ) i hW_symm hW_diag _ using 1;
    exact fun j a => asyncUpdate_ne W θ s a;
  cases hs i <;> simp_all +decide [ sub_eq_iff_eq_add ];
  · split_ifs <;> simp_all +decide [ funext_iff, asyncUpdate ];
    · grind +extAll;
    · linarith;
    · exact hne.elim fun x hx => hx <| by rw [ update_apply ] ; aesop;
  · contrapose! hne; ext j; by_cases hj : j = i <;> simp_all +decide ;
    intro h; split_ifs at hne ; nlinarith;

end Hopfield