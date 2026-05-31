import RequestProject.Hopfield.Defs

/-!
# Valid State Lemmas

Properties of ±1 states and preservation under updates.
-/

namespace Hopfield

open Finset Function

variable {N : ℕ}

/-! ## Basic arithmetic facts for ±1 values -/

lemma ValidState.sq_eq_one {s : Fin N → ℝ} (hs : ValidState s) (i : Fin N) :
    s i * s i = 1 := by
  cases hs i <;> simp +decide [ * ]

lemma ValidState.neg_mem {s : Fin N → ℝ} (hs : ValidState s) (i : Fin N) :
    -(s i) = 1 ∨ -(s i) = -1 := by
  cases hs i <;> simp +decide [ * ]

lemma ValidState.ne_zero {s : Fin N → ℝ} (hs : ValidState s) (i : Fin N) :
    s i ≠ 0 := by
  cases hs i <;> aesop

lemma ValidState.abs_eq_one {s : Fin N → ℝ} (hs : ValidState s) (i : Fin N) :
    |s i| = 1 := by
  cases hs i <;> simp +decide [ * ]

/-! ## Preservation under updates -/

lemma asyncUpdate_valid {W : Matrix (Fin N) (Fin N) ℝ} {θ : Fin N → ℝ}
    {s : Fin N → ℝ} (hs : ValidState s) (i : Fin N) :
    ValidState (asyncUpdate W θ s i) := by
  intro j; by_cases hj : j = i <;> simp_all +decide [ asyncUpdate ] ;
  · split_ifs <;> simp +decide [ *, update_apply ];
    exact hs i;
  · exact hs j

lemma flipUnit_valid {s : Fin N → ℝ} (hs : ValidState s) (i : Fin N) :
    ValidState (flipUnit s i) := by
  intro j; by_cases h : j = i <;> simp_all +decide [ flipUnit ] ;
  · cases hs i <;> aesop;
  · exact hs j

/-! ## Async update access lemmas -/

@[simp]
lemma asyncUpdate_self (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) (i : Fin N) :
    asyncUpdate W θ s i i =
      if 0 < localField W θ s i then 1
      else if localField W θ s i < 0 then -1
      else s i := by
  exact Function.update_self _ _ _

@[simp]
lemma asyncUpdate_ne (W : Matrix (Fin N) (Fin N) ℝ) (θ : Fin N → ℝ)
    (s : Fin N → ℝ) {i j : Fin N} (hij : j ≠ i) :
    asyncUpdate W θ s i j = s j := by
  exact Function.update_of_ne hij _ _

@[simp]
lemma flipUnit_self (s : Fin N → ℝ) (i : Fin N) :
    flipUnit s i i = -(s i) := by
  exact Function.update_self _ _ _

@[simp]
lemma flipUnit_ne (s : Fin N → ℝ) {i j : Fin N} (hij : j ≠ i) :
    flipUnit s i j = s j := by
  exact Function.update_of_ne hij _ _

/-! ## Encoding lemma -/

lemma encodeState_injective_on_valid {s t : Fin N → ℝ}
    (hs : ValidState s) (ht : ValidState t)
    (h : encodeState s = encodeState t) : s = t := by
  funext i; have := congr_fun h i; cases hs i <;> cases ht i <;> simp_all +decide [ encodeState ] ;

end Hopfield