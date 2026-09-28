import Erdos1135.ND.PhaseGap
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Phase-Gap Rotation Sums

This file is the first checked P3 interface.  It turns the conditional
`PhaseGap` hypothesis into the finite rotation-sum estimate used by the later
Erdős--Turán argument.  No discrepancy theorem is assumed here.
-/

open scoped BigOperators FourierTransform

namespace Erdos1135
namespace ND

/-- The unanchored `N`-term Fourier sum at positive integer frequency `q`. -/
noncomputable def ndPhaseRotationSum (N q : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    (Real.fourierChar
      ((n : ℝ) * ((q : ℝ) * logTwoThree)) : ℂ)

/-- The normalized rotation sum.  Its public bound below requires `N > 0`. -/
noncomputable def ndPhaseRotationAverage (N q : ℕ) : ℂ :=
  ((N : ℂ)⁻¹) * ndPhaseRotationSum N q

/-- The chord of the analyst's Fourier character controls four times the
distance to the nearest integer. -/
private theorem nearestIntegerNorm_chord (x : ℝ) :
    4 * nearestIntegerNorm x ≤
      ‖((Real.fourierChar x : Circle) : ℂ) - 1‖ := by
  have hd : |x - (round x : ℝ)| ≤ (1 : ℝ) / 2 := abs_sub_round x
  have hpi :
      |Real.pi * (x - (round x : ℝ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_left hd Real.pi_pos.le)
  have hj := Real.mul_abs_le_abs_sin hpi
  have hj' :
      2 * |x - (round x : ℝ)| ≤
        |Real.sin (Real.pi * (x - (round x : ℝ)))| := by
    calc
      2 * |x - (round x : ℝ)|
          = 2 / Real.pi * |Real.pi * (x - (round x : ℝ))| := by
              rw [abs_mul, abs_of_pos Real.pi_pos]
              field_simp [Real.pi_ne_zero]
      _ ≤ _ := hj
  have hsin :
      |Real.sin (Real.pi * (x - (round x : ℝ)))| =
        |Real.sin (Real.pi * x)| := by
    rw [show Real.pi * (x - (round x : ℝ)) =
        Real.pi * x - (round x : ℝ) * Real.pi by ring]
    rw [Real.sin_sub_int_mul_pi]
    simp [abs_mul]
  rw [nearestIntegerNorm]
  change 4 * |x - (round x : ℝ)| ≤
    ‖Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) - 1‖
  rw [show (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) =
      Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) by ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  rw [← hsin]
  linarith

/-- `PhaseGap` bounds the raw finite rotation sum by the reciprocal gap.

The empty sum `N = 0` is allowed.  The positive-frequency hypothesis is
load-bearing: the corresponding claim at `q = 0` is false for nonempty sums.
-/
theorem norm_ndPhaseRotationSum_le
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (N q : ℕ) (hq : 0 < q) :
    ‖ndPhaseRotationSum N q‖ ≤
      (2 * c * Real.rpow (q : ℝ) (1 - kappa))⁻¹ := by
  let z : ℂ :=
    (Real.fourierChar ((q : ℝ) * logTwoThree) : ℂ)
  have hrpow_pos :
      0 < Real.rpow (q : ℝ) (1 - kappa) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hq) _
  have hscale_pos :
      0 < c * Real.rpow (q : ℝ) (1 - kappa) :=
    mul_pos hPhase.c_pos hrpow_pos
  have hden :
      4 * (c * Real.rpow (q : ℝ) (1 - kappa)) ≤ ‖z - 1‖ := by
    calc
      4 * (c * Real.rpow (q : ℝ) (1 - kappa))
          ≤ 4 * nearestIntegerNorm ((q : ℝ) * logTwoThree) := by
              gcongr
              exact hPhase.gap q hq
      _ ≤ ‖z - 1‖ := by
              simpa [z] using
                nearestIntegerNorm_chord ((q : ℝ) * logTwoThree)
  have hden_pos : 0 < ‖z - 1‖ :=
    lt_of_lt_of_le (mul_pos (by norm_num) hscale_pos) hden
  have hz : z ≠ 1 := by
    intro hz
    rw [hz, sub_self, norm_zero] at hden_pos
    exact lt_irrefl 0 hden_pos
  have hsum :
      ndPhaseRotationSum N q = ∑ n ∈ Finset.range N, z ^ n := by
    unfold ndPhaseRotationSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (n : ℝ) * ((q : ℝ) * logTwoThree) =
        n • ((q : ℝ) * logTwoThree) by simp [nsmul_eq_mul]]
    rw [AddChar.map_nsmul_eq_pow]
    exact Circle.coe_pow _ _
  rw [hsum, geom_sum_eq hz, norm_div]
  apply (div_le_iff₀ hden_pos).2
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    calc
      ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow]
        change ‖(Real.fourierChar
          ((q : ℝ) * logTwoThree) : ℂ)‖ ^ N + ‖(1 : ℂ)‖ = 2
        rw [Circle.norm_coe]
        norm_num
  have hinv_nonneg :
      0 ≤ (2 * c * Real.rpow (q : ℝ) (1 - kappa))⁻¹ :=
    inv_nonneg.mpr <|
      mul_nonneg (mul_nonneg (by norm_num) hPhase.c_pos.le) hrpow_pos.le
  calc
    ‖z ^ N - 1‖ ≤ 2 := hnum
    _ = (2 * c * Real.rpow (q : ℝ) (1 - kappa))⁻¹ *
          (4 * (c * Real.rpow (q : ℝ) (1 - kappa))) := by
      field_simp [hPhase.c_pos.ne', hrpow_pos.ne']
      norm_num
    _ ≤ (2 * c * Real.rpow (q : ℝ) (1 - kappa))⁻¹ * ‖z - 1‖ :=
      mul_le_mul_of_nonneg_left hden hinv_nonneg

/-- Positive-length normalized rotation sums obey both the trivial unit bound
and the sharp `PhaseGap` reciprocal bound needed by Erdős--Turán. -/
theorem norm_ndPhaseRotationAverage_le
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (N q : ℕ) (hN : 0 < N) (hq : 0 < q) :
    ‖ndPhaseRotationAverage N q‖ ≤
      min 1
        (2 * (N : ℝ) * c *
          Real.rpow (q : ℝ) (1 - kappa))⁻¹ := by
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hrpow_pos :
      0 < Real.rpow (q : ℝ) (1 - kappa) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hq) _
  have hsum_trivial : ‖ndPhaseRotationSum N q‖ ≤ (N : ℝ) := by
    unfold ndPhaseRotationSum
    calc
      ‖∑ n ∈ Finset.range N,
          (Real.fourierChar
            ((n : ℝ) * ((q : ℝ) * logTwoThree)) : ℂ)‖
          ≤ ∑ n ∈ Finset.range N,
              ‖(Real.fourierChar
                ((n : ℝ) * ((q : ℝ) * logTwoThree)) : ℂ)‖ :=
            norm_sum_le _ _
      _ = (N : ℝ) := by simp
  have havg_norm :
      ‖ndPhaseRotationAverage N q‖ =
        (N : ℝ)⁻¹ * ‖ndPhaseRotationSum N q‖ := by
    rw [ndPhaseRotationAverage, norm_mul, norm_inv]
    norm_cast
  apply le_min
  · rw [havg_norm]
    calc
      (N : ℝ)⁻¹ * ‖ndPhaseRotationSum N q‖
          ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hsum_trivial
              (inv_nonneg.mpr hNreal.le)
      _ = 1 := inv_mul_cancel₀ hNreal.ne'
  · rw [havg_norm]
    calc
      (N : ℝ)⁻¹ * ‖ndPhaseRotationSum N q‖
          ≤ (N : ℝ)⁻¹ *
              (2 * c * Real.rpow (q : ℝ) (1 - kappa))⁻¹ :=
            mul_le_mul_of_nonneg_left
              (norm_ndPhaseRotationSum_le hPhase N q hq)
              (inv_nonneg.mpr hNreal.le)
      _ = (2 * (N : ℝ) * c *
            Real.rpow (q : ℝ) (1 - kappa))⁻¹ := by
          field_simp [hNreal.ne', hPhase.c_pos.ne', hrpow_pos.ne']

end ND
end Erdos1135
