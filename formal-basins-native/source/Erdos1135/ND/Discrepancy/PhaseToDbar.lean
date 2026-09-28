import Erdos1135.ND.Discrepancy.ErdosTuran
import Erdos1135.ND.Discrepancy.PhaseRotation

/-!
# Phase Gap to Endpoint Discrepancy

This file turns the conditional phase-gap estimate into the anchored orbit
interfaces consumed by the positive-length endpoint discrepancy bound.  The
first interface below records the exact anchor character before its unit norm
is removed.
-/

open scoped BigOperators FourierTransform
open AddCircle

namespace Erdos1135
namespace ND

/-- The rotation orbit with an arbitrary additive-circle anchor. -/
noncomputable def ndPhaseOrbit
    (phi : UnitAddCircle) (n : ℕ) : UnitAddCircle :=
  phi + n • (logTwoThree : UnitAddCircle)

/-- A Fourier character is multiplicative in its additive-circle argument. -/
private theorem fourier_add_argument
    (q : ℤ) (phi psi : UnitAddCircle) :
    fourier q (phi + psi) = fourier q phi * fourier q psi := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- The character along the unanchored orbit is the phase-rotation summand. -/
private theorem fourier_nsmul_logTwoThree (q n : ℕ) :
    fourier (q : ℤ) (n • (logTwoThree : UnitAddCircle)) =
      (Real.fourierChar
        ((n : ℝ) * ((q : ℝ) * logTwoThree)) : ℂ) := by
  rw [← AddCircle.coe_nsmul]
  rw [fourier_coe_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- Exact anchored factorization of the empirical character average. -/
theorem ndEmpiricalCharacterAverage_ndPhaseOrbit
    (phi : UnitAddCircle) (N q : ℕ) :
    ndEmpiricalCharacterAverage N (ndPhaseOrbit phi) (q : ℤ) =
      fourier (q : ℤ) phi * ndPhaseRotationAverage N q := by
  unfold ndEmpiricalCharacterAverage ndPhaseOrbit
    ndPhaseRotationAverage ndPhaseRotationSum
  calc
    (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          fourier (q : ℤ) (phi + n • (logTwoThree : UnitAddCircle)) =
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          fourier (q : ℤ) phi *
            (Real.fourierChar
              ((n : ℝ) * ((q : ℝ) * logTwoThree)) : ℂ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [fourier_add_argument, fourier_nsmul_logTwoThree]
    _ = fourier (q : ℤ) phi *
        ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          (Real.fourierChar
            ((n : ℝ) * ((q : ℝ) * logTwoThree)) : ℂ)) := by
      rw [← Finset.mul_sum]
      ring

/-- The anchor character has unit norm and contributes no discrepancy loss. -/
theorem norm_ndEmpiricalCharacterAverage_ndPhaseOrbit
    (phi : UnitAddCircle) (N q : ℕ) :
    ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi) (q : ℤ)‖ =
      ‖ndPhaseRotationAverage N q‖ := by
  rw [ndEmpiricalCharacterAverage_ndPhaseOrbit, norm_mul]
  rw [show ‖fourier (q : ℤ) phi‖ = 1 by
    rw [fourier_apply, Circle.norm_coe]]
  exact one_mul _

/-- The raw weak error uses the same strict left-endpoint anchor as the raw
strict error. -/
theorem ndWeakEmpiricalError_eq_centeredWeak_sub_centeredStrict_zero
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) :
    ndWeakEmpiricalError N x t =
      ndCenteredWeakEmpiricalError N x t -
        ndCenteredStrictEmpiricalError N x 0 := by
  unfold ndCenteredWeakEmpiricalError ndCenteredStrictEmpiricalError
    ndStrictEmpiricalError
  rw [ndStrictEmpiricalCDF_zero]
  ring

/-- Raw strict endpoint error is always at most one on the fundamental
interval, including for the empty sample. -/
theorem abs_ndStrictEmpiricalError_le_one
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndStrictEmpiricalError N x t| ≤ 1 := by
  rw [ndStrictEmpiricalError_eq_centered_sub_zero]
  calc
    |ndCenteredStrictEmpiricalError N x t -
        ndCenteredStrictEmpiricalError N x 0| ≤
        |ndCenteredStrictEmpiricalError N x t| +
          |ndCenteredStrictEmpiricalError N x 0| := abs_sub _ _
    _ ≤ 1 := by
      have ht' := abs_ndCenteredStrictEmpiricalError_le_half N x t ht
      have hzero := abs_ndCenteredStrictEmpiricalError_le_half N x 0 (by norm_num)
      linarith

/-- Raw weak endpoint error obeys the same unit cap. -/
theorem abs_ndWeakEmpiricalError_le_one
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndWeakEmpiricalError N x t| ≤ 1 := by
  rw [ndWeakEmpiricalError_eq_centeredWeak_sub_centeredStrict_zero]
  calc
    |ndCenteredWeakEmpiricalError N x t -
        ndCenteredStrictEmpiricalError N x 0| ≤
        |ndCenteredWeakEmpiricalError N x t| +
          |ndCenteredStrictEmpiricalError N x 0| := abs_sub _ _
    _ ≤ 1 := by
      have ht' := abs_ndCenteredWeakEmpiricalError_le_half N x t ht
      have hzero := abs_ndCenteredStrictEmpiricalError_le_half N x 0 (by norm_num)
      linarith

/-- The sharp weak endpoint analogue of the checked anchored Erdős--Turán
estimate. -/
theorem abs_ndWeakEmpiricalError_le_erdosTuran_sharp
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) (hH : 0 < H)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndWeakEmpiricalError N x t| ≤
      6 / (((H + 1 : ℕ) : ℝ)) +
        (4 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ)) -
              1 / (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
  have hamp := ndEmpiricalAmplitude_le_erdosTuran N H x hN hH
  have htA := abs_ndCenteredWeakEmpiricalError_le_amplitude N x t ht
  have hzeroA :=
    abs_ndCenteredStrictEmpiricalError_le_amplitude N x 0 (by norm_num)
  rw [ndWeakEmpiricalError_eq_centeredWeak_sub_centeredStrict_zero]
  calc
    |ndCenteredWeakEmpiricalError N x t -
        ndCenteredStrictEmpiricalError N x 0| ≤
        |ndCenteredWeakEmpiricalError N x t| +
          |ndCenteredStrictEmpiricalError N x 0| := abs_sub _ _
    _ ≤ 2 * ndEmpiricalAmplitude N x := by linarith
    _ ≤ 2 * (3 / (((H + 1 : ℕ) : ℝ)) +
        (2 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ)) -
              1 / (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖) :=
      mul_le_mul_of_nonneg_left hamp (by norm_num)
    _ = 6 / (((H + 1 : ℕ) : ℝ)) +
        (4 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ)) -
              1 / (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
      ring

/-- The weak endpoint analogue of the weakened anchored Erdős--Turán
estimate, with exactly the same right-hand side as the strict theorem. -/
theorem abs_ndWeakEmpiricalError_le_erdosTuran
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) (hH : 0 < H)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndWeakEmpiricalError N x t| ≤
      6 / (((H + 1 : ℕ) : ℝ)) +
        (4 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
  calc
    |ndWeakEmpiricalError N x t| ≤
        6 / (((H + 1 : ℕ) : ℝ)) +
          (4 / Real.pi) * ∑ j ∈ Finset.range H,
            (1 / (((j + 1 : ℕ) : ℝ)) -
                1 / (((H + 1 : ℕ) : ℝ))) *
              ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ :=
      abs_ndWeakEmpiricalError_le_erdosTuran_sharp N H x hN hH t ht
    _ ≤ 6 / (((H + 1 : ℕ) : ℝ)) +
        (4 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hH1inv : 0 ≤ 1 / (((H + 1 : ℕ) : ℝ)) := by positivity
      linarith

/-- A single endpoint majorant controls both strict and weak empirical
errors on the closed fundamental interval. -/
def ndStrictWeakEndpointDiscrepancyLE
    (N : ℕ) (x : ℕ → UnitAddCircle) (D : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1,
    |ndStrictEmpiricalError N x t| ≤ D ∧
      |ndWeakEmpiricalError N x t| ≤ D

/-- The source-locked cutoff `ceil (N^(1/kappa)) - 1`. -/
private noncomputable def ndEndpointCutoff
    (kappa : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (Real.rpow (N : ℝ) (1 / kappa)) - 1

@[simp] private theorem ndEndpointCutoff_one (kappa : ℝ) :
    ndEndpointCutoff kappa 1 = 0 := by
  simp [ndEndpointCutoff]

private theorem ndEndpointCutoff_pos
    {kappa : ℝ} (hkappa : 0 < kappa)
    {N : ℕ} (hN : 1 < N) :
    0 < ndEndpointCutoff kappa N := by
  let R := Real.rpow (N : ℝ) (1 / kappa)
  have hR : 1 < R := by
    dsimp [R]
    exact Real.one_lt_rpow
      (by exact_mod_cast hN)
      (one_div_pos.mpr hkappa)
  have hceil : 1 + 1 ≤ Nat.ceil R :=
    Nat.add_one_le_ceil_iff.mpr (by
      simpa only [Nat.cast_one] using hR)
  change 0 < Nat.ceil R - 1
  omega

private theorem ndEndpointCutoff_cast_le_root
    {kappa : ℝ} (hkappa : 0 < kappa)
    {N : ℕ} (hN : 1 < N) :
    (ndEndpointCutoff kappa N : ℝ) ≤
      Real.rpow (N : ℝ) (1 / kappa) := by
  let R := Real.rpow (N : ℝ) (1 / kappa)
  have hR : 1 < R := by
    dsimp [R]
    exact Real.one_lt_rpow
      (by exact_mod_cast hN)
      (one_div_pos.mpr hkappa)
  have hceil2 : 1 + 1 ≤ Nat.ceil R :=
    Nat.add_one_le_ceil_iff.mpr (by
      simpa only [Nat.cast_one] using hR)
  have hceil1 : 1 ≤ Nat.ceil R := by omega
  have hceil_lt : (Nat.ceil R : ℝ) < R + 1 :=
    Nat.ceil_lt_add_one (zero_lt_one.trans hR).le
  change ((Nat.ceil R - 1 : ℕ) : ℝ) ≤ R
  rw [Nat.cast_sub hceil1]
  norm_num only [Nat.cast_one]
  linarith

private theorem root_le_ndEndpointCutoff_add_one
    {kappa : ℝ} (hkappa : 0 < kappa)
    {N : ℕ} (hN : 1 < N) :
    Real.rpow (N : ℝ) (1 / kappa) ≤
      ((ndEndpointCutoff kappa N + 1 : ℕ) : ℝ) := by
  let R := Real.rpow (N : ℝ) (1 / kappa)
  have hR : 1 < R := by
    dsimp [R]
    exact Real.one_lt_rpow
      (by exact_mod_cast hN)
      (one_div_pos.mpr hkappa)
  have hceil2 : 1 + 1 ≤ Nat.ceil R :=
    Nat.add_one_le_ceil_iff.mpr (by
      simpa only [Nat.cast_one] using hR)
  have hceil1 : 1 ≤ Nat.ceil R := by omega
  change R ≤ (((Nat.ceil R - 1) + 1 : ℕ) : ℝ)
  rw [Nat.sub_add_cancel hceil1]
  exact Nat.le_ceil R

/-- The finite power sum needed after applying the phase-gap estimate. -/
private theorem sum_range_succ_rpow_le
    (H : ℕ) {kappa : ℝ} (hkappa : 2 < kappa) :
    ∑ j ∈ Finset.range H,
        Real.rpow (((j + 1 : ℕ) : ℝ)) (kappa - 2) ≤
      Real.rpow (H : ℝ) (kappa - 1) := by
  by_cases hH : H = 0
  · subst H
    simp [Real.zero_rpow (by linarith : kappa - 1 ≠ 0)]
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    have hHreal : 0 < (H : ℝ) := Nat.cast_pos.mpr hHpos
    calc
      ∑ j ∈ Finset.range H,
          Real.rpow (((j + 1 : ℕ) : ℝ)) (kappa - 2) ≤
          ∑ _j ∈ Finset.range H,
            Real.rpow (H : ℝ) (kappa - 2) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Real.rpow_le_rpow (by positivity) _ (by linarith)
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      _ = (H : ℝ) * Real.rpow (H : ℝ) (kappa - 2) := by
        simp
      _ = Real.rpow (H : ℝ) 1 *
          Real.rpow (H : ℝ) (kappa - 2) := by
        change (H : ℝ) * Real.rpow (H : ℝ) (kappa - 2) =
          (H : ℝ) ^ (1 : ℝ) * Real.rpow (H : ℝ) (kappa - 2)
        simp only [Real.rpow_one]
      _ = Real.rpow (H : ℝ) (1 + (kappa - 2)) :=
        (Real.rpow_add hHreal 1 (kappa - 2)).symm
      _ = Real.rpow (H : ℝ) (kappa - 1) := by
        rw [show 1 + (kappa - 2) = kappa - 1 by ring]

/-- Exact normalization of one Erdős--Turán weight after the phase bound. -/
private theorem phase_weight_algebra
    {c kappa : ℝ} {N q : ℕ} (hq : 0 < q) :
    (1 / (q : ℝ)) *
        (2 * (N : ℝ) * c *
          Real.rpow (q : ℝ) (1 - kappa))⁻¹ =
      Real.rpow (q : ℝ) (kappa - 2) /
        (2 * (N : ℝ) * c) := by
  have hqreal : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hrpow :
      (q : ℝ)⁻¹ *
          (Real.rpow (q : ℝ) (1 - kappa))⁻¹ =
        Real.rpow (q : ℝ) (kappa - 2) := by
    calc
      (q : ℝ)⁻¹ *
          (Real.rpow (q : ℝ) (1 - kappa))⁻¹ =
          Real.rpow (q : ℝ) (-1) *
            Real.rpow (q : ℝ) (-(1 - kappa)) := by
        congr 1
        · exact (Real.rpow_neg_one _).symm
        · exact (Real.rpow_neg hqreal.le _).symm
      _ = Real.rpow (q : ℝ) ((-1) + (-(1 - kappa))) :=
        (Real.rpow_add hqreal _ _).symm
      _ = Real.rpow (q : ℝ) (kappa - 2) := by
        congr 1
        ring
  calc
    (1 / (q : ℝ)) *
        (2 * (N : ℝ) * c *
          Real.rpow (q : ℝ) (1 - kappa))⁻¹ =
        ((q : ℝ)⁻¹ *
          (Real.rpow (q : ℝ) (1 - kappa))⁻¹) /
            (2 * (N : ℝ) * c) := by
      rw [one_div, mul_inv, div_eq_mul_inv]
      ring
    _ = Real.rpow (q : ℝ) (kappa - 2) /
        (2 * (N : ℝ) * c) := by
      rw [hrpow]

/-- The weighted character sum is bounded by the finite phase power sum. -/
private theorem phase_weighted_sum_le
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) (N H : ℕ) (hN : 0 < N) :
    ∑ j ∈ Finset.range H,
        (1 / (((j + 1 : ℕ) : ℝ))) *
          ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
            ((j + 1 : ℕ) : ℤ)‖ ≤
      Real.rpow (H : ℝ) (kappa - 1) /
        (2 * (N : ℝ) * c) := by
  have hden : 0 < 2 * (N : ℝ) * c := by
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hN))
      hPhase.c_pos
  calc
    ∑ j ∈ Finset.range H,
        (1 / (((j + 1 : ℕ) : ℝ))) *
          ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
            ((j + 1 : ℕ) : ℤ)‖ ≤
        ∑ j ∈ Finset.range H,
          Real.rpow (((j + 1 : ℕ) : ℝ)) (kappa - 2) /
            (2 * (N : ℝ) * c) := by
      apply Finset.sum_le_sum
      intro j hj
      have hq : 0 < j + 1 := Nat.succ_pos j
      calc
        (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
              ((j + 1 : ℕ) : ℤ)‖ ≤
            (1 / (((j + 1 : ℕ) : ℝ))) *
              (2 * (N : ℝ) * c *
                Real.rpow (((j + 1 : ℕ) : ℝ))
                  (1 - kappa))⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [norm_ndEmpiricalCharacterAverage_ndPhaseOrbit]
          exact (norm_ndPhaseRotationAverage_le
            hPhase N (j + 1) hN hq).trans (min_le_right _ _)
        _ = Real.rpow (((j + 1 : ℕ) : ℝ)) (kappa - 2) /
            (2 * (N : ℝ) * c) := phase_weight_algebra hq
    _ = (∑ j ∈ Finset.range H,
        Real.rpow (((j + 1 : ℕ) : ℝ)) (kappa - 2)) /
          (2 * (N : ℝ) * c) := by
      rw [Finset.sum_div]
    _ ≤ Real.rpow (H : ℝ) (kappa - 1) /
        (2 * (N : ℝ) * c) :=
      (div_le_div_iff_of_pos_right hden).2
        (sum_range_succ_rpow_le H hPhase.two_lt_kappa)

/-- The cutoff power has exactly the source exponent `1 - 1/kappa`. -/
private theorem cutoff_power_le_nat_scale
    {kappa : ℝ} (hkappa : 2 < kappa)
    {N : ℕ} (hN : 1 < N) :
    Real.rpow (ndEndpointCutoff kappa N : ℝ) (kappa - 1) ≤
      Real.rpow (N : ℝ) (1 - 1 / kappa) := by
  have hkappa_pos : 0 < kappa := by linarith
  have hcut := ndEndpointCutoff_cast_le_root hkappa_pos hN
  calc
    Real.rpow (ndEndpointCutoff kappa N : ℝ) (kappa - 1) ≤
        Real.rpow (Real.rpow (N : ℝ) (1 / kappa))
          (kappa - 1) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hcut (by linarith)
    _ = Real.rpow (N : ℝ) ((1 / kappa) * (kappa - 1)) :=
      (Real.rpow_mul (Nat.cast_nonneg N) (1 / kappa) (kappa - 1)).symm
    _ = Real.rpow (N : ℝ) (1 - 1 / kappa) := by
      congr 1
      field_simp [ne_of_gt hkappa_pos]

private theorem inv_root_eq_endpoint_scale
    (kappa : ℝ) (N : ℕ) :
    (Real.rpow (N : ℝ) (1 / kappa))⁻¹ =
      Real.rpow (N : ℝ) (-1 / kappa) := by
  calc
    (Real.rpow (N : ℝ) (1 / kappa))⁻¹ =
        Real.rpow (N : ℝ) (-(1 / kappa)) :=
      (Real.rpow_neg (Nat.cast_nonneg N) (1 / kappa)).symm
    _ = Real.rpow (N : ℝ) (-1 / kappa) := by
      congr 1
      ring

private theorem rpow_one_sub_div_nat_eq_endpoint_scale
    {kappa : ℝ} {N : ℕ} (hN : 0 < N) :
    Real.rpow (N : ℝ) (1 - 1 / kappa) / (N : ℝ) =
      Real.rpow (N : ℝ) (-1 / kappa) := by
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  calc
    Real.rpow (N : ℝ) (1 - 1 / kappa) / (N : ℝ) =
        Real.rpow (N : ℝ) ((1 - 1 / kappa) - 1) :=
      (Real.rpow_sub_one hNreal.ne' (1 - 1 / kappa)).symm
    _ = Real.rpow (N : ℝ) (-1 / kappa) := by
      congr 1
      ring

private theorem erdosTuran_cutoff_term_le
    {kappa : ℝ} (hkappa : 2 < kappa)
    {N : ℕ} (hN : 1 < N) :
    6 / (((ndEndpointCutoff kappa N + 1 : ℕ) : ℝ)) ≤
      6 * Real.rpow (N : ℝ) (-1 / kappa) := by
  have hkappa_pos : 0 < kappa := by linarith
  have hNpos : 0 < N := by omega
  have hroot_pos : 0 < Real.rpow (N : ℝ) (1 / kappa) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hNpos) _
  calc
    6 / (((ndEndpointCutoff kappa N + 1 : ℕ) : ℝ)) ≤
        6 / Real.rpow (N : ℝ) (1 / kappa) :=
      div_le_div_of_nonneg_left (by norm_num) hroot_pos
        (root_le_ndEndpointCutoff_add_one hkappa_pos hN)
    _ = 6 * Real.rpow (N : ℝ) (-1 / kappa) := by
      rw [div_eq_mul_inv, inv_root_eq_endpoint_scale kappa N]

private theorem phase_weighted_cutoff_term_le
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) {N : ℕ} (hN : 1 < N) :
    (4 / Real.pi) *
        (∑ j ∈ Finset.range (ndEndpointCutoff kappa N),
          (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
              ((j + 1 : ℕ) : ℤ)‖) ≤
      (2 / (Real.pi * c)) *
        Real.rpow (N : ℝ) (-1 / kappa) := by
  have hNpos : 0 < N := by omega
  have hden : 0 < 2 * (N : ℝ) * c := by
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hNpos))
      hPhase.c_pos
  have hsum :
      ∑ j ∈ Finset.range (ndEndpointCutoff kappa N),
          (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
              ((j + 1 : ℕ) : ℤ)‖ ≤
        Real.rpow (N : ℝ) (1 - 1 / kappa) /
          (2 * (N : ℝ) * c) := by
    calc
      ∑ j ∈ Finset.range (ndEndpointCutoff kappa N),
          (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
              ((j + 1 : ℕ) : ℤ)‖ ≤
          Real.rpow (ndEndpointCutoff kappa N : ℝ) (kappa - 1) /
            (2 * (N : ℝ) * c) :=
        phase_weighted_sum_le hPhase phi N
          (ndEndpointCutoff kappa N) hNpos
      _ ≤ Real.rpow (N : ℝ) (1 - 1 / kappa) /
          (2 * (N : ℝ) * c) :=
        (div_le_div_iff_of_pos_right hden).2
          (cutoff_power_le_nat_scale hPhase.two_lt_kappa hN)
  calc
    (4 / Real.pi) *
        (∑ j ∈ Finset.range (ndEndpointCutoff kappa N),
          (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
              ((j + 1 : ℕ) : ℤ)‖) ≤
        (4 / Real.pi) *
          (Real.rpow (N : ℝ) (1 - 1 / kappa) /
            (2 * (N : ℝ) * c)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 / (Real.pi * c)) *
        (Real.rpow (N : ℝ) (1 - 1 / kappa) / (N : ℝ)) := by
      field_simp [Real.pi_ne_zero, hPhase.c_pos.ne',
        (Nat.cast_pos.mpr hNpos).ne']
      ring
    _ = (2 / (Real.pi * c)) *
        Real.rpow (N : ℝ) (-1 / kappa) := by
      rw [rpow_one_sub_div_nat_eq_endpoint_scale hNpos]

/-- The v10 positive-length endpoint discrepancy majorant. -/
noncomputable def ndEndpointDbar
    (c kappa : ℝ) (N : ℕ) : ℝ :=
  min 1 ((6 + 2 / (Real.pi * c)) *
    Real.rpow (N : ℝ) (-1 / kappa))

private theorem ndEndpointDbar_one
    {c kappa : ℝ} (hc : 0 < c) :
    ndEndpointDbar c kappa 1 = 1 := by
  have hC : 1 ≤ 6 + 2 / (Real.pi * c) := by
    have hpos : 0 < 2 / (Real.pi * c) := by positivity
    linarith
  unfold ndEndpointDbar
  rw [Nat.cast_one]
  rw [show Real.rpow (1 : ℝ) (-1 / kappa) = 1 by
    exact Real.one_rpow _]
  rw [mul_one]
  exact min_eq_left hC

private theorem endpointDbar_constant_pos
    {c kappa : ℝ} (hPhase : PhaseGap c kappa) :
    0 < 6 + 2 / (Real.pi * c) := by
  have hden : 0 < Real.pi * c := mul_pos Real.pi_pos hPhase.c_pos
  have hfrac : 0 < 2 / (Real.pi * c) := div_pos (by norm_num) hden
  linarith

private theorem abs_ndStrictEmpiricalError_ndPhaseOrbit_le_uncapped_of_one_lt
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) {N : ℕ} (hN : 1 < N)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndStrictEmpiricalError N (ndPhaseOrbit phi) t| ≤
      (6 + 2 / (Real.pi * c)) *
        Real.rpow (N : ℝ) (-1 / kappa) := by
  have hNpos : 0 < N := by omega
  have hkappa_pos : 0 < kappa := by linarith [hPhase.two_lt_kappa]
  have hH : 0 < ndEndpointCutoff kappa N :=
    ndEndpointCutoff_pos hkappa_pos hN
  calc
    |ndStrictEmpiricalError N (ndPhaseOrbit phi) t| ≤
        6 / (((ndEndpointCutoff kappa N + 1 : ℕ) : ℝ)) +
          (4 / Real.pi) *
            ∑ j ∈ Finset.range (ndEndpointCutoff kappa N),
              (1 / (((j + 1 : ℕ) : ℝ))) *
                ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
                  ((j + 1 : ℕ) : ℤ)‖ :=
      abs_ndStrictEmpiricalError_le_erdosTuran N
        (ndEndpointCutoff kappa N) (ndPhaseOrbit phi) hNpos hH t ht
    _ ≤ 6 * Real.rpow (N : ℝ) (-1 / kappa) +
        (2 / (Real.pi * c)) *
          Real.rpow (N : ℝ) (-1 / kappa) :=
      add_le_add
        (erdosTuran_cutoff_term_le hPhase.two_lt_kappa hN)
        (phase_weighted_cutoff_term_le hPhase phi hN)
    _ = (6 + 2 / (Real.pi * c)) *
        Real.rpow (N : ℝ) (-1 / kappa) := by
      ring

private theorem abs_ndWeakEmpiricalError_ndPhaseOrbit_le_uncapped_of_one_lt
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) {N : ℕ} (hN : 1 < N)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndWeakEmpiricalError N (ndPhaseOrbit phi) t| ≤
      (6 + 2 / (Real.pi * c)) *
        Real.rpow (N : ℝ) (-1 / kappa) := by
  have hNpos : 0 < N := by omega
  have hkappa_pos : 0 < kappa := by linarith [hPhase.two_lt_kappa]
  have hH : 0 < ndEndpointCutoff kappa N :=
    ndEndpointCutoff_pos hkappa_pos hN
  calc
    |ndWeakEmpiricalError N (ndPhaseOrbit phi) t| ≤
        6 / (((ndEndpointCutoff kappa N + 1 : ℕ) : ℝ)) +
          (4 / Real.pi) *
            ∑ j ∈ Finset.range (ndEndpointCutoff kappa N),
              (1 / (((j + 1 : ℕ) : ℝ))) *
                ‖ndEmpiricalCharacterAverage N (ndPhaseOrbit phi)
                  ((j + 1 : ℕ) : ℤ)‖ :=
      abs_ndWeakEmpiricalError_le_erdosTuran N
        (ndEndpointCutoff kappa N) (ndPhaseOrbit phi) hNpos hH t ht
    _ ≤ 6 * Real.rpow (N : ℝ) (-1 / kappa) +
        (2 / (Real.pi * c)) *
          Real.rpow (N : ℝ) (-1 / kappa) :=
      add_le_add
        (erdosTuran_cutoff_term_le hPhase.two_lt_kappa hN)
        (phase_weighted_cutoff_term_le hPhase phi hN)
    _ = (6 + 2 / (Real.pi * c)) *
        Real.rpow (N : ℝ) (-1 / kappa) := by
      ring

/-- Strict phase-orbit endpoint discrepancy at every positive length. -/
theorem abs_ndStrictEmpiricalError_ndPhaseOrbit_le_endpointDbar
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) (N : ℕ) (hN : 0 < N)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndStrictEmpiricalError N (ndPhaseOrbit phi) t| ≤
      ndEndpointDbar c kappa N := by
  by_cases hN1 : N = 1
  · subst N
    rw [ndEndpointDbar_one hPhase.c_pos]
    exact abs_ndStrictEmpiricalError_le_one 1 (ndPhaseOrbit phi) t ht
  · have hNgt : 1 < N := by omega
    unfold ndEndpointDbar
    apply le_min
    · exact abs_ndStrictEmpiricalError_le_one N (ndPhaseOrbit phi) t ht
    · exact
        abs_ndStrictEmpiricalError_ndPhaseOrbit_le_uncapped_of_one_lt
          hPhase phi hNgt t ht

/-- Weak phase-orbit endpoint discrepancy with the identical majorant. -/
theorem abs_ndWeakEmpiricalError_ndPhaseOrbit_le_endpointDbar
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) (N : ℕ) (hN : 0 < N)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndWeakEmpiricalError N (ndPhaseOrbit phi) t| ≤
      ndEndpointDbar c kappa N := by
  by_cases hN1 : N = 1
  · subst N
    rw [ndEndpointDbar_one hPhase.c_pos]
    exact abs_ndWeakEmpiricalError_le_one 1 (ndPhaseOrbit phi) t ht
  · have hNgt : 1 < N := by omega
    unfold ndEndpointDbar
    apply le_min
    · exact abs_ndWeakEmpiricalError_le_one N (ndPhaseOrbit phi) t ht
    · exact
        abs_ndWeakEmpiricalError_ndPhaseOrbit_le_uncapped_of_one_lt
          hPhase phi hNgt t ht

/-- The source-locked dual endpoint interface consumed by localized Koksma. -/
theorem ndPhaseOrbit_strictWeakEndpointDiscrepancyLE
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) (N : ℕ) (hN : 0 < N) :
    ndStrictWeakEndpointDiscrepancyLE N (ndPhaseOrbit phi)
      (ndEndpointDbar c kappa N) := by
  intro t ht
  exact ⟨
    abs_ndStrictEmpiricalError_ndPhaseOrbit_le_endpointDbar
      hPhase phi N hN t ht,
    abs_ndWeakEmpiricalError_ndPhaseOrbit_le_endpointDbar
      hPhase phi N hN t ht⟩

/-- The endpoint majorant is nonnegative at every natural input. -/
theorem ndEndpointDbar_nonneg
    {c kappa : ℝ} (hPhase : PhaseGap c kappa) (N : ℕ) :
    0 ≤ ndEndpointDbar c kappa N := by
  unfold ndEndpointDbar
  apply le_min
  · norm_num
  · exact mul_nonneg (endpointDbar_constant_pos hPhase).le
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The endpoint majorant is nonincreasing on positive natural lengths.
It is intentionally not claimed to be antitone at the totalized input zero. -/
theorem antitoneOn_ndEndpointDbar
    {c kappa : ℝ} (hPhase : PhaseGap c kappa) :
    AntitoneOn (ndEndpointDbar c kappa) (Set.Ici 1) := by
  intro M hM N hN hMN
  unfold ndEndpointDbar
  apply min_le_min le_rfl
  apply mul_le_mul_of_nonneg_left _ (endpointDbar_constant_pos hPhase).le
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hMNreal : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hexp : -1 / kappa ≤ 0 := by
    have hkappa_pos : 0 < kappa := by linarith [hPhase.two_lt_kappa]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hkappa_pos.le
  exact Real.rpow_le_rpow_of_nonpos hMpos hMNreal hexp

end ND
end Erdos1135
