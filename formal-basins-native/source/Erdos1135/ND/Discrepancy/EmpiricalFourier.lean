import Erdos1135.ND.Discrepancy.EmpiricalCDF
import Erdos1135.ND.Discrepancy.Fejer
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Periodic Empirical Errors and Their Fourier Coefficients

This file supplies the sign- and atom-sensitive interface between the finite
empirical CDF and the later Fejer convolution.  The strict centered error is
periodized by an integer ceiling in each summand.  This makes both cyclic
slope inequalities termwise ceiling facts and avoids period-wrap case splits.

Only the strict error is periodized or integrated.  The weak centered error
appears solely as the attained right-limit witness for a positive extremum.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory Set AddCircle

namespace Erdos1135
namespace ND

/-- One periodized strict sawtooth atom.  The ceiling preserves the strict
value at an atom while recording every integer wrap. -/
noncomputable def ndPeriodicStrictAtom (r t : ℝ) : ℝ :=
  (((⌈t - r⌉ : ℤ) : ℝ)) + r - t - 1 / 2

/-- The period-one centered strict empirical error, written as a finite
ceiling sum. -/
noncomputable def ndPeriodicStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
    ndPeriodicStrictAtom (ndUnitRep (x n)) t

/-- The normalized finite empirical average of the circle character at
integer frequency `h`. -/
noncomputable def ndEmpiricalCharacterAverage
    (N : ℕ) (x : ℕ → UnitAddCircle) (h : ℤ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier h (x n)

private theorem ndCeil_sub_eq_strictIndicator
    (r t : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (((⌈t - r⌉ : ℤ) : ℝ)) = if r < t then 1 else 0 := by
  rcases hr with ⟨hr0, hr1⟩
  rcases ht with ⟨ht0, ht1⟩
  by_cases hrt : r < t
  · rw [if_pos hrt]
    simpa using (Int.ceil_eq_on_Ioc' (R := ℝ) 1 (t - r)
      ⟨by norm_num; linarith, by norm_num; linarith⟩)
  · rw [if_neg hrt]
    simpa using (Int.ceil_eq_on_Ioc' (R := ℝ) 0 (t - r)
      ⟨by norm_num; linarith, by norm_num; linarith⟩)

/-- The finite-ceiling empirical error has period one, including for the
empty sample. -/
theorem ndPeriodicStrictEmpiricalError_periodic
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    Function.Periodic (ndPeriodicStrictEmpiricalError N x) 1 := by
  intro t
  unfold ndPeriodicStrictEmpiricalError ndPeriodicStrictAtom
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [show t + 1 - ndUnitRep (x n) =
      (t - ndUnitRep (x n)) + 1 by ring]
  rw [Int.ceil_add_one]
  push_cast
  ring

/-- On the closed fundamental interval, a nonempty finite-ceiling lift is the
checked centered strict empirical error. -/
theorem ndPeriodicStrictEmpiricalError_eq_centeredStrict
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (hN : 0 < N) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ndPeriodicStrictEmpiricalError N x t =
      ndCenteredStrictEmpiricalError N x t := by
  rw [ndCenteredStrictEmpiricalError_eq_sawtoothAverage N x t hN]
  unfold ndPeriodicStrictEmpiricalError ndPeriodicStrictAtom
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [ndCeil_sub_eq_strictIndicator _ _ (ndUnitRep_mem_Ico _) ht]

/-- For a nonempty sample, the periodic strict error is interval integrable
on every finite interval. -/
theorem intervalIntegrable_ndPeriodicStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N)
    (u v : ℝ) :
    IntervalIntegrable (ndPeriodicStrictEmpiricalError N x) volume u v := by
  apply (ndPeriodicStrictEmpiricalError_periodic N x).intervalIntegrable₀
      one_ne_zero
  apply (intervalIntegrable_ndCenteredStrictEmpiricalError N x 0 1).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  filter_upwards [] with t
  intro ht
  rw [uIoc_of_le zero_le_one] at ht
  exact (ndPeriodicStrictEmpiricalError_eq_centeredStrict N x t hN
    ⟨ht.1.le, ht.2⟩).symm

/-- The periodic strict empirical error has exact mean zero on its fundamental
interval. -/
theorem intervalIntegral_ndPeriodicStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) :
    (∫ t in (0 : ℝ)..1, ndPeriodicStrictEmpiricalError N x t) = 0 := by
  rw [show (∫ t in (0 : ℝ)..1, ndPeriodicStrictEmpiricalError N x t) =
      ∫ t in (0 : ℝ)..1, ndCenteredStrictEmpiricalError N x t by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact ndPeriodicStrictEmpiricalError_eq_centeredStrict N x t hN ht]
  exact intervalIntegral_ndCenteredStrictEmpiricalError N x

/-- The finite oriented amplitude controls the strict periodic lift at every
real argument. -/
theorem abs_ndPeriodicStrictEmpiricalError_le_amplitude
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) (t : ℝ) :
    |ndPeriodicStrictEmpiricalError N x t| ≤ ndEmpiricalAmplitude N x := by
  have hshift :=
    (ndPeriodicStrictEmpiricalError_periodic N x).sub_int_mul_eq
      (Int.floor t) (x := t)
  rw [mul_one, Int.self_sub_floor] at hshift
  rw [← hshift]
  rw [ndPeriodicStrictEmpiricalError_eq_centeredStrict N x (Int.fract t) hN
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩]
  exact abs_ndCenteredStrictEmpiricalError_le_amplitude N x _
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

private theorem ndWeakAtom_sub_le_periodic_add
    (r a d : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hd : 0 < d) :
    (if r ≤ a then (1 : ℝ) else 0) + r - a - 1 / 2 - d ≤
      ndPeriodicStrictAtom r (a + d) := by
  rcases hr with ⟨hr0, hr1⟩
  rcases ha with ⟨ha0, ha1⟩
  by_cases hra : r ≤ a
  · have hceilZ : (1 : ℤ) ≤ ⌈a + d - r⌉ := by
      rw [Int.one_le_ceil_iff]
      linarith
    have hceilR : (1 : ℝ) ≤ (((⌈a + d - r⌉ : ℤ) : ℝ)) := by
      exact_mod_cast hceilZ
    simp only [if_pos hra, ndPeriodicStrictAtom]
    linarith
  · have hceilZ : (0 : ℤ) ≤ ⌈a + d - r⌉ := by
      apply Int.ceil_nonneg_of_neg_one_lt
      linarith
    have hceilR : (0 : ℝ) ≤ (((⌈a + d - r⌉ : ℤ) : ℝ)) := by
      exact_mod_cast hceilZ
    simp only [if_neg hra, ndPeriodicStrictAtom]
    linarith

private theorem ndPeriodic_sub_le_strictAtom_add
    (r a d : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hd : 0 ≤ d) :
    ndPeriodicStrictAtom r (a - d) ≤
      (if r < a then (1 : ℝ) else 0) + r - a - 1 / 2 + d := by
  rcases hr with ⟨hr0, hr1⟩
  rcases ha with ⟨ha0, ha1⟩
  by_cases hra : r < a
  · have hceilZ : ⌈a - d - r⌉ ≤ (1 : ℤ) := by
      rw [Int.ceil_le]
      norm_num
      linarith
    have hceilR : (((⌈a - d - r⌉ : ℤ) : ℝ)) ≤ (1 : ℝ) := by
      exact_mod_cast hceilZ
    simp only [if_pos hra, ndPeriodicStrictAtom]
    linarith
  · have hceilZ : ⌈a - d - r⌉ ≤ (0 : ℤ) := by
      rw [Int.ceil_le]
      norm_num
      linarith
    have hceilR : (((⌈a - d - r⌉ : ℤ) : ℝ)) ≤ (0 : ℝ) := by
      exact_mod_cast hceilZ
    simp only [if_neg hra, ndPeriodicStrictAtom]
    linarith

private theorem ndCenteredWeakEmpiricalError_sub_le_periodic_add_of_pos
    (N : ℕ) (x : ℕ → UnitAddCircle) (a d : ℝ)
    (hN : 0 < N) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hd : 0 < d) :
    ndCenteredWeakEmpiricalError N x a - d ≤
      ndPeriodicStrictEmpiricalError N x (a + d) := by
  rw [ndCenteredWeakEmpiricalError_eq_sawtoothAverage N x a hN]
  unfold ndPeriodicStrictEmpiricalError
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let F := fun n : ℕ =>
    (if ndUnitRep (x n) ≤ a then (1 : ℝ) else 0) +
      ndUnitRep (x n) - a - 1 / 2
  calc
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, F n - d =
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (F n - d) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      field_simp [hNr]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          ndPeriodicStrictAtom (ndUnitRep (x n)) (a + d) := by
      gcongr with n hn
      exact ndWeakAtom_sub_le_periodic_add _ _ _
        (ndUnitRep_mem_Ico _) ha hd

/-- A positive weak right-limit propagates forward through the strict
periodic lift.  Positivity of `d` is essential at an atom. -/
theorem ndCenteredWeakEmpiricalError_sub_le_periodic_add
    (N : ℕ) (x : ℕ → UnitAddCircle) (a d : ℝ)
    (hN : 0 < N) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Ioc (0 : ℝ) 1) :
    ndCenteredWeakEmpiricalError N x a - d ≤
      ndPeriodicStrictEmpiricalError N x (a + d) :=
  ndCenteredWeakEmpiricalError_sub_le_periodic_add_of_pos
    N x a d hN ha hd.1

private theorem ndPeriodic_sub_le_centeredStrict_add_of_nonneg
    (N : ℕ) (x : ℕ → UnitAddCircle) (a d : ℝ)
    (hN : 0 < N) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hd : 0 ≤ d) :
    ndPeriodicStrictEmpiricalError N x (a - d) ≤
      ndCenteredStrictEmpiricalError N x a + d := by
  rw [ndCenteredStrictEmpiricalError_eq_sawtoothAverage N x a hN]
  unfold ndPeriodicStrictEmpiricalError
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let F := fun n : ℕ =>
    (if ndUnitRep (x n) < a then (1 : ℝ) else 0) +
      ndUnitRep (x n) - a - 1 / 2
  calc
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          ndPeriodicStrictAtom (ndUnitRep (x n)) (a - d) ≤
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (F n + d) := by
      gcongr with n hn
      exact ndPeriodic_sub_le_strictAtom_add _ _ _
        (ndUnitRep_mem_Ico _) ha hd
    _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, F n + d := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      field_simp [hNr]

/-- A negative strict extremum propagates backward through the strict
periodic lift.  Unlike the weak branch, `d = 0` is allowed. -/
theorem neg_centeredStrict_sub_le_neg_periodic_sub
    (N : ℕ) (x : ℕ → UnitAddCircle) (a d : ℝ)
    (hN : 0 < N) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    -ndCenteredStrictEmpiricalError N x a - d ≤
      -ndPeriodicStrictEmpiricalError N x (a - d) := by
  have h := ndPeriodic_sub_le_centeredStrict_add_of_nonneg
    N x a d hN ha hd.1
  linarith

/-- The real representative character agrees with Mathlib's additive-circle
Fourier monomial. -/
theorem ndCircleChar_ndUnitRep (h : ℤ) (z : UnitAddCircle) :
    ndCircleChar h (ndUnitRep z) = fourier h z := by
  calc
    ndCircleChar h (ndUnitRep z) =
        fourier h ((ndUnitRep z : ℝ) : UnitAddCircle) := by
      rw [fourier_coe_apply]
      rw [ndCircleChar, Real.fourierChar_apply]
      congr 1
      push_cast
      ring
    _ = fourier h z := by
      congr 1
      exact AddCircle.coe_equivIco
        (p := (1 : ℝ)) (a := (0 : ℝ)) (y := z)

/-- Mean centering kills the zero Fourier coefficient, including for the
empty sample. -/
theorem fourierCoeffOn_ndCenteredStrictEmpiricalError_zero
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    fourierCoeffOn zero_lt_one
      (fun t => (ndCenteredStrictEmpiricalError N x t : ℂ)) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_smul, neg_zero, fourier_zero]
  rw [intervalIntegral.integral_ofReal]
  rw [intervalIntegral_ndCenteredStrictEmpiricalError]
  simp

private theorem intervalIntegral_fourier_neg
    (h : ℤ) (hh : h ≠ 0) (a b : ℝ) :
    (∫ t in a..b, fourier (-h) (t : UnitAddCircle)) =
      (1 : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
        (fourier (-h) (b : UnitAddCircle) -
          fourier (-h) (a : UnitAddCircle)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => has_antideriv_at_fourier_neg
      (T := (1 : ℝ)) (Fact.mk zero_lt_one) hh t)]
  · norm_num
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

private theorem intervalIntegral_fourier_neg_unit
    (h : ℤ) (hh : h ≠ 0) :
    (∫ t in (0 : ℝ)..1, fourier (-h) (t : UnitAddCircle)) = 0 := by
  rw [intervalIntegral_fourier_neg h hh]
  have hcoe :
      ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
    simpa using (AddCircle.coe_add_period (1 : ℝ) (0 : ℝ))
  rw [hcoe, sub_self, mul_zero]

private theorem intervalIntegral_strictIndicator_mul_fourier
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (h : ℤ) (hh : h ≠ 0) :
    (∫ t in (0 : ℝ)..1,
      fourier (-h) (t : UnitAddCircle) *
        (if r < t then (1 : ℂ) else 0)) =
      (1 : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
        (1 - fourier (-h) (r : UnitAddCircle)) := by
  let e : ℝ → ℂ := fun t => fourier (-h) (t : UnitAddCircle)
  have he : IntervalIntegrable e volume 0 1 :=
    Continuous.intervalIntegrable (by unfold e; fun_prop) _ _
  have hind : IntervalIntegrable
      (Set.indicator {u : ℝ | u ≤ r} e) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact ((intervalIntegrable_iff.mp he)).indicator measurableSet_Iic
  have hfun :
      (fun t : ℝ => e t * (if r < t then (1 : ℂ) else 0)) =
        fun t => e t - Set.indicator {u : ℝ | u ≤ r} e t := by
    funext t
    by_cases hrt : r < t
    · simp [hrt, not_le.mpr hrt]
    · simp [hrt, le_of_not_gt hrt]
  change (∫ t in (0 : ℝ)..1,
      e t * (if r < t then (1 : ℂ) else 0)) = _
  rw [hfun, intervalIntegral.integral_sub he hind,
    intervalIntegral.integral_indicator hr]
  rw [show (∫ t in (0 : ℝ)..1, e t) = 0 by
    exact intervalIntegral_fourier_neg_unit h hh]
  rw [show (∫ t in (0 : ℝ)..r, e t) =
      (1 : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
        (fourier (-h) (r : UnitAddCircle) - 1) by
    rw [intervalIntegral_fourier_neg h hh]
    simp]
  ring

private theorem fourierCoeffOn_const_of_ne_zero
    (h : ℤ) (hh : h ≠ 0) (c : ℂ) :
    fourierCoeffOn zero_lt_one (fun _ : ℝ => c) h = 0 := by
  have hzero :
      fourierCoeffOn zero_lt_one (fun _ : ℝ => (0 : ℂ)) h = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp
  rw [fourierCoeffOn_of_hasDerivAt zero_lt_one hh
    (f' := fun _ : ℝ => (0 : ℂ))]
  · simp [hzero]
  · intro t ht
    exact hasDerivAt_const t c
  · exact intervalIntegrable_const

private theorem hasDerivAt_empiricalAffine (r t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((r - s - 1 / 2 : ℝ) : ℂ)) (-1 : ℂ) t := by
  have hreal := ((hasDerivAt_id t).const_sub r).sub_const (1 / 2)
  convert hreal.ofReal_comp using 1 <;> norm_num

private theorem fourierCoeffOn_empiricalAffine
    (r : ℝ) (h : ℤ) (hh : h ≠ 0) :
    fourierCoeffOn zero_lt_one
      (fun t : ℝ => ((r - t - 1 / 2 : ℝ) : ℂ)) h =
      (1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) := by
  rw [fourierCoeffOn_of_hasDerivAt zero_lt_one hh
    (f' := fun _ : ℝ => (-1 : ℂ))]
  · rw [fourierCoeffOn_const_of_ne_zero h hh (-1)]
    simp
  · intro t ht
    exact hasDerivAt_empiricalAffine r t
  · exact intervalIntegrable_const

private theorem intervalIntegral_empiricalAffine_mul_fourier
    (r : ℝ) (h : ℤ) (hh : h ≠ 0) :
    (∫ t in (0 : ℝ)..1,
      fourier (-h) (t : UnitAddCircle) *
        ((r - t - 1 / 2 : ℝ) : ℂ)) =
      (1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) := by
  have hc := fourierCoeffOn_empiricalAffine r h hh
  rw [fourierCoeffOn_eq_integral] at hc
  norm_num at hc ⊢
  exact hc

private theorem intervalIntegrable_empiricalSawtooth_mul_fourier
    (r : ℝ) (h : ℤ) :
    IntervalIntegrable
      (fun t : ℝ => fourier (-h) (t : UnitAddCircle) *
        (((if r < t then (1 : ℝ) else 0) + r - t - 1 / 2 : ℝ) : ℂ))
      volume 0 1 := by
  let e : ℝ → ℂ := fun t => fourier (-h) (t : UnitAddCircle)
  have he : IntervalIntegrable e volume 0 1 :=
    Continuous.intervalIntegrable (by unfold e; fun_prop) _ _
  have hind : IntervalIntegrable
      (Set.indicator {u : ℝ | u ≤ r} e) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact ((intervalIntegrable_iff.mp he)).indicator measurableSet_Iic
  have htail : IntervalIntegrable
      (fun t : ℝ => e t * (if r < t then (1 : ℂ) else 0))
      volume 0 1 := by
    apply (he.sub hind).congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [] with t
    intro ht
    by_cases hrt : r < t
    · simp [hrt, not_le.mpr hrt]
    · simp [hrt, le_of_not_gt hrt]
  have haff : IntervalIntegrable
      (fun t : ℝ => e t * ((r - t - 1 / 2 : ℝ) : ℂ))
      volume 0 1 :=
    Continuous.intervalIntegrable (by unfold e; fun_prop) _ _
  apply (htail.add haff).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  filter_upwards [] with t
  intro ht
  change
    e t * (if r < t then (1 : ℂ) else 0) +
        e t * ((r - t - 1 / 2 : ℝ) : ℂ) =
      e t *
        (((if r < t then (1 : ℝ) else 0) + r - t - 1 / 2 : ℝ) : ℂ)
  by_cases hrt : r < t
  · simp only [if_pos hrt]
    push_cast
    ring
  · simp only [if_neg hrt]
    push_cast
    ring

private theorem intervalIntegral_empiricalSawtooth_mul_fourier
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (h : ℤ) (hh : h ≠ 0) :
    (∫ t in (0 : ℝ)..1,
      fourier (-h) (t : UnitAddCircle) *
        (((if r < t then (1 : ℝ) else 0) + r - t - 1 / 2 : ℝ) : ℂ)) =
      fourier (-h) (r : UnitAddCircle) /
        (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) := by
  let e : ℝ → ℂ := fun t => fourier (-h) (t : UnitAddCircle)
  let tail : ℝ → ℂ :=
    fun t => e t * (if r < t then (1 : ℂ) else 0)
  let aff : ℝ → ℂ :=
    fun t => e t * ((r - t - 1 / 2 : ℝ) : ℂ)
  have he : IntervalIntegrable e volume 0 1 :=
    Continuous.intervalIntegrable (by unfold e; fun_prop) _ _
  have hind : IntervalIntegrable
      (Set.indicator {u : ℝ | u ≤ r} e) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact ((intervalIntegrable_iff.mp he)).indicator measurableSet_Iic
  have htail : IntervalIntegrable tail volume 0 1 := by
    apply (he.sub hind).congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [] with t
    intro ht
    unfold tail
    by_cases hrt : r < t
    · simp [hrt, not_le.mpr hrt]
    · simp [hrt, le_of_not_gt hrt]
  have haff : IntervalIntegrable aff volume 0 1 :=
    Continuous.intervalIntegrable (by unfold aff e; fun_prop) _ _
  have hsplit :
      (fun t : ℝ => e t *
        (((if r < t then (1 : ℝ) else 0) + r - t - 1 / 2 : ℝ) : ℂ)) =
        fun t => tail t + aff t := by
    funext t
    unfold tail aff
    by_cases hrt : r < t <;> simp [hrt] <;> ring
  change (∫ t in (0 : ℝ)..1, e t *
      (((if r < t then (1 : ℝ) else 0) + r - t - 1 / 2 : ℝ) : ℂ)) = _
  rw [hsplit, intervalIntegral.integral_add htail haff]
  rw [show (∫ t in (0 : ℝ)..1, tail t) =
      (1 : ℂ) / (-2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) *
        (1 - fourier (-h) (r : UnitAddCircle)) by
    exact intervalIntegral_strictIndicator_mul_fourier r hr h hh]
  rw [show (∫ t in (0 : ℝ)..1, aff t) =
      (1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) by
    exact intervalIntegral_empiricalAffine_mul_fourier r h hh]
  ring

/-- At a nonzero frequency, Mathlib's Fourier coefficient convention gives
the empirical average at the opposite frequency divided by `2 * pi * I * h`.
The opposite sign is load-bearing: `fourierCoeffOn ... h` integrates against
`fourier (-h)`. -/
theorem fourierCoeffOn_ndCenteredStrictEmpiricalError_of_ne_zero
    (N : ℕ) (x : ℕ → UnitAddCircle) (h : ℤ)
    (hN : 0 < N) (hh : h ≠ 0) :
    fourierCoeffOn zero_lt_one
      (fun t => (ndCenteredStrictEmpiricalError N x t : ℂ)) h =
      ndEmpiricalCharacterAverage N x (-h) /
        (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) := by
  have hdirect :
      (∫ t in (0 : ℝ)..1,
        fourier (-h) (t : UnitAddCircle) *
          (ndCenteredStrictEmpiricalError N x t : ℂ)) =
        ndEmpiricalCharacterAverage N x (-h) /
          (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) := by
    calc
      (∫ t in (0 : ℝ)..1,
          fourier (-h) (t : UnitAddCircle) *
            (ndCenteredStrictEmpiricalError N x t : ℂ)) =
          ∫ t in (0 : ℝ)..1,
            (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
              fourier (-h) (t : UnitAddCircle) *
                ((((if ndUnitRep (x n) < t then (1 : ℝ) else 0) +
                  ndUnitRep (x n) - t - 1 / 2 : ℝ) : ℂ)) := by
            apply intervalIntegral.integral_congr
            intro t ht
            dsimp only
            rw [ndCenteredStrictEmpiricalError_eq_sawtoothAverage
              N x t hN]
            push_cast
            rw [← Finset.mul_sum]
            ring
      _ = (N : ℂ)⁻¹ *
          ∫ t in (0 : ℝ)..1,
            ∑ n ∈ Finset.range N,
              fourier (-h) (t : UnitAddCircle) *
                ((((if ndUnitRep (x n) < t then (1 : ℝ) else 0) +
                  ndUnitRep (x n) - t - 1 / 2 : ℝ) : ℂ)) := by
            exact intervalIntegral.integral_const_mul _ _
      _ = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          ∫ t in (0 : ℝ)..1,
            fourier (-h) (t : UnitAddCircle) *
              ((((if ndUnitRep (x n) < t then (1 : ℝ) else 0) +
                ndUnitRep (x n) - t - 1 / 2 : ℝ) : ℂ)) := by
            rw [intervalIntegral.integral_finset_sum]
            intro n hn
            exact intervalIntegrable_empiricalSawtooth_mul_fourier
              (ndUnitRep (x n)) h
      _ = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          fourier (-h) ((ndUnitRep (x n) : ℝ) : UnitAddCircle) /
            (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro n hn
            exact intervalIntegral_empiricalSawtooth_mul_fourier
              (ndUnitRep (x n))
              ⟨(ndUnitRep_mem_Ico _).1, (ndUnitRep_mem_Ico _).2.le⟩
              h hh
      _ = ndEmpiricalCharacterAverage N x (-h) /
          (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) := by
            unfold ndEmpiricalCharacterAverage
            have hcoe : ∀ n : ℕ,
                fourier (-h)
                    ((ndUnitRep (x n) : ℝ) : UnitAddCircle) =
                  fourier (-h) (x n) := by
              intro n
              congr 1
              exact AddCircle.coe_equivIco
                (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x n)
            simp_rw [hcoe]
            simp_rw [div_eq_mul_inv]
            rw [← Finset.sum_mul]
            ring
  rw [fourierCoeffOn_eq_integral]
  norm_num at hdirect ⊢
  exact hdirect

/-- Replacing the raw strict error by its finite-ceiling periodization does
not change any Fourier coefficient for a nonempty sample. -/
theorem fourierCoeffOn_ndPeriodicStrictEmpiricalError_eq
    (N : ℕ) (x : ℕ → UnitAddCircle) (h : ℤ) (hN : 0 < N) :
    fourierCoeffOn zero_lt_one
      (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ)) h =
      fourierCoeffOn zero_lt_one
        (fun t => (ndCenteredStrictEmpiricalError N x t : ℂ)) h := by
  apply congrFun (fourierCoeffOn_congr_ae zero_lt_one ?_) h
  apply (ae_restrict_iff' measurableSet_Ioc).2
  filter_upwards [] with t
  intro ht
  exact congrArg Complex.ofReal
    (ndPeriodicStrictEmpiricalError_eq_centeredStrict N x t hN
      ⟨ht.1.le, ht.2⟩)

/-- The strict periodization has the same explicit nonzero Fourier
coefficient as the raw centered error. -/
theorem fourierCoeffOn_ndPeriodicStrictEmpiricalError_of_ne_zero
    (N : ℕ) (x : ℕ → UnitAddCircle) (h : ℤ)
    (hN : 0 < N) (hh : h ≠ 0) :
    fourierCoeffOn zero_lt_one
      (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ)) h =
      ndEmpiricalCharacterAverage N x (-h) /
        (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ)) := by
  rw [fourierCoeffOn_ndPeriodicStrictEmpiricalError_eq N x h hN]
  exact fourierCoeffOn_ndCenteredStrictEmpiricalError_of_ne_zero
    N x h hN hh

/-- The zero Fourier mode of the strict periodization vanishes for a
nonempty sample. -/
theorem fourierCoeffOn_ndPeriodicStrictEmpiricalError_zero
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) :
    fourierCoeffOn zero_lt_one
      (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ)) 0 = 0 := by
  rw [fourierCoeffOn_ndPeriodicStrictEmpiricalError_eq N x 0 hN]
  exact fourierCoeffOn_ndCenteredStrictEmpiricalError_zero N x

/-- At positive natural frequency `q`, the coefficient at `-q` has the exact
norm consumed by the finite Erdos--Turan argument. -/
theorem norm_fourierCoeffOn_ndCenteredStrictEmpiricalError_neg_nat
    (N q : ℕ) (x : ℕ → UnitAddCircle)
    (hN : 0 < N) (hq : 0 < q) :
    ‖fourierCoeffOn zero_lt_one
      (fun t => (ndCenteredStrictEmpiricalError N x t : ℂ))
      (-(q : ℤ))‖ =
      ‖ndEmpiricalCharacterAverage N x (q : ℤ)‖ /
        (2 * Real.pi * (q : ℝ)) := by
  rw [fourierCoeffOn_ndCenteredStrictEmpiricalError_of_ne_zero
    N x (-(q : ℤ)) hN]
  · simp only [neg_neg]
    rw [norm_div]
    congr 1
    rw [norm_mul, norm_mul, norm_mul]
    rw [Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, Complex.norm_intCast]
    norm_num
  · exact neg_ne_zero.mpr (by exact_mod_cast hq.ne')

/-- The positive-frequency norm formula is unchanged by the strict
periodization. -/
theorem norm_fourierCoeffOn_ndPeriodicStrictEmpiricalError_neg_nat
    (N q : ℕ) (x : ℕ → UnitAddCircle)
    (hN : 0 < N) (hq : 0 < q) :
    ‖fourierCoeffOn zero_lt_one
      (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
      (-(q : ℤ))‖ =
      ‖ndEmpiricalCharacterAverage N x (q : ℤ)‖ /
        (2 * Real.pi * (q : ℝ)) := by
  rw [fourierCoeffOn_ndPeriodicStrictEmpiricalError_eq
    N x (-(q : ℤ)) hN]
  exact norm_fourierCoeffOn_ndCenteredStrictEmpiricalError_neg_nat
    N q x hN hq

end ND
end Erdos1135
