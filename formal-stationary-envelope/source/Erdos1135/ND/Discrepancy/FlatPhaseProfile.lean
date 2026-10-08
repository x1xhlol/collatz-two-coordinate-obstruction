import Erdos1135.ND.Discrepancy.PhaseLattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Flat A5 Phase Profile

This file builds the literal flat A5 phase profile from the checked open-lattice
count.  A finite layer-cake identity turns the coefficient-one weak-endpoint
count estimate into the exact flat-profile prefix bound needed by the
zero-head Abel consumer.
-/

open scoped BigOperators
open AddCircle
open MeasureTheory

namespace Erdos1135
namespace ND

/-- The frozen flat A5 phase profile on a real representative `t`.
Both lattice boundaries remain strict. -/
noncomputable def ndA5FlatPhaseProfile (beta t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 3,
    let u := ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2)
    if 0 < u ∧ u < beta then Real.exp u else 0

/-- The exact deterministic mean of the flat A5 profile. -/
noncomputable def ndA5FlatPhaseMean (beta : ℝ) : ℝ :=
  (Real.exp beta - 1) / Real.log 2

/-- The flat A5 profile centered at its exact deterministic mean. -/
noncomputable def ndA5CenteredFlatPhaseProfile (beta t : ℝ) : ℝ :=
  ndA5FlatPhaseProfile beta t - ndA5FlatPhaseMean beta

private theorem intervalIntegrable_exp_mul_openCell
    (u a b : ℝ) :
    IntervalIntegrable
      (fun r : ℝ => Real.exp r *
        (if 0 < u ∧ u < r then (1 : ℝ) else 0))
      volume a b := by
  by_cases hu : 0 < u
  · have hfun :
        (fun r : ℝ => Real.exp r *
          (if 0 < u ∧ u < r then (1 : ℝ) else 0)) =
          fun r : ℝ => Set.indicator (Set.Ioi u) Real.exp r := by
      funext r
      by_cases hur : u < r <;> simp [hu, hur]
    rw [hfun, intervalIntegrable_iff]
    exact ((intervalIntegrable_iff.mp
      (Real.continuous_exp.intervalIntegrable a b))).indicator measurableSet_Ioi
  · simp [hu]

private theorem flatCell_layerCake
    (beta u : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp beta * (if 0 < u ∧ u < beta then (1 : ℝ) else 0) -
        (∫ b in (0 : ℝ)..beta,
          Real.exp b * (if 0 < u ∧ u < b then (1 : ℝ) else 0)) =
      if 0 < u ∧ u < beta then Real.exp u else 0 := by
  by_cases hu : 0 < u
  · by_cases hubeta : u < beta
    · have hfun :
          (fun b : ℝ => Real.exp b *
            (if 0 < u ∧ u < b then (1 : ℝ) else 0)) =
            fun b : ℝ => Real.exp b -
              Set.indicator (Set.Iic u) Real.exp b := by
        funext b
        by_cases hub : u < b
        · simp [hu, hub, not_le.mpr hub]
        · simp [hu, hub, le_of_not_gt hub]
      have hind : IntervalIntegrable
          (fun b : ℝ => Set.indicator (Set.Iic u) Real.exp b)
          volume 0 beta := by
        rw [intervalIntegrable_iff]
        exact ((intervalIntegrable_iff.mp
          (Real.continuous_exp.intervalIntegrable 0 beta))).indicator measurableSet_Iic
      have hint :
          (∫ b in (0 : ℝ)..beta,
            Real.exp b * (if 0 < u ∧ u < b then (1 : ℝ) else 0)) =
            Real.exp beta - Real.exp u := by
        have hind_value :
            (∫ b in (0 : ℝ)..beta,
              Set.indicator (Set.Iic u) Real.exp b) =
              ∫ b in (0 : ℝ)..u, Real.exp b := by
          exact intervalIntegral.integral_indicator (μ := volume)
            (f := Real.exp) (a₁ := 0) (a₂ := u) (a₃ := beta)
            ⟨hu.le, hubeta.le⟩
        rw [hfun, intervalIntegral.integral_sub
          (Real.continuous_exp.intervalIntegrable 0 beta) hind]
        rw [hind_value]
        rw [integral_exp, integral_exp]
        simp
      rw [hint]
      simp [hu, hubeta]
    · have hbetau : beta ≤ u := le_of_not_gt hubeta
      have hint :
          (∫ b in (0 : ℝ)..beta,
            Real.exp b * (if 0 < u ∧ u < b then (1 : ℝ) else 0)) = 0 := by
        calc
          (∫ b in (0 : ℝ)..beta,
              Real.exp b *
                (if 0 < u ∧ u < b then (1 : ℝ) else 0)) =
              ∫ _b in (0 : ℝ)..beta, (0 : ℝ) := by
                apply intervalIntegral.integral_congr
                intro b hb
                rw [Set.uIcc_of_le hbeta] at hb
                have hbu : b ≤ u := hb.2.trans hbetau
                simp [hu, not_lt_of_ge hbu]
          _ = 0 := intervalIntegral.integral_zero
      rw [hint]
      simp [hu, hubeta]
  · simp [hu]

private theorem intervalIntegrable_exp_mul_ndA5OpenLatticeCount
    (t a b : ℝ) :
    IntervalIntegrable
      (fun r : ℝ => Real.exp r * ndA5OpenLatticeCount r t)
      volume a b := by
  have hsum : IntervalIntegrable
      (fun r : ℝ =>
        ∑ k ∈ Finset.range 3,
          Real.exp r *
            (if 0 < ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) ∧
                ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) < r
              then (1 : ℝ) else 0))
      volume a b :=
    IntervalIntegrable.sum (Finset.range 3) fun k hk =>
      intervalIntegrable_exp_mul_openCell
        ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) a b
  simpa only [ndA5OpenLatticeCount, Finset.mul_sum] using hsum

private theorem ndA5FlatPhaseProfile_eq_layerCake
    (beta t : ℝ) (hbeta : 0 ≤ beta) :
    ndA5FlatPhaseProfile beta t =
      Real.exp beta * ndA5OpenLatticeCount beta t -
        ∫ b in (0 : ℝ)..beta,
          Real.exp b * ndA5OpenLatticeCount b t := by
  unfold ndA5FlatPhaseProfile ndA5OpenLatticeCount
  rw [Finset.mul_sum]
  have hint :
      (∫ b in (0 : ℝ)..beta,
        Real.exp b *
          ∑ k ∈ Finset.range 3,
            if 0 < ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) ∧
                ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) < b
              then (1 : ℝ) else 0) =
        ∑ k ∈ Finset.range 3,
          ∫ b in (0 : ℝ)..beta,
            Real.exp b *
              (if 0 < ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) ∧
                  ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) < b
                then (1 : ℝ) else 0) := by
    rw [show
      (fun b : ℝ =>
        Real.exp b *
          ∑ k ∈ Finset.range 3,
            if 0 < ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) ∧
                ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) < b
              then (1 : ℝ) else 0) =
      (fun b : ℝ =>
        ∑ k ∈ Finset.range 3,
          Real.exp b *
            (if 0 < ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) ∧
                ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) < b
              then (1 : ℝ) else 0)) by
        funext b
        rw [Finset.mul_sum]]
    rw [intervalIntegral.integral_finset_sum]
    intro k hk
    exact intervalIntegrable_exp_mul_openCell
      ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) 0 beta
  rw [hint, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact (flatCell_layerCake beta
    ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) hbeta).symm

private theorem intervalIntegral_exp_mul_id (beta : ℝ) :
    (∫ b in (0 : ℝ)..beta, Real.exp b * b) =
      beta * Real.exp beta - Real.exp beta + 1 := by
  have hderiv : ∀ b : ℝ,
      HasDerivAt (fun r : ℝ => (r - 1) * Real.exp r)
        (Real.exp b * b) b := by
    intro b
    convert ((hasDerivAt_id b).sub_const 1).mul
      (Real.hasDerivAt_exp b) using 1
    all_goals simp only [id_eq]
    all_goals ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun b hb => hderiv b)]
  · simp
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The centered flat profile is the exact finite layer cake of the checked
open-lattice count. -/
theorem ndA5CenteredFlatPhaseProfile_eq_layerCake
    (beta t : ℝ) (hbeta : 0 ≤ beta) :
    ndA5CenteredFlatPhaseProfile beta t =
      Real.exp beta *
          (ndA5OpenLatticeCount beta t - beta / Real.log 2) -
        ∫ b in (0 : ℝ)..beta,
          Real.exp b *
            (ndA5OpenLatticeCount b t - b / Real.log 2) := by
  have hlinear : IntervalIntegrable
      (fun b : ℝ => Real.exp b * (b / Real.log 2))
      volume 0 beta := by
    exact (Real.continuous_exp.mul
      (continuous_id.div_const _)).intervalIntegrable 0 beta
  have hsplit :
      (∫ b in (0 : ℝ)..beta,
        Real.exp b *
          (ndA5OpenLatticeCount b t - b / Real.log 2)) =
        (∫ b in (0 : ℝ)..beta,
          Real.exp b * ndA5OpenLatticeCount b t) -
        ∫ b in (0 : ℝ)..beta,
          Real.exp b * (b / Real.log 2) := by
    rw [show
      (fun b : ℝ => Real.exp b *
        (ndA5OpenLatticeCount b t - b / Real.log 2)) =
      (fun b : ℝ => Real.exp b * ndA5OpenLatticeCount b t -
        Real.exp b * (b / Real.log 2)) by
        funext b
        ring]
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_exp_mul_ndA5OpenLatticeCount t 0 beta)
      hlinear]
  have hmoment :
      (∫ b in (0 : ℝ)..beta,
        Real.exp b * (b / Real.log 2)) =
        (beta * Real.exp beta - Real.exp beta + 1) / Real.log 2 := by
    rw [show
      (fun b : ℝ => Real.exp b * (b / Real.log 2)) =
        fun b : ℝ => (Real.exp b * b) / Real.log 2 by
          funext b
          ring]
    rw [intervalIntegral.integral_div, intervalIntegral_exp_mul_id]
  unfold ndA5CenteredFlatPhaseProfile ndA5FlatPhaseMean
  rw [ndA5FlatPhaseProfile_eq_layerCake beta t hbeta, hsplit, hmoment]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

private theorem intervalIntegrable_flatKernel
    (beta a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        if 0 < u ∧ u < beta then Real.exp u else 0)
      volume a b := by
  have hfun :
      (fun u : ℝ =>
        if 0 < u ∧ u < beta then Real.exp u else 0) =
      Set.indicator (Set.Ioo (0 : ℝ) beta) Real.exp := by
    funext u
    by_cases h : u ∈ Set.Ioo (0 : ℝ) beta
    · rw [Set.indicator_of_mem (s := Set.Ioo (0 : ℝ) beta)
        (a := u) h Real.exp]
      simp [h.1, h.2]
    · rw [Set.indicator_of_notMem (s := Set.Ioo (0 : ℝ) beta)
        (a := u) h Real.exp]
      have hnot : ¬(0 < u ∧ u < beta) := by
        simpa [Set.mem_Ioo] using h
      simp [hnot]
  rw [hfun, intervalIntegrable_iff]
  exact ((intervalIntegrable_iff.mp
    (Real.continuous_exp.intervalIntegrable a b))).indicator
      measurableSet_Ioo

private theorem intervalIntegrable_flatAffineCell
    (beta a L r s : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        if 0 < (a - t) * L ∧ (a - t) * L < beta
        then Real.exp ((a - t) * L) else 0)
      volume r s := by
  let u : ℝ → ℝ := fun t => (a - t) * L
  have hu : Continuous u := by
    dsimp [u]
    fun_prop
  have hfun :
      (fun t : ℝ =>
        if 0 < (a - t) * L ∧ (a - t) * L < beta
        then Real.exp ((a - t) * L) else 0) =
      Set.indicator (u ⁻¹' Set.Ioo (0 : ℝ) beta)
        (fun t : ℝ => Real.exp (u t)) := by
    funext t
    by_cases h : u t ∈ Set.Ioo (0 : ℝ) beta
    · have ht : t ∈ u ⁻¹' Set.Ioo (0 : ℝ) beta := h
      rw [Set.indicator_of_mem (s := u ⁻¹' Set.Ioo (0 : ℝ) beta)
        (a := t) ht]
      simp [u, h.1, h.2]
    · have ht : t ∉ u ⁻¹' Set.Ioo (0 : ℝ) beta := h
      rw [Set.indicator_of_notMem
        (s := u ⁻¹' Set.Ioo (0 : ℝ) beta) (a := t) ht]
      have hnot :
          ¬(0 < (a - t) * L ∧ (a - t) * L < beta) := by
        simpa [u, Set.mem_Ioo] using h
      simp [hnot]
  rw [hfun, intervalIntegrable_iff]
  exact ((intervalIntegrable_iff.mp
    ((Real.continuous_exp.comp hu).intervalIntegrable r s))).indicator
      (measurableSet_Ioo.preimage hu.measurable)

private theorem mul_intervalIntegral_flatAffineCell
    (beta a L : ℝ) :
    L * (∫ t in (0 : ℝ)..1,
      if 0 < (a - t) * L ∧ (a - t) * L < beta
      then Real.exp ((a - t) * L) else 0) =
      ∫ u in (a - 1) * L..a * L,
        if 0 < u ∧ u < beta then Real.exp u else 0 := by
  let F : ℝ → ℝ := fun u =>
    if 0 < u ∧ u < beta then Real.exp u else 0
  have hsub := intervalIntegral.mul_integral_comp_add_mul
    (f := F) (a := (0 : ℝ)) (b := 1) (-L) (a * L)
  have hfun :
      (fun t : ℝ => F (a * L + -L * t)) =
      fun t : ℝ =>
        if 0 < (a - t) * L ∧ (a - t) * L < beta
        then Real.exp ((a - t) * L) else 0 := by
    funext t
    dsimp [F]
    have harg : a * L + -L * t = (a - t) * L := by ring
    rw [harg]
  rw [hfun] at hsub
  calc
    L * (∫ t in (0 : ℝ)..1,
        if 0 < (a - t) * L ∧ (a - t) * L < beta
        then Real.exp ((a - t) * L) else 0) =
        -((-L) * (∫ t in (0 : ℝ)..1,
          if 0 < (a - t) * L ∧ (a - t) * L < beta
          then Real.exp ((a - t) * L) else 0)) := by ring
    _ = -(∫ u in a * L + -L * 0..a * L + -L * 1, F u) := by
      rw [hsub]
    _ = ∫ u in (a - 1) * L..a * L,
        if 0 < u ∧ u < beta then Real.exp u else 0 := by
      rw [intervalIntegral.integral_symm]
      dsimp [F]
      ring_nf

private theorem intervalIntegral_flatKernel_eq
    (beta B : ℝ) (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) :
    (∫ u in (0 : ℝ)..B,
      if 0 < u ∧ u < beta then Real.exp u else 0) =
      ∫ u in (0 : ℝ)..beta, Real.exp u := by
  have hindicator :
      (∫ u in (0 : ℝ)..B,
        Set.indicator (Set.Iic beta) Real.exp u) =
        ∫ u in (0 : ℝ)..beta, Real.exp u := by
    exact intervalIntegral.integral_indicator (μ := volume)
      (f := Real.exp) (a₁ := 0) (a₂ := beta) (a₃ := B)
      ⟨hbeta, hbetaB⟩
  rw [← hindicator]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ beta by
    simp [ae_iff, measure_singleton]] with u hne
  intro hu
  rw [Set.uIoc_of_le (hbeta.trans hbetaB)] at hu
  have hu0 : 0 < u := hu.1
  by_cases hubeta : u < beta
  · have humem : u ∈ Set.Iic beta := hubeta.le
    rw [Set.indicator_of_mem (s := Set.Iic beta) (a := u)
      humem Real.exp]
    simp [hu0, hubeta]
  · have hbeta_u : beta < u :=
      lt_of_le_of_ne (le_of_not_gt hubeta) hne.symm
    have hunmem : u ∉ Set.Iic beta := not_le.mpr hbeta_u
    rw [Set.indicator_of_notMem (s := Set.Iic beta) (a := u)
      hunmem Real.exp]
    simp [hu0, hubeta]

/-- The literal flat A5 profile has the exact frozen period-Fubini mean. -/
theorem intervalIntegral_ndA5FlatPhaseProfile
    (beta : ℝ) (hbeta : beta ∈ Set.Icc (0 : ℝ) 2) :
    (∫ t in (0 : ℝ)..1, ndA5FlatPhaseProfile beta t) =
      ndA5FlatPhaseMean beta := by
  let F : ℝ → ℝ := fun u =>
    if 0 < u ∧ u < beta then Real.exp u else 0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbeta_three_log : beta ≤ 3 * Real.log 2 := by
    have htwo_lt : (2 : ℝ) < 3 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact hbeta.2.trans htwo_lt.le
  have hprofile :
      (∫ t in (0 : ℝ)..1, ndA5FlatPhaseProfile beta t) =
        ∑ k ∈ Finset.range 3,
          ∫ t in (0 : ℝ)..1,
            if 0 < ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) ∧
                ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) < beta
            then Real.exp
              ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2)
            else 0 := by
    unfold ndA5FlatPhaseProfile
    rw [intervalIntegral.integral_finset_sum]
    intro k hk
    exact intervalIntegrable_flatAffineCell beta
      ((k + 1 : ℕ) : ℝ) (Real.log 2) 0 1
  have hconcat :
      (∑ k ∈ Finset.range 3,
        ∫ u in (((((k + 1 : ℕ) : ℝ) - 1) * Real.log 2))..
            (((k + 1 : ℕ) : ℝ) * Real.log 2), F u) =
        ∫ u in (0 : ℝ)..3 * Real.log 2, F u := by
    calc
      (∑ k ∈ Finset.range 3,
          ∫ u in (((((k + 1 : ℕ) : ℝ) - 1) * Real.log 2))..
              (((k + 1 : ℕ) : ℝ) * Real.log 2), F u) =
          ((∫ u in (0 : ℝ)..Real.log 2, F u) +
            ∫ u in Real.log 2..2 * Real.log 2, F u) +
            ∫ u in 2 * Real.log 2..3 * Real.log 2, F u := by
              norm_num [Finset.sum_range_succ]
      _ = (∫ u in (0 : ℝ)..2 * Real.log 2, F u) +
          ∫ u in 2 * Real.log 2..3 * Real.log 2, F u := by
            rw [intervalIntegral.integral_add_adjacent_intervals
              (intervalIntegrable_flatKernel beta 0 (Real.log 2))
              (intervalIntegrable_flatKernel beta (Real.log 2)
                (2 * Real.log 2))]
      _ = ∫ u in (0 : ℝ)..3 * Real.log 2, F u := by
            rw [intervalIntegral.integral_add_adjacent_intervals
              (intervalIntegrable_flatKernel beta 0 (2 * Real.log 2))
              (intervalIntegrable_flatKernel beta (2 * Real.log 2)
                (3 * Real.log 2))]
  have hscaled :
      Real.log 2 *
          (∫ t in (0 : ℝ)..1, ndA5FlatPhaseProfile beta t) =
        ∫ u in (0 : ℝ)..3 * Real.log 2, F u := by
    rw [hprofile, Finset.mul_sum]
    calc
      (∑ k ∈ Finset.range 3,
          Real.log 2 *
            ∫ t in (0 : ℝ)..1,
              if 0 < ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) ∧
                  ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2) < beta
              then Real.exp
                ((((k + 1 : ℕ) : ℝ) - t) * Real.log 2)
              else 0) =
          ∑ k ∈ Finset.range 3,
            ∫ u in (((((k + 1 : ℕ) : ℝ) - 1) * Real.log 2))..
                (((k + 1 : ℕ) : ℝ) * Real.log 2), F u := by
            apply Finset.sum_congr rfl
            intro k hk
            exact mul_intervalIntegral_flatAffineCell beta
              ((k + 1 : ℕ) : ℝ) (Real.log 2)
      _ = ∫ u in (0 : ℝ)..3 * Real.log 2, F u := hconcat
  have hmain :
      Real.log 2 *
          (∫ t in (0 : ℝ)..1, ndA5FlatPhaseProfile beta t) =
        Real.exp beta - 1 := by
    rw [hscaled]
    change (∫ u in (0 : ℝ)..3 * Real.log 2,
      if 0 < u ∧ u < beta then Real.exp u else 0) = _
    rw [intervalIntegral_flatKernel_eq beta (3 * Real.log 2)
      hbeta.1 hbeta_three_log]
    rw [integral_exp]
    simp
  unfold ndA5FlatPhaseMean
  apply (eq_div_iff (ne_of_gt hlog)).2
  simpa [mul_comm] using hmain

private theorem intervalIntegrable_exp_mul_ndA5OpenLatticeCount_centered
    (t a b : ℝ) :
    IntervalIntegrable
      (fun r : ℝ => Real.exp r *
        (ndA5OpenLatticeCount r t - r / Real.log 2))
      volume a b := by
  have hlinear : IntervalIntegrable
      (fun r : ℝ => Real.exp r * (r / Real.log 2))
      volume a b := by
    exact (Real.continuous_exp.mul
      (continuous_id.div_const _)).intervalIntegrable a b
  have hsub :=
    (intervalIntegrable_exp_mul_ndA5OpenLatticeCount t a b).sub hlinear
  apply hsub.congr
  intro r hr
  ring

/-- A strict/weak endpoint discrepancy bound gives the exact flat-profile
prefix coefficient `2*exp(beta)-1`. -/
theorem abs_sum_ndA5CenteredFlatPhaseProfile_le_of_endpoint
    (N : ℕ) (x : ℕ → UnitAddCircle) (D beta : ℝ)
    (hN : 0 < N) (hbeta : beta ∈ Set.Icc (0 : ℝ) 2)
    (hdisc : ndStrictWeakEndpointDiscrepancyLE N x D) :
    |∑ n ∈ Finset.range N,
      ndA5CenteredFlatPhaseProfile beta (ndUnitRep (x n))| ≤
      (2 * Real.exp beta - 1) * (N : ℝ) * D := by
  let S : ℝ → ℝ := fun b =>
    ∑ n ∈ Finset.range N,
      (ndA5OpenLatticeCount b (ndUnitRep (x n)) -
        b / Real.log 2)
  have hsum :
      (∑ n ∈ Finset.range N,
        ndA5CenteredFlatPhaseProfile beta (ndUnitRep (x n))) =
        Real.exp beta * S beta -
          ∫ b in (0 : ℝ)..beta, Real.exp b * S b := by
    calc
      (∑ n ∈ Finset.range N,
          ndA5CenteredFlatPhaseProfile beta (ndUnitRep (x n))) =
          ∑ n ∈ Finset.range N,
            (Real.exp beta *
                (ndA5OpenLatticeCount beta (ndUnitRep (x n)) -
                  beta / Real.log 2) -
              ∫ b in (0 : ℝ)..beta,
                Real.exp b *
                  (ndA5OpenLatticeCount b (ndUnitRep (x n)) -
                    b / Real.log 2)) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact ndA5CenteredFlatPhaseProfile_eq_layerCake beta
              (ndUnitRep (x n)) hbeta.1
      _ = Real.exp beta * S beta -
          ∑ n ∈ Finset.range N,
            ∫ b in (0 : ℝ)..beta,
              Real.exp b *
                (ndA5OpenLatticeCount b (ndUnitRep (x n)) -
                  b / Real.log 2) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = Real.exp beta * S beta -
          ∫ b in (0 : ℝ)..beta,
            ∑ n ∈ Finset.range N,
              Real.exp b *
                (ndA5OpenLatticeCount b (ndUnitRep (x n)) -
                  b / Real.log 2) := by
            rw [intervalIntegral.integral_finset_sum]
            intro n hn
            exact
              intervalIntegrable_exp_mul_ndA5OpenLatticeCount_centered
                (ndUnitRep (x n)) 0 beta
      _ = Real.exp beta * S beta -
          ∫ b in (0 : ℝ)..beta, Real.exp b * S b := by
            congr 1
            apply intervalIntegral.integral_congr
            intro b hb
            dsimp [S]
            rw [Finset.mul_sum]
  have hD : 0 ≤ D :=
    (abs_nonneg (ndWeakEmpiricalError N x 0)).trans
      ((hdisc 0 (by norm_num)).2)
  have hND : 0 ≤ (N : ℝ) * D :=
    mul_nonneg (Nat.cast_nonneg N) hD
  have hterminal : |S beta| ≤ (N : ℝ) * D := by
    exact abs_sum_ndA5OpenLatticeCount_centered_le
      N x D beta hN hbeta hdisc
  have hintegral :
      |∫ b in (0 : ℝ)..beta, Real.exp b * S b| ≤
        (Real.exp beta - 1) * ((N : ℝ) * D) := by
    have hmajor : IntervalIntegrable
        (fun b : ℝ => Real.exp b * ((N : ℝ) * D))
        volume 0 beta := by
      exact (Real.continuous_exp.mul continuous_const).intervalIntegrable
        0 beta
    have hbound := intervalIntegral.norm_integral_le_of_norm_le
      hbeta.1 (f := fun b : ℝ => Real.exp b * S b)
      (g := fun b : ℝ => Real.exp b * ((N : ℝ) * D))
      (Filter.Eventually.of_forall fun b hb => by
        have hb' : b ∈ Set.Icc (0 : ℝ) 2 :=
          ⟨hb.1.le, hb.2.trans hbeta.2⟩
        have hSb : |S b| ≤ (N : ℝ) * D := by
          exact abs_sum_ndA5OpenLatticeCount_centered_le
            N x D b hN hb' hdisc
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos b)]
        exact mul_le_mul_of_nonneg_left hSb (Real.exp_pos b).le)
      hmajor
    rw [intervalIntegral.integral_mul_const, integral_exp] at hbound
    simp only [Real.exp_zero] at hbound
    simpa only [Real.norm_eq_abs] using hbound
  rw [hsum]
  calc
    |Real.exp beta * S beta -
        ∫ b in (0 : ℝ)..beta, Real.exp b * S b| ≤
        |Real.exp beta * S beta| +
          |∫ b in (0 : ℝ)..beta, Real.exp b * S b| :=
      abs_sub _ _
    _ ≤ Real.exp beta * ((N : ℝ) * D) +
        (Real.exp beta - 1) * ((N : ℝ) * D) := by
      apply add_le_add
      · rw [abs_mul, abs_of_pos (Real.exp_pos beta)]
        exact mul_le_mul_of_nonneg_left hterminal (Real.exp_pos beta).le
      · exact hintegral
    _ = (2 * Real.exp beta - 1) * (N : ℝ) * D := by ring

/-- The checked phase-gap socket supplies the flat A5 prefix estimate at every
positive length and arbitrary additive-circle anchor. -/
theorem abs_sum_ndA5CenteredFlatPhaseProfile_ndPhaseOrbit_le_endpointDbar
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (phi : UnitAddCircle) (beta : ℝ)
    (hbeta : beta ∈ Set.Icc (0 : ℝ) 2)
    (N : ℕ) (hN : 0 < N) :
    |∑ n ∈ Finset.range N,
      ndA5CenteredFlatPhaseProfile beta
        (ndUnitRep (ndPhaseOrbit phi n))| ≤
      (2 * Real.exp beta - 1) * (N : ℝ) *
        ndEndpointDbar c kappa N := by
  exact abs_sum_ndA5CenteredFlatPhaseProfile_le_of_endpoint N
    (ndPhaseOrbit phi) (ndEndpointDbar c kappa N) beta hN hbeta
    (ndPhaseOrbit_strictWeakEndpointDiscrepancyLE hPhase phi N hN)

end ND
end Erdos1135
