import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Finite Centered Empirical CDFs

This file fixes the strict and weak empirical-CDF conventions used by the
finite Erdos--Turan argument.  Observations retain their multiplicity in the
indexed filters.  The finite node set is deduplicated only when it is used to
attain the oriented centered amplitude.

The strict CDF is the later periodic integrand.  The weak CDF is kept as a
fundamental-domain companion which records the right limit at an atom.
-/

open scoped BigOperators
open MeasureTheory Set

namespace Erdos1135
namespace ND

/-- The representative of a point of `ℝ / ℤ` in the half-open interval `[0,1)`. -/
noncomputable def ndUnitRep (z : UnitAddCircle) : ℝ :=
  ((AddCircle.equivIco (1 : ℝ) 0) z : ℝ)

/-- The deduplicated finite support of the first `N` observations. -/
noncomputable def ndEmpiricalAtoms
    (N : ℕ) (x : ℕ → UnitAddCircle) : Finset ℝ :=
  (Finset.range N).image (fun n => ndUnitRep (x n))

/-- The mass of the atom at `t`, with observation multiplicity retained. -/
noncomputable def ndEmpiricalAtomMass
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) : ℝ :=
  (N : ℝ)⁻¹ *
    (((((Finset.range N).filter
      (fun n => ndUnitRep (x n) = t)).card : ℕ) : ℝ))

/-- The normalized empirical CDF with the public strict half-open convention. -/
noncomputable def ndStrictEmpiricalCDF
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) : ℝ :=
  (N : ℝ)⁻¹ *
    (((((Finset.range N).filter
      (fun n => ndUnitRep (x n) < t)).card : ℕ) : ℝ))

/-- The normalized weak empirical CDF, used only to record atom right limits. -/
noncomputable def ndWeakEmpiricalCDF
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) : ℝ :=
  (N : ℝ)⁻¹ *
    (((((Finset.range N).filter
      (fun n => ndUnitRep (x n) ≤ t)).card : ℕ) : ℝ))

/-- The strict empirical count error. -/
noncomputable def ndStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) : ℝ :=
  ndStrictEmpiricalCDF N x t - t

/-- The weak empirical count error. -/
noncomputable def ndWeakEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) : ℝ :=
  ndWeakEmpiricalCDF N x t - t

/-- The exact interval mean of either empirical error on `[0,1]`. -/
noncomputable def ndEmpiricalErrorMean
    (N : ℕ) (x : ℕ → UnitAddCircle) : ℝ :=
  (N : ℝ)⁻¹ *
      ∑ n ∈ Finset.range N, (1 - ndUnitRep (x n))
    - 1 / 2

/-- The mean-zero centered strict empirical error. -/
noncomputable def ndCenteredStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) : ℝ :=
  ndStrictEmpiricalError N x t - ndEmpiricalErrorMean N x

/-- The mean-zero centered weak empirical error. -/
noncomputable def ndCenteredWeakEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) : ℝ :=
  ndWeakEmpiricalError N x t - ndEmpiricalErrorMean N x

/-- The finite breakpoint set, including both endpoints of the fundamental domain. -/
noncomputable def ndEmpiricalNodes
    (N : ℕ) (x : ℕ → UnitAddCircle) : Finset ℝ :=
  insert 0 (insert 1 (ndEmpiricalAtoms N x))

/-- Oriented candidate values for the attained centered amplitude. -/
noncomputable def ndEmpiricalExtremalValues
    (N : ℕ) (x : ℕ → UnitAddCircle) : Finset ℝ :=
  (ndEmpiricalNodes N x).image
      (fun t => -ndCenteredStrictEmpiricalError N x t) ∪
    (ndEmpiricalNodes N x).image
      (fun t => ndCenteredWeakEmpiricalError N x t)

private theorem ndEmpiricalExtremalValues_nonempty
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    (ndEmpiricalExtremalValues N x).Nonempty := by
  refine ⟨-ndCenteredStrictEmpiricalError N x 0, ?_⟩
  simp [ndEmpiricalExtremalValues, ndEmpiricalNodes]

/-- The maximum of the finite oriented strict/weak candidate set. -/
noncomputable def ndEmpiricalAmplitude
    (N : ℕ) (x : ℕ → UnitAddCircle) : ℝ :=
  (ndEmpiricalExtremalValues N x).max'
    (ndEmpiricalExtremalValues_nonempty N x)

/-- The chosen representative lies in `[0,1)`. -/
theorem ndUnitRep_mem_Ico (z : UnitAddCircle) :
    ndUnitRep z ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [ndUnitRep] using
    ((AddCircle.equivIco (1 : ℝ) 0) z).property

/-- A real already in `[0,1)` is unchanged by the representative map. -/
theorem ndUnitRep_coe (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ndUnitRep ((t : ℝ) : UnitAddCircle) = t := by
  have ht' : t ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa using ht
  simpa [ndUnitRep] using
    (AddCircle.equivIco_coe_of_mem
      (p := (1 : ℝ)) (a := (0 : ℝ)) ht')

private theorem ndEmpiricalAtomMass_nonneg
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) :
    0 ≤ ndEmpiricalAtomMass N x t := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (Nat.cast_nonneg _)

/-- The weak CDF is the strict CDF plus the full indexed atom mass. -/
theorem ndWeakEmpiricalCDF_eq_strict_add_atomMass
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) :
    ndWeakEmpiricalCDF N x t =
      ndStrictEmpiricalCDF N x t + ndEmpiricalAtomMass N x t := by
  let s := (Finset.range N).filter (fun n => ndUnitRep (x n) < t)
  let e := (Finset.range N).filter (fun n => ndUnitRep (x n) = t)
  have hdisj : Disjoint s e := by
    rw [Finset.disjoint_left]
    intro n hns hne
    simp only [s, Finset.mem_filter] at hns
    simp only [e, Finset.mem_filter] at hne
    linarith
  have hfilter :
      (Finset.range N).filter (fun n => ndUnitRep (x n) ≤ t) = s ∪ e := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_union, s, e]
    constructor
    · rintro ⟨hn, hle⟩
      rcases hle.lt_or_eq with hlt | heq
      · exact Or.inl ⟨hn, hlt⟩
      · exact Or.inr ⟨hn, heq⟩
    · rintro (⟨hn, hlt⟩ | ⟨hn, heq⟩)
      · exact ⟨hn, hlt.le⟩
      · exact ⟨hn, heq.le⟩
  simp only [ndWeakEmpiricalCDF, ndStrictEmpiricalCDF, ndEmpiricalAtomMass]
  rw [hfilter, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

/-- Centering preserves the strict-to-weak atom jump. -/
theorem ndCenteredWeakEmpiricalError_eq_strict_add_atomMass
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) :
    ndCenteredWeakEmpiricalError N x t =
      ndCenteredStrictEmpiricalError N x t + ndEmpiricalAtomMass N x t := by
  unfold ndCenteredWeakEmpiricalError ndCenteredStrictEmpiricalError
  unfold ndWeakEmpiricalError ndStrictEmpiricalError
  rw [ndWeakEmpiricalCDF_eq_strict_add_atomMass]
  ring

/-- Pointwise, the strict centered value never exceeds its weak companion. -/
theorem ndCenteredStrictEmpiricalError_le_weak
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) :
    ndCenteredStrictEmpiricalError N x t ≤
      ndCenteredWeakEmpiricalError N x t := by
  rw [ndCenteredWeakEmpiricalError_eq_strict_add_atomMass]
  exact le_add_of_nonneg_right (ndEmpiricalAtomMass_nonneg N x t)

private theorem ndStrictEmpiricalCDF_ae_eq_weak
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    ∀ᵐ t : ℝ ∂volume,
      ndStrictEmpiricalCDF N x t = ndWeakEmpiricalCDF N x t := by
  let s : Finset ℝ :=
    (Finset.range N).image (fun n => ndUnitRep (x n))
  have hnot : ∀ᵐ t : ℝ ∂volume, t ∉ (s : Set ℝ) :=
    s.finite_toSet.countable.ae_notMem volume
  filter_upwards [hnot] with t ht
  have hfilter :
      (Finset.range N).filter (fun n => ndUnitRep (x n) < t) =
        (Finset.range N).filter (fun n => ndUnitRep (x n) ≤ t) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hlt⟩
      exact ⟨hn, hlt.le⟩
    · rintro ⟨hn, hle⟩
      refine ⟨hn, lt_of_le_of_ne hle ?_⟩
      intro heq
      apply ht
      simp only [s, Finset.coe_image, Set.mem_image]
      exact ⟨n, by simpa using hn, heq⟩
  simp only [ndStrictEmpiricalCDF, ndWeakEmpiricalCDF, hfilter]

/-- The centered strict and weak errors agree away from the finite atom set. -/
theorem ndCenteredStrictEmpiricalError_ae_eq_weak
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    ∀ᵐ t : ℝ ∂volume,
      ndCenteredStrictEmpiricalError N x t =
        ndCenteredWeakEmpiricalError N x t := by
  filter_upwards [ndStrictEmpiricalCDF_ae_eq_weak N x] with t ht
  unfold ndCenteredStrictEmpiricalError ndCenteredWeakEmpiricalError
  unfold ndStrictEmpiricalError ndWeakEmpiricalError
  rw [ht]

private theorem ndStrictIndicator_eq (a : ℝ) :
    (fun t : ℝ => if a < t then (1 : ℝ) else 0) =
      fun t => 1 - Set.indicator {u : ℝ | u ≤ a} (fun _ => (1 : ℝ)) t := by
  funext t
  by_cases h : a < t
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

private theorem intervalIntegrable_ndStrictIndicator
    (a u v : ℝ) :
    IntervalIntegrable (fun t : ℝ => if a < t then (1 : ℝ) else 0)
      volume u v := by
  rw [ndStrictIndicator_eq]
  apply IntervalIntegrable.sub intervalIntegrable_const
  rw [intervalIntegrable_iff]
  exact ((intervalIntegrable_iff.mp intervalIntegrable_const)).indicator
    measurableSet_Iic

private theorem intervalIntegral_ndStrictIndicator
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, if a < t then (1 : ℝ) else 0) = 1 - a := by
  rw [ndStrictIndicator_eq]
  have hind : IntervalIntegrable
      (fun t : ℝ =>
        Set.indicator {u : ℝ | u ≤ a} (fun _ => (1 : ℝ)) t)
      volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact ((intervalIntegrable_iff.mp intervalIntegrable_const)).indicator
      measurableSet_Iic
  rw [intervalIntegral.integral_sub intervalIntegrable_const hind]
  rw [intervalIntegral.integral_indicator ha]
  simp [intervalIntegral.integral_const]

private theorem intervalIntegrable_ndStrictEmpiricalCDF
    (N : ℕ) (x : ℕ → UnitAddCircle) (u v : ℝ) :
    IntervalIntegrable (ndStrictEmpiricalCDF N x) volume u v := by
  have hsum : IntervalIntegrable
      (fun t : ℝ => ∑ n ∈ Finset.range N,
        if ndUnitRep (x n) < t then (1 : ℝ) else 0)
      volume u v := by
    refine (IntervalIntegrable.sum (Finset.range N) fun n hn =>
      intervalIntegrable_ndStrictIndicator (ndUnitRep (x n)) u v).congr ?_
    intro t ht
    simp
  have hmul := hsum.const_mul (N : ℝ)⁻¹
  apply hmul.congr
  intro t ht
  simp [ndStrictEmpiricalCDF]

private theorem intervalIntegrable_ndWeakEmpiricalCDF_unit
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    IntervalIntegrable (ndWeakEmpiricalCDF N x) volume 0 1 := by
  apply (intervalIntegrable_ndStrictEmpiricalCDF N x 0 1).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  filter_upwards [ndStrictEmpiricalCDF_ae_eq_weak N x] with t ht
  intro hmem
  exact ht

private theorem intervalIntegrable_ndStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (u v : ℝ) :
    IntervalIntegrable (ndStrictEmpiricalError N x) volume u v :=
  (intervalIntegrable_ndStrictEmpiricalCDF N x u v).sub
    (continuous_id.intervalIntegrable u v)

private theorem intervalIntegrable_ndWeakEmpiricalError_unit
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    IntervalIntegrable (ndWeakEmpiricalError N x) volume 0 1 :=
  (intervalIntegrable_ndWeakEmpiricalCDF_unit N x).sub
    (continuous_id.intervalIntegrable 0 1)

/-- The centered strict empirical error is integrable on every finite interval. -/
theorem intervalIntegrable_ndCenteredStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) (u v : ℝ) :
    IntervalIntegrable (ndCenteredStrictEmpiricalError N x) volume u v :=
  (intervalIntegrable_ndStrictEmpiricalError N x u v).sub
    intervalIntegrable_const

/-- The exact integral of the strict CDF on the fundamental interval. -/
theorem intervalIntegral_ndStrictEmpiricalCDF
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    (∫ t in (0 : ℝ)..1, ndStrictEmpiricalCDF N x t) =
      (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (1 - ndUnitRep (x n)) := by
  calc
    (∫ t in (0 : ℝ)..1, ndStrictEmpiricalCDF N x t) =
        ∫ t in (0 : ℝ)..1,
          (N : ℝ)⁻¹ *
            ∑ n ∈ Finset.range N,
              if ndUnitRep (x n) < t then (1 : ℝ) else 0 := by
          apply intervalIntegral.integral_congr
          intro t ht
          simp [ndStrictEmpiricalCDF]
    _ = (N : ℝ)⁻¹ *
        ∫ t in (0 : ℝ)..1,
          ∑ n ∈ Finset.range N,
            if ndUnitRep (x n) < t then (1 : ℝ) else 0 := by
          rw [intervalIntegral.integral_const_mul]
    _ = (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N,
          ∫ t in (0 : ℝ)..1,
            if ndUnitRep (x n) < t then (1 : ℝ) else 0 := by
          rw [intervalIntegral.integral_finset_sum]
          intro n hn
          exact intervalIntegrable_ndStrictIndicator (ndUnitRep (x n)) 0 1
    _ = (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (1 - ndUnitRep (x n)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          exact intervalIntegral_ndStrictIndicator _
            ⟨(ndUnitRep_mem_Ico _).1, (ndUnitRep_mem_Ico _).2.le⟩

/-- The weak CDF has the same integral as the strict CDF. -/
theorem intervalIntegral_ndWeakEmpiricalCDF
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    (∫ t in (0 : ℝ)..1, ndWeakEmpiricalCDF N x t) =
      (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (1 - ndUnitRep (x n)) := by
  calc
    (∫ t in (0 : ℝ)..1, ndWeakEmpiricalCDF N x t) =
        ∫ t in (0 : ℝ)..1, ndStrictEmpiricalCDF N x t := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [ndStrictEmpiricalCDF_ae_eq_weak N x] with t ht
          intro hmem
          exact ht.symm
    _ = _ := intervalIntegral_ndStrictEmpiricalCDF N x

/-- The exact integral of the strict empirical error. -/
theorem intervalIntegral_ndStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    (∫ t in (0 : ℝ)..1, ndStrictEmpiricalError N x t) =
      ndEmpiricalErrorMean N x := by
  unfold ndStrictEmpiricalError
  rw [intervalIntegral.integral_sub
    (f := ndStrictEmpiricalCDF N x) (g := fun t : ℝ => t)
    (intervalIntegrable_ndStrictEmpiricalCDF N x 0 1)
    (continuous_id.intervalIntegrable 0 1)]
  rw [intervalIntegral_ndStrictEmpiricalCDF, integral_id]
  unfold ndEmpiricalErrorMean
  ring

/-- The exact integral of the weak empirical error. -/
theorem intervalIntegral_ndWeakEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    (∫ t in (0 : ℝ)..1, ndWeakEmpiricalError N x t) =
      ndEmpiricalErrorMean N x := by
  unfold ndWeakEmpiricalError
  rw [intervalIntegral.integral_sub
    (f := ndWeakEmpiricalCDF N x) (g := fun t : ℝ => t)
    (intervalIntegrable_ndWeakEmpiricalCDF_unit N x)
    (continuous_id.intervalIntegrable 0 1)]
  rw [intervalIntegral_ndWeakEmpiricalCDF, integral_id]
  unfold ndEmpiricalErrorMean
  ring

/-- The centered strict empirical error has mean zero. -/
theorem intervalIntegral_ndCenteredStrictEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    (∫ t in (0 : ℝ)..1, ndCenteredStrictEmpiricalError N x t) = 0 := by
  unfold ndCenteredStrictEmpiricalError
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_ndStrictEmpiricalError N x 0 1)
    intervalIntegrable_const]
  rw [intervalIntegral_ndStrictEmpiricalError,
    intervalIntegral.integral_const]
  simp

/-- The centered weak empirical error also has mean zero on `[0,1]`. -/
theorem intervalIntegral_ndCenteredWeakEmpiricalError
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    (∫ t in (0 : ℝ)..1, ndCenteredWeakEmpiricalError N x t) = 0 := by
  unfold ndCenteredWeakEmpiricalError
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_ndWeakEmpiricalError_unit N x)
    intervalIntegrable_const]
  rw [intervalIntegral_ndWeakEmpiricalError,
    intervalIntegral.integral_const]
  simp

/-- The strict CDF vanishes at the left endpoint, including when `N = 0`. -/
theorem ndStrictEmpiricalCDF_zero
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    ndStrictEmpiricalCDF N x 0 = 0 := by
  simp only [ndStrictEmpiricalCDF]
  have hfilter :
      (Finset.range N).filter (fun n => ndUnitRep (x n) < 0) = ∅ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
      iff_false, not_and]
    intro hn
    exact not_lt_of_ge (ndUnitRep_mem_Ico (x n)).1
  rw [hfilter]
  simp

/-- For a nonempty sample, the strict CDF equals one at the right endpoint. -/
theorem ndStrictEmpiricalCDF_one
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) :
    ndStrictEmpiricalCDF N x 1 = 1 := by
  simp only [ndStrictEmpiricalCDF]
  have hfilter :
      (Finset.range N).filter (fun n => ndUnitRep (x n) < 1) =
        Finset.range N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
    intro hn
    exact (ndUnitRep_mem_Ico (x n)).2
  rw [hfilter, Finset.card_range]
  field_simp

/-- For a nonempty sample, the weak CDF also equals one at the right endpoint. -/
theorem ndWeakEmpiricalCDF_one
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) :
    ndWeakEmpiricalCDF N x 1 = 1 := by
  simp only [ndWeakEmpiricalCDF]
  have hfilter :
      (Finset.range N).filter (fun n => ndUnitRep (x n) ≤ 1) =
        Finset.range N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
    intro hn
    exact (ndUnitRep_mem_Ico (x n)).2.le
  rw [hfilter, Finset.card_range]
  field_simp

/-- The centered strict error has matching fundamental-domain endpoints. -/
theorem ndCenteredStrictEmpiricalError_zero_eq_one
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) :
    ndCenteredStrictEmpiricalError N x 0 =
      ndCenteredStrictEmpiricalError N x 1 := by
  unfold ndCenteredStrictEmpiricalError ndStrictEmpiricalError
  rw [ndStrictEmpiricalCDF_zero, ndStrictEmpiricalCDF_one N x hN]
  ring

/-- The weak value at one is the strict value at zero, not the weak right limit at zero. -/
theorem ndCenteredWeakEmpiricalError_one_eq_strict_zero
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) :
    ndCenteredWeakEmpiricalError N x 1 =
      ndCenteredStrictEmpiricalError N x 0 := by
  unfold ndCenteredWeakEmpiricalError ndCenteredStrictEmpiricalError
  unfold ndWeakEmpiricalError ndStrictEmpiricalError
  rw [ndWeakEmpiricalCDF_one N x hN, ndStrictEmpiricalCDF_zero]
  ring

/-- The raw strict error is the difference of two centered strict values. -/
theorem ndStrictEmpiricalError_eq_centered_sub_zero
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) :
    ndStrictEmpiricalError N x t =
      ndCenteredStrictEmpiricalError N x t -
        ndCenteredStrictEmpiricalError N x 0 := by
  unfold ndCenteredStrictEmpiricalError ndStrictEmpiricalError
  rw [ndStrictEmpiricalCDF_zero]
  ring

/-- The centered strict error is the average of its strict sawtooth summands. -/
theorem ndCenteredStrictEmpiricalError_eq_sawtoothAverage
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) (hN : 0 < N) :
    ndCenteredStrictEmpiricalError N x t =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ((if ndUnitRep (x n) < t then (1 : ℝ) else 0) +
          ndUnitRep (x n) - t - 1 / 2) := by
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  unfold ndCenteredStrictEmpiricalError ndStrictEmpiricalError
  simp only [ndStrictEmpiricalCDF, ndEmpiricalErrorMean]
  rw [show
    (((((Finset.range N).filter
      (fun n => ndUnitRep (x n) < t)).card : ℕ) : ℝ)) =
      ∑ n ∈ Finset.range N,
        if ndUnitRep (x n) < t then (1 : ℝ) else 0 by simp]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- The centered weak error is the average of its weak sawtooth summands. -/
theorem ndCenteredWeakEmpiricalError_eq_sawtoothAverage
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) (hN : 0 < N) :
    ndCenteredWeakEmpiricalError N x t =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ((if ndUnitRep (x n) ≤ t then (1 : ℝ) else 0) +
          ndUnitRep (x n) - t - 1 / 2) := by
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  unfold ndCenteredWeakEmpiricalError ndWeakEmpiricalError
  simp only [ndWeakEmpiricalCDF, ndEmpiricalErrorMean]
  rw [show
    (((((Finset.range N).filter
      (fun n => ndUnitRep (x n) ≤ t)).card : ℕ) : ℝ)) =
      ∑ n ∈ Finset.range N,
        if ndUnitRep (x n) ≤ t then (1 : ℝ) else 0 by simp]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

private theorem abs_ndStrictSawtooth_le_half
    (a t : ℝ) (ha : a ∈ Set.Ico (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(if a < t then (1 : ℝ) else 0) + a - t - 1 / 2| ≤ 1 / 2 := by
  rcases ha with ⟨ha0, ha1⟩
  rcases ht with ⟨ht0, ht1⟩
  by_cases h : a < t
  · simp only [if_pos h]
    rw [abs_le]
    constructor <;> linarith
  · simp only [if_neg h, zero_add]
    rw [abs_le]
    constructor <;> linarith [le_of_not_gt h]

private theorem abs_ndWeakSawtooth_le_half
    (a t : ℝ) (ha : a ∈ Set.Ico (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(if a ≤ t then (1 : ℝ) else 0) + a - t - 1 / 2| ≤ 1 / 2 := by
  rcases ha with ⟨ha0, ha1⟩
  rcases ht with ⟨ht0, ht1⟩
  by_cases h : a ≤ t
  · simp only [if_pos h]
    rw [abs_le]
    constructor <;> linarith
  · simp only [if_neg h, zero_add]
    rw [abs_le]
    constructor <;> linarith [lt_of_not_ge h]

/-- The centered strict error is bounded by one half on `[0,1]`, also for `N = 0`. -/
theorem abs_ndCenteredStrictEmpiricalError_le_half
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndCenteredStrictEmpiricalError N x t| ≤ 1 / 2 := by
  by_cases hN : N = 0
  · subst N
    rcases ht with ⟨ht0, ht1⟩
    simp only [ndCenteredStrictEmpiricalError, ndStrictEmpiricalError,
      ndStrictEmpiricalCDF, ndEmpiricalErrorMean, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty, Nat.cast_zero, inv_zero,
      zero_mul, Finset.sum_empty]
    rw [abs_le]
    constructor <;> linarith
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    rw [ndCenteredStrictEmpiricalError_eq_sawtoothAverage N x t hNpos,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    calc
      (N : ℝ)⁻¹ *
          |∑ n ∈ Finset.range N,
            ((if ndUnitRep (x n) < t then (1 : ℝ) else 0) +
              ndUnitRep (x n) - t - 1 / 2)|
        ≤ (N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N,
            |(if ndUnitRep (x n) < t then (1 : ℝ) else 0) +
              ndUnitRep (x n) - t - 1 / 2| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, (1 / 2 : ℝ) := by
            gcongr with n hn
            exact abs_ndStrictSawtooth_le_half _ _
              (ndUnitRep_mem_Ico _) ht
      _ = 1 / 2 := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have hNr : (N : ℝ) ≠ 0 := by
              exact_mod_cast hN
            field_simp

/-- The centered weak error is bounded by one half on `[0,1]`, also for `N = 0`. -/
theorem abs_ndCenteredWeakEmpiricalError_le_half
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndCenteredWeakEmpiricalError N x t| ≤ 1 / 2 := by
  by_cases hN : N = 0
  · subst N
    rcases ht with ⟨ht0, ht1⟩
    simp only [ndCenteredWeakEmpiricalError, ndWeakEmpiricalError,
      ndWeakEmpiricalCDF, ndEmpiricalErrorMean, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty, Nat.cast_zero, inv_zero,
      zero_mul, Finset.sum_empty]
    rw [abs_le]
    constructor <;> linarith
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    rw [ndCenteredWeakEmpiricalError_eq_sawtoothAverage N x t hNpos,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    calc
      (N : ℝ)⁻¹ *
          |∑ n ∈ Finset.range N,
            ((if ndUnitRep (x n) ≤ t then (1 : ℝ) else 0) +
              ndUnitRep (x n) - t - 1 / 2)|
        ≤ (N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N,
            |(if ndUnitRep (x n) ≤ t then (1 : ℝ) else 0) +
              ndUnitRep (x n) - t - 1 / 2| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, (1 / 2 : ℝ) := by
            gcongr with n hn
            exact abs_ndWeakSawtooth_le_half _ _
              (ndUnitRep_mem_Ico _) ht
      _ = 1 / 2 := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have hNr : (N : ℝ) ≠ 0 := by
              exact_mod_cast hN
            field_simp

/-- Every empirical node belongs to the closed fundamental interval. -/
theorem ndEmpiricalNodes_subset_Icc
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    (ndEmpiricalNodes N x : Set ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro b hb
  have hb' : b ∈ ndEmpiricalNodes N x := by
    simpa using hb
  simp only [ndEmpiricalNodes, Finset.mem_insert] at hb'
  rcases hb' with rfl | rfl | hb'
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · simp only [ndEmpiricalAtoms, Finset.mem_image] at hb'
    obtain ⟨n, hn, rfl⟩ := hb'
    exact ⟨(ndUnitRep_mem_Ico _).1, (ndUnitRep_mem_Ico _).2.le⟩

private theorem ndUnitRep_mem_nodes
    (N : ℕ) (x : ℕ → UnitAddCircle) {n : ℕ}
    (hn : n ∈ Finset.range N) :
    ndUnitRep (x n) ∈ ndEmpiricalNodes N x := by
  simp only [ndEmpiricalNodes, Finset.mem_insert, ndEmpiricalAtoms,
    Finset.mem_image]
  exact Or.inr (Or.inr ⟨n, hn, rfl⟩)

private theorem exists_ndEmpirical_predecessor
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) (ht : 0 ≤ t) :
    ∃ a ∈ ndEmpiricalNodes N x, a ≤ t ∧
      (Finset.range N).filter (fun n => ndUnitRep (x n) ≤ a) =
        (Finset.range N).filter (fun n => ndUnitRep (x n) ≤ t) := by
  let candidates :=
    (ndEmpiricalNodes N x).filter (fun a => a ≤ t)
  have hcandidates : candidates.Nonempty := by
    refine ⟨0, ?_⟩
    simp [candidates, ndEmpiricalNodes, ht]
  let a := candidates.max' hcandidates
  have ha_mem_candidates : a ∈ candidates :=
    candidates.max'_mem hcandidates
  have ha_parts := Finset.mem_filter.mp ha_mem_candidates
  refine ⟨a, ha_parts.1, ha_parts.2, ?_⟩
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hn, hna⟩
    exact ⟨hn, hna.trans ha_parts.2⟩
  · rintro ⟨hn, hnt⟩
    refine ⟨hn, ?_⟩
    apply candidates.le_max'
    exact Finset.mem_filter.mpr
      ⟨ndUnitRep_mem_nodes N x hn, hnt⟩

private theorem exists_ndEmpirical_successor
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ) (ht : t ≤ 1) :
    ∃ b ∈ ndEmpiricalNodes N x, t ≤ b ∧
      (Finset.range N).filter (fun n => ndUnitRep (x n) < t) =
        (Finset.range N).filter (fun n => ndUnitRep (x n) < b) := by
  let candidates :=
    (ndEmpiricalNodes N x).filter (fun b => t ≤ b)
  have hcandidates : candidates.Nonempty := by
    refine ⟨1, ?_⟩
    simp [candidates, ndEmpiricalNodes, ht]
  let b := candidates.min' hcandidates
  have hb_mem_candidates : b ∈ candidates :=
    candidates.min'_mem hcandidates
  have hb_parts := Finset.mem_filter.mp hb_mem_candidates
  refine ⟨b, hb_parts.1, hb_parts.2, ?_⟩
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hn, hnt⟩
    exact ⟨hn, hnt.trans_le hb_parts.2⟩
  · rintro ⟨hn, hnb⟩
    refine ⟨hn, ?_⟩
    by_contra hnot
    have htn : t ≤ ndUnitRep (x n) := le_of_not_gt hnot
    have hb_le : b ≤ ndUnitRep (x n) := candidates.min'_le _
      (Finset.mem_filter.mpr
        ⟨ndUnitRep_mem_nodes N x hn, htn⟩)
    exact (not_le_of_gt hnb) hb_le

private theorem neg_ndCenteredStrictEmpiricalError_le_amplitude
    (N : ℕ) (x : ℕ → UnitAddCircle) {b : ℝ}
    (hb : b ∈ ndEmpiricalNodes N x) :
    -ndCenteredStrictEmpiricalError N x b ≤ ndEmpiricalAmplitude N x := by
  apply (ndEmpiricalExtremalValues N x).le_max'
  simp only [ndEmpiricalExtremalValues, Finset.mem_union, Finset.mem_image]
  exact Or.inl ⟨b, hb, rfl⟩

private theorem ndCenteredWeakEmpiricalError_le_amplitude_at_node
    (N : ℕ) (x : ℕ → UnitAddCircle) {a : ℝ}
    (ha : a ∈ ndEmpiricalNodes N x) :
    ndCenteredWeakEmpiricalError N x a ≤ ndEmpiricalAmplitude N x := by
  apply (ndEmpiricalExtremalValues N x).le_max'
  simp only [ndEmpiricalExtremalValues, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨a, ha, rfl⟩

private theorem ndCenteredEmpiricalError_bounds
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    -ndEmpiricalAmplitude N x ≤ ndCenteredStrictEmpiricalError N x t ∧
      ndCenteredStrictEmpiricalError N x t ≤
        ndCenteredWeakEmpiricalError N x t ∧
      ndCenteredWeakEmpiricalError N x t ≤ ndEmpiricalAmplitude N x := by
  obtain ⟨a, ha_nodes, ha_le, ha_filter⟩ :=
    exists_ndEmpirical_predecessor N x t ht.1
  obtain ⟨b, hb_nodes, ht_le_b, hb_filter⟩ :=
    exists_ndEmpirical_successor N x t ht.2
  have hstrict_lower :
      ndCenteredStrictEmpiricalError N x b ≤
        ndCenteredStrictEmpiricalError N x t := by
    have hcdf :
        ndStrictEmpiricalCDF N x t = ndStrictEmpiricalCDF N x b := by
      simp only [ndStrictEmpiricalCDF]
      rw [hb_filter]
    unfold ndCenteredStrictEmpiricalError ndStrictEmpiricalError
    rw [hcdf]
    linarith
  have hweak_upper :
      ndCenteredWeakEmpiricalError N x t ≤
        ndCenteredWeakEmpiricalError N x a := by
    have hcdf :
        ndWeakEmpiricalCDF N x a = ndWeakEmpiricalCDF N x t := by
      simp only [ndWeakEmpiricalCDF]
      rw [ha_filter]
    unfold ndCenteredWeakEmpiricalError ndWeakEmpiricalError
    rw [← hcdf]
    linarith
  have hcross := ndCenteredStrictEmpiricalError_le_weak N x t
  constructor
  · linarith [neg_ndCenteredStrictEmpiricalError_le_amplitude N x hb_nodes]
  · exact ⟨hcross,
      hweak_upper.trans
        (ndCenteredWeakEmpiricalError_le_amplitude_at_node N x ha_nodes)⟩

private theorem abs_ndCenteredStrictEmpiricalError_le_amplitude_core
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndCenteredStrictEmpiricalError N x t| ≤ ndEmpiricalAmplitude N x := by
  rw [abs_le]
  have h := ndCenteredEmpiricalError_bounds N x t ht
  exact ⟨h.1, h.2.1.trans h.2.2⟩

private theorem abs_ndCenteredWeakEmpiricalError_le_amplitude_core
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndCenteredWeakEmpiricalError N x t| ≤ ndEmpiricalAmplitude N x := by
  rw [abs_le]
  have h := ndCenteredEmpiricalError_bounds N x t ht
  exact ⟨h.1.trans h.2.1, h.2.2⟩

/-- The finite centered amplitude is nonnegative, including for the empty sample. -/
theorem ndEmpiricalAmplitude_nonneg
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    0 ≤ ndEmpiricalAmplitude N x := by
  exact (abs_nonneg (ndCenteredStrictEmpiricalError N x 0)).trans
    (abs_ndCenteredStrictEmpiricalError_le_amplitude_core N x 0
      ⟨le_rfl, zero_le_one⟩)

/-- The finite centered amplitude is at most one half. -/
theorem ndEmpiricalAmplitude_le_half
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    ndEmpiricalAmplitude N x ≤ 1 / 2 := by
  apply Finset.max'_le (ndEmpiricalExtremalValues N x)
    (ndEmpiricalExtremalValues_nonempty N x)
  intro y hy
  simp only [ndEmpiricalExtremalValues, Finset.mem_union,
    Finset.mem_image] at hy
  rcases hy with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
  · exact (neg_le_abs (ndCenteredStrictEmpiricalError N x b)).trans
      (abs_ndCenteredStrictEmpiricalError_le_half N x b
        (ndEmpiricalNodes_subset_Icc N x (by simpa using hb)))
  · exact (le_abs_self (ndCenteredWeakEmpiricalError N x b)).trans
      (abs_ndCenteredWeakEmpiricalError_le_half N x b
        (ndEmpiricalNodes_subset_Icc N x (by simpa using hb)))

/-- Every centered strict value on `[0,1]` is bounded by the finite amplitude. -/
theorem abs_ndCenteredStrictEmpiricalError_le_amplitude
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndCenteredStrictEmpiricalError N x t| ≤ ndEmpiricalAmplitude N x :=
  abs_ndCenteredStrictEmpiricalError_le_amplitude_core N x t ht

/-- Every centered weak value on `[0,1]` is bounded by the finite amplitude. -/
theorem abs_ndCenteredWeakEmpiricalError_le_amplitude
    (N : ℕ) (x : ℕ → UnitAddCircle) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndCenteredWeakEmpiricalError N x t| ≤ ndEmpiricalAmplitude N x :=
  abs_ndCenteredWeakEmpiricalError_le_amplitude_core N x t ht

/-- The oriented finite amplitude is attained by a strict negative or weak positive value. -/
theorem exists_ndEmpirical_extremal
    (N : ℕ) (x : ℕ → UnitAddCircle) :
    ∃ b ∈ ndEmpiricalNodes N x,
      ndCenteredStrictEmpiricalError N x b = -ndEmpiricalAmplitude N x ∨
        ndCenteredWeakEmpiricalError N x b = ndEmpiricalAmplitude N x := by
  have hmax :
      ndEmpiricalAmplitude N x ∈ ndEmpiricalExtremalValues N x := by
    simpa only [ndEmpiricalAmplitude] using
      (ndEmpiricalExtremalValues N x).max'_mem
        (ndEmpiricalExtremalValues_nonempty N x)
  simp only [ndEmpiricalExtremalValues, Finset.mem_union,
    Finset.mem_image] at hmax
  rcases hmax with ⟨b, hb, hvalue⟩ | ⟨b, hb, hvalue⟩
  · refine ⟨b, hb, Or.inl ?_⟩
    linarith
  · exact ⟨b, hb, Or.inr hvalue⟩

end ND
end Erdos1135
