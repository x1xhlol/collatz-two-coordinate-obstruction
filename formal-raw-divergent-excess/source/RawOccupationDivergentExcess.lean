import AsymptoticResidualWithPrefix
import ForwardLogPrefix
import ActualUnitSupport

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation.DivergentExcess
open CollatzClockAudit Erdos1135.Tao
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic CollatzCanonical.ForwardComponent

noncomputable def divergentTraceExcess (u : ℕ) : ℝ :=
  actualFirstHitDensity u / (wholeOrbitCorrection u * Real.log (3 / 2 : ℝ))

theorem divergentTraceExcess_nonneg {u : ℕ} (hu : Odd u)
    (hinj : Function.Injective (fun i => iterate i u)) : 0 ≤ divergentTraceExcess u := by
  have hW : 0 < wholeOrbitCorrection u := lt_of_lt_of_le (by norm_num)
    (wholeOrbitCorrection_one_le hu.pos hinj)
  have hg : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  exact div_nonneg (actualFirstHitDensity_nonneg u) (mul_pos hW hg).le

theorem divergentTraceExcess_pos_of_unit {u : ℕ} (hu : Odd u)
    (hinj : Function.Injective (fun i => iterate i u)) (hunit : u % 3 ≠ 0) :
    0 < divergentTraceExcess u := by
  have hW : 0 < wholeOrbitCorrection u := lt_of_lt_of_le (by norm_num)
    (wholeOrbitCorrection_one_le hu.pos hinj)
  have hg : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  exact div_pos ((actual_weighted_density_positive_iff_unit hu.pos).mpr hunit) (mul_pos hW hg)

/-- An injective odd root contributes its entire weighted forward trace in
addition to the actual descent-clock baseline. All source and prefix-rate
inputs have been discharged. -/
theorem actual_raw_occupation_divergent_eventual_lower
    {u : ℕ} (hu : Odd u) (hinj : Function.Injective (fun i => iterate i u))
    (b : ℝ) (hb : b < 1 / clockDrift + divergentTraceExcess u) :
    ∀ᶠ R : ℕ in atTop, b ≤ oddTargetDensitySum R / Real.log (R : ℝ) := by
  let H := 1 / clockDrift + divergentTraceExcess u
  have hH : 0 < H := add_pos_of_pos_of_nonneg (one_div_pos.mpr clockDrift_pos)
    (divergentTraceExcess_nonneg hu hinj)
  have hbdiv : b / H < 1 := (div_lt_one hH).mpr hb
  obtain ⟨a, ha, ha1⟩ := exists_between
    (show max 0 (b / H) < 1 from max_lt_iff.mpr ⟨by norm_num, hbdiv⟩)
  have ha0 : 0 < a := (le_max_left _ _).trans_lt ha
  have hba : b < a * H := (div_lt_iff₀ hH).mp ((le_max_right _ _).trans_lt ha)
  have hid : a * H = a / clockDrift + actualFirstHitDensity u *
      ((a / Real.log (3 / 2 : ℝ)) / wholeOrbitCorrection u) := by
    dsimp only [H, divergentTraceExcess]
    ring
  rw [hid] at hba
  exact actual_raw_occupation_lower_with_prefix_rate hu hinj ha0 ha1 (oddForwardLogLength a)
    (oddForwardLogLength_div_log_tendsto ha0.le)
    (oddForwardLogLength_eventual_growth_budget ha0.le ha1 u) b hba

theorem actual_raw_occupation_strict_baseline_excess_of_unit
    {u : ℕ} (hu : Odd u) (hinj : Function.Injective (fun i => iterate i u))
    (hunit : u % 3 ≠ 0) :
    ∃ b : ℝ, 1 / clockDrift < b ∧
      ∀ᶠ R : ℕ in atTop, b ≤ oddTargetDensitySum R / Real.log (R : ℝ) := by
  have hp := divergentTraceExcess_pos_of_unit hu hinj hunit
  refine ⟨1 / clockDrift + divergentTraceExcess u / 2, by linarith, ?_⟩
  exact actual_raw_occupation_divergent_eventual_lower hu hinj _ (by linarith)

#print axioms divergentTraceExcess_nonneg
#print axioms divergentTraceExcess_pos_of_unit
#print axioms actual_raw_occupation_divergent_eventual_lower
#print axioms actual_raw_occupation_strict_baseline_excess_of_unit

end CollatzCanonical.RawOccupation.DivergentExcess
