import PadicIntegerEnvelope
import UnitHaarCylinder
import ActualUnitSupport

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal
open CollatzCylinderPacking.Arithmetic Erdos1135.Tao

namespace CollatzCanonical.IntegerStationaryEnvelope

noncomputable def actualIntegerTrace (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (actualDensityValue actualFirstHitDensity n)

noncomputable def canonicalIntegerStep (k : ℕ) : ℤ_[3] → ℝ≥0∞ :=
  padicIntegerStep actualIntegerTrace k

noncomputable def canonicalIntegerEnvelope : ℤ_[3] → ℝ≥0∞ :=
  padicIntegerEnvelope actualIntegerTrace

theorem actualIntegerTrace_lt_top (n : ℕ) : actualIntegerTrace n < ⊤ :=
  ENNReal.ofReal_lt_top

theorem actualIntegerTrace_zero {n : ℕ} (hn : 0 < n) (hu : n % 3 = 0) :
    actualIntegerTrace n = 0 := by
  apply ENNReal.ofReal_eq_zero.mpr
  apply le_of_not_gt
  intro h
  exact (actual_trace_positive_iff_unit hn).mp h hu

theorem padic_natCast_isUnit_iff (n : ℕ) : IsUnit (n : ℤ_[3]) ↔ n % 3 ≠ 0 := by
  rw [padicThree_isUnit_iff_projection_ne_zero, map_natCast]
  exact not_congr ((ZMod.natCast_eq_zero_iff _ _).trans (by
    simp only [pow_one, Nat.dvd_iff_mod_eq_zero]))

theorem canonicalIntegerStep_lt_top (k : ℕ) (x : ℤ_[3]) :
    canonicalIntegerStep k x < ⊤ :=
  padicIntegerStep_lt_top actualIntegerTrace (fun n _ => actualIntegerTrace_lt_top n) k x

theorem canonicalIntegerStep_toReal_continuous (k : ℕ) :
    Continuous (fun x => (canonicalIntegerStep k x).toReal) :=
  padicIntegerStep_toReal_continuous actualIntegerTrace
    (fun n _ => actualIntegerTrace_lt_top n) k

theorem canonicalIntegerStep_zero_of_not_isUnit (k : ℕ) (hk : 1 ≤ k)
    (x : ℤ_[3]) (hx : ¬ IsUnit x) : canonicalIntegerStep k x = 0 := by
  let n := (PadicInt.toZModPow k x).val + 3 ^ k
  have hn : 0 < n := by dsimp [n]; positivity
  have he : PadicInt.toZModPow k (n : ℤ_[3]) = PadicInt.toZModPow k x := by
    rw [map_natCast]
    simp only [n, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
  have hu : n % 3 = 0 := by
    by_contra hnu
    have hunit := (padic_natCast_isUnit_iff n).mpr hnu
    apply hx
    rw [padicThree_isUnit_iff_projection_ne_zero] at hunit ⊢
    rwa [← padic_projection_refines hk he]
  apply le_antisymm _ (zero_le _)
  change padicIntegerStep actualIntegerTrace k x ≤ 0
  rw [← actualIntegerTrace_zero hn hu]
  exact iInf_le_of_le n (iInf_le_of_le hn (iInf_le_of_le he le_rfl))

theorem canonicalIntegerEnvelope_zero_of_not_isUnit (x : ℤ_[3]) (hx : ¬ IsUnit x) :
    canonicalIntegerEnvelope x = 0 := by
  apply le_antisymm _ (zero_le _)
  refine iSup_le fun k => ?_
  have h := padicIntegerStep_monotone actualIntegerTrace x (Nat.le_succ k)
  exact h.trans (le_of_eq (canonicalIntegerStep_zero_of_not_isUnit (k + 1) (by omega) x hx))

theorem canonicalIntegerEnvelope_lowerSemicontinuous :
    LowerSemicontinuous canonicalIntegerEnvelope :=
  padicIntegerEnvelope_lowerSemicontinuous actualIntegerTrace

theorem canonicalIntegerEnvelope_natCast_le (n : ℕ) (hn : 0 < n) :
    canonicalIntegerEnvelope (n : ℤ_[3]) ≤ actualIntegerTrace n :=
  padicIntegerEnvelope_natCast_le actualIntegerTrace n hn

#print axioms canonicalIntegerEnvelope_zero_of_not_isUnit
#print axioms canonicalIntegerEnvelope_lowerSemicontinuous

end CollatzCanonical.IntegerStationaryEnvelope
