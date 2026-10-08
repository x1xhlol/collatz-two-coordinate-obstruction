import CanonicalEnvelopeStationary
import CanonicalEnvelopePeriodicExtension

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open Erdos1135.Tao CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem canonicalIntegerEnvelope_syracuseH_lower (x : ℤ_[3]) :
    (1 / 2 : ℝ≥0∞) * canonicalIntegerEnvelope x ≤
      canonicalIntegerEnvelope (syracuseH x) := by
  have h := canonicalIntegerEnvelope_transfer_le (syracuseH x)
  have he : (2 : ℤ_[3]) * syracuseH x = x := by
    rw [syracuseH, ← mul_assoc, ← padicTwoUnit_coe, Units.mul_inv, one_mul]
  exact (le_add_right le_rfl).trans (by simpa only [padicBinaryTransfer, he] using h)

theorem canonicalIntegerEnvelope_syracuseJ_lower (x : ℤ_[3]) :
    (3 / 2 : ℝ≥0∞) * canonicalIntegerEnvelope x ≤
      canonicalIntegerEnvelope (syracuseJ x) := by
  have h := canonicalIntegerEnvelope_transfer_le (padicAffineBranch 1 x)
  rw [padicBinaryTransfer, padicOddLiftENN_apply_branch,
    padicAffineBranch_one_eq_syracuseJ] at h
  exact (le_add_left le_rfl).trans h

theorem canonicalIntegerEnvelope_neg_one_eq_top :
    canonicalIntegerEnvelope (-1) = ⊤ := by
  have hfix : syracuseJ (-1) = -1 := by
    unfold syracuseJ
    have he : (1 : ℤ_[3]) + 3 * -1 = 2 * -1 := by ring
    rw [he, ← mul_assoc, ← padicTwoUnit_coe, Units.inv_mul, one_mul]
  have hle := canonicalIntegerEnvelope_syracuseJ_lower (-1)
  rw [hfix] at hle
  by_contra hfin
  obtain ⟨c, hc, _hcfin, hfloor⟩ := canonicalIntegerEnvelope_uniform_unit_floor
  have hpos : 0 < canonicalIntegerEnvelope (-1) :=
    hc.trans_le (hfloor (-1) isUnit_one.neg)
  have hrpos := ENNReal.toReal_pos (ne_of_gt hpos) hfin
  have hr := ENNReal.toReal_mono hfin hle
  norm_num only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat] at hr
  linarith

theorem canonicalIntegerEnvelope_syracuseH_eq_top {x : ℤ_[3]}
    (hx : canonicalIntegerEnvelope x = ⊤) :
    canonicalIntegerEnvelope (syracuseH x) = ⊤ := by
  apply top_unique
  have h := canonicalIntegerEnvelope_syracuseH_lower x
  simpa only [hx, ENNReal.mul_top (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)] using h

theorem canonicalIntegerEnvelope_syracuseJ_eq_top {x : ℤ_[3]}
    (hx : canonicalIntegerEnvelope x = ⊤) :
    canonicalIntegerEnvelope (syracuseJ x) = ⊤ := by
  apply top_unique
  have h := canonicalIntegerEnvelope_syracuseJ_lower x
  simpa only [hx, ENNReal.mul_top (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)] using h

theorem canonicalIntegerEnvelope_halving_neg_one_eq_top (a : ℕ) :
    canonicalIntegerEnvelope ((syracuseH^[a]) (-1)) = ⊤ := by
  induction a with
  | zero => exact canonicalIntegerEnvelope_neg_one_eq_top
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact canonicalIntegerEnvelope_syracuseH_eq_top ih

#print axioms canonicalIntegerEnvelope_neg_one_eq_top
#print axioms canonicalIntegerEnvelope_halving_neg_one_eq_top

end CollatzCanonical.IntegerStationaryEnvelope
