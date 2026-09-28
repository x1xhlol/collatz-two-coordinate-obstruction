/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7Geometry
import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageTails
import Erdos1135Predecessor.Tao.Renewal.HoldListHorizontalTail
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshMarginals

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79CanonicalPreHorizontalEvent_subset_deviation
    {gap m : ℕ}
    (hgap :
      (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ)) :
    {r : ℕ | 4 * m ≤ 5 * r} ⊆
      lemma77CanonicalHorizontalDeviationEvent gap
        (((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) := by
  intro r hr
  have hrReal : (4 : ℝ) * (m : ℝ) ≤ 5 * (r : ℝ) := by
    exact_mod_cast hr
  have hcenter :
      ((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ) ≤
        (r : ℝ) - (gap : ℝ) / 4 := by
    nlinarith
  change
    ((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ) ≤
      |(r : ℝ) - (gap : ℝ) / 4|
  exact hcenter.trans (le_abs_self _)

theorem lemma79CanonicalEndpointFreshPMF_suffixHorizontalTail_outerMeasure_le
    {P J : ℕ} (hPJ : P ≤ J)
    (entry : TaoSection7RenewalPoint) (gap m : ℕ) :
    (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom |
          m ≤ 10 * lemma77HoldPrefixHorizontalDelta P atom.2} ≤
      ENNReal.ofReal
        (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) := by
  let project : ((ℕ × ℤ) × List TaoSection7RenewalPoint) →
      List TaoSection7RenewalPoint := fun atom => atom.2.take P
  let Event : Set (List TaoSection7RenewalPoint) :=
    {fresh | m ≤ 10 * lemma77HoldPrefixHorizontalDelta P fresh}
  have hset :
      {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint |
          m ≤ 10 * lemma77HoldPrefixHorizontalDelta P atom.2} =
        project ⁻¹' Event := by
    ext atom
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact iff_of_eq (congrArg (fun q => m ≤ 10 * q)
      (lemma79HoldPrefixHorizontalDelta_take P atom.2).symm)
  rw [hset]
  rw [← PMF.toOuterMeasure_map_apply]
  rw [show (lemma79CanonicalEndpointFreshPMF J entry gap).map project =
      taoSection7HoldListPMF P by
    simpa [project] using
      (lemma79CanonicalEndpointFreshPMF_map_fresh_take_eq_of_le
        hPJ entry gap)]
  exact taoSection7HoldListPMF_horizontalTail_outerMeasure_le P m

theorem lemma79CanonicalPreHorizontalQuadraticRate_le
    {gap m : ℕ} (hm : 1 ≤ m)
    (hgap :
      (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ)) :
    (5 / 21 : ℝ) *
          ((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) ^ 2 *
          (m : ℝ) ≤
      ((((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) ^ 2 /
        (1 + (gap : ℝ))) := by
  let eta : ℝ := (4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hratio :
      Real.log 9 / Real.log 2 ≤ (16 / 5 : ℝ) :=
    taoSection7_log9_div_log2_lt_sixteen_fifths.le
  have hgap' : (gap : ℝ) ≤ (16 / 5 : ℝ) * (m : ℝ) :=
    hgap.trans
      (mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg m))
  have hden :
      1 + (gap : ℝ) ≤ (21 / 5 : ℝ) * (m : ℝ) := by
    nlinarith
  have hgapDen : 0 < 1 + (gap : ℝ) := by positivity
  change (5 / 21 : ℝ) * eta ^ 2 * (m : ℝ) ≤
    (eta * (m : ℝ)) ^ 2 / (1 + (gap : ℝ))
  rw [show (5 / 21 : ℝ) * eta ^ 2 * (m : ℝ) =
      (eta ^ 2 * (m : ℝ)) / (21 / 5 : ℝ) by ring]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 21 / 5) hgapDen]
  calc
    eta ^ 2 * (m : ℝ) * (1 + (gap : ℝ)) ≤
        eta ^ 2 * (m : ℝ) * ((21 / 5 : ℝ) * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hden
        (mul_nonneg (sq_nonneg eta) (Nat.cast_nonneg m))
    _ = (eta * (m : ℝ)) ^ 2 * (21 / 5 : ℝ) := by ring

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
