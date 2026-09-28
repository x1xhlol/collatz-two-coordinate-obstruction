/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case3EStarSupportProducer
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3Stopping
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeWidth

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79OutsideEprimeKernelWidths_of_currentScale_admissible
    {n m p fpGap R : ℕ}
    {old : TaoSection7Triangle} {entry : TaoSection7RenewalPoint}
    {M S sMin : ℝ}
    (hscale :
      TaoSection7Lemma710CurrentScaleControls
        n old entry.toPoint M S)
    (hm : 2 ≤ m)
    (hM : M = (m : ℝ))
    (hgapAlign : old.cornerL - entry.l = (fpGap : ℤ))
    (hadmissible :
      TaoSection7Case3EStarUsedOffsetAdmissible m p sMin)
    (hR : (R : ℝ) ≤ sMin / 10) :
    (R : ℝ) ^ 2 ≤ 1 + (fpGap : ℝ) ∧
      (sigmaSeparationScale sMin) ^ 2 ≤ 1 + (fpGap : ℝ) := by
  have hm_gt_one : 1 < m := by omega
  have hm_gt_one_real : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm_gt_one
  have hMlarge : 1 < M := by
    rw [hM]
    exact hm_gt_one_real
  have hdepth :
      old.verticalDepth entry.toPoint = (fpGap : ℤ) := by
    simpa [TaoSection7Triangle.verticalDepth,
      TaoSection7RenewalPoint.toPoint] using hgapAlign
  have hS_fpGap : S = (fpGap : ℝ) := by
    calc
      S = ((old.verticalDepth entry.toPoint : ℤ) : ℝ) :=
        hscale.S_def
      _ = ((fpGap : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hdepth
      _ = (fpGap : ℝ) := by norm_num
  have hgap :
      M / (Real.log M) ^ 2 ≤ (fpGap : ℝ) := by
    calc
      M / (Real.log M) ^ 2 ≤ S := hscale.hMlower
      _ = (fpGap : ℝ) := hS_fpGap
  have hsMin_nonneg : 0 ≤ sMin :=
    le_trans (by norm_num) hadmissible.2.1
  have hsMin_le : sMin ≤ M ^ (2 / 5 : ℝ) := by
    calc
      sMin ≤ (m : ℝ) ^ (2 / 5 : ℝ) := hadmissible.2.2
      _ = M ^ (2 / 5 : ℝ) := by rw [hM]
  exact
    lemma79OutsideEprimeKernelWidths_of_sourceScale
      hMlarge hsMin_nonneg hsMin_le hgap hR

theorem lemma79OutsideEprimeKernelWidths_of_baseKcutSchedule
    {allowed : Finset ℕ}
    {n base m Kcut p fpGap R : ℕ}
    {old : TaoSection7Triangle} {entry : TaoSection7RenewalPoint}
    {M S : ℝ}
    (hscale :
      TaoSection7Lemma710CurrentScaleControls
        n old entry.toPoint M S)
    (hm : 2 ≤ m)
    (hM : M = (m : ℝ))
    (hgapAlign : old.cornerL - entry.l = (fpGap : ℤ))
    (hschedule :
      TaoSection7Case3BaseKcutAdmissibilitySchedule
        allowed base m Kcut)
    (hp : p ∈ allowed)
    (hR :
      (R : ℝ) ≤
        taoSection7Case3LargeTriangleBoundWithBase
          (base : ℝ) Kcut p / 10) :
    (R : ℝ) ^ 2 ≤ 1 + (fpGap : ℝ) ∧
      (sigmaSeparationScale
        (taoSection7Case3LargeTriangleBoundWithBase
          (base : ℝ) Kcut p)) ^ 2 ≤
        1 + (fpGap : ℝ) := by
  exact
    lemma79OutsideEprimeKernelWidths_of_currentScale_admissible
      hscale hm hM hgapAlign (hschedule.admissible hp) hR

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
