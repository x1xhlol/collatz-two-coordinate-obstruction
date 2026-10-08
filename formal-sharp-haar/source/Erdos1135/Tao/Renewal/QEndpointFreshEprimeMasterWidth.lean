import Erdos1135.Tao.Renewal.QEndpointFreshOutsideEprimeSourceWidth

/-!
# Canonical Eprime Master Source Width

This source-facing leaf exposes the master quadratic width retained from the
current-scale packet and derives the three-fifths gap scale needed to absorb
the fresh horizontal tail in Tao's `(7.61)`.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Current-scale controls with the exact natural gap expose the master
quadratic width before it is weakened to individual kernel widths. -/
theorem lemma79EprimeMasterWidth_of_currentScale
    {n fpGap : ℕ}
    {old : TaoSection7Triangle} {entry : TaoSection7RenewalPoint}
    {M sMin : ℝ}
    (hscale :
      TaoSection7Lemma710CurrentScaleControls
        n old entry.toPoint M (fpGap : ℝ))
    (hsMin_nonneg : 0 ≤ sMin)
    (hsMin_le : sMin ≤ M ^ (2 / 5 : ℝ)) :
    sMin ^ 2 ≤ 100 * (fpGap : ℝ) :=
  lemma79_sMin_sq_le_hundred_mul_gap
    hscale.M_large hsMin_nonneg hsMin_le hscale.hMlower

/-- Exact offset admissibility supplies the scale hypotheses of the master
width theorem. -/
theorem lemma79EprimeMasterWidth_of_currentScale_admissible
    {n m p fpGap : ℕ}
    {old : TaoSection7Triangle} {entry : TaoSection7RenewalPoint}
    {M sMin : ℝ}
    (hscale :
      TaoSection7Lemma710CurrentScaleControls
        n old entry.toPoint M (fpGap : ℝ))
    (hM : M = (m : ℝ))
    (hadmissible :
      TaoSection7Case3EStarUsedOffsetAdmissible m p sMin) :
    sMin ^ 2 ≤ 100 * (fpGap : ℝ) := by
  apply lemma79EprimeMasterWidth_of_currentScale hscale
  · exact le_trans (by norm_num) hadmissible.2.1
  · calc
      sMin ≤ (m : ℝ) ^ (2 / 5 : ℝ) := hadmissible.2.2
      _ = M ^ (2 / 5 : ℝ) := by rw [hM]

/-- A positive master scale controls the source three-fifths gap from below.
The constants are chosen so the proof reduces to
`100^3 ≤ 16^5` after raising both sides to the fifth power. -/
theorem lemma79_sMin_div_sixteen_le_gap_threeFifths
    {sMin gap : ℝ}
    (hgap_nonneg : 0 ≤ gap)
    (hsMin : 1 ≤ sMin)
    (hmaster : sMin ^ 2 ≤ 100 * gap) :
    sMin / 16 ≤ gap ^ (3 / 5 : ℝ) := by
  have hsMin_nonneg : 0 ≤ sMin := le_trans (by norm_num) hsMin
  have hsMin5_nonneg : 0 ≤ sMin ^ 5 := pow_nonneg hsMin_nonneg 5
  have hsMin5_le6 : sMin ^ 5 ≤ sMin ^ 6 := by
    calc
      sMin ^ 5 ≤ sMin ^ 5 * sMin :=
        by
          simpa using
            (mul_le_mul_of_nonneg_left hsMin hsMin5_nonneg)
      _ = sMin ^ 6 := by ring
  have hcube :
      (sMin ^ 2) ^ 3 ≤ (100 * gap) ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg sMin) hmaster 3
  have hsMin6_le :
      sMin ^ 6 ≤ (100 : ℝ) ^ 3 * gap ^ 3 := by
    calc
      sMin ^ 6 = (sMin ^ 2) ^ 3 := by ring
      _ ≤ (100 * gap) ^ 3 := hcube
      _ = (100 : ℝ) ^ 3 * gap ^ 3 := by ring
  have hconstant : (100 : ℝ) ^ 3 ≤ 16 ^ 5 := by
    norm_num
  have hscaled :
      (100 : ℝ) ^ 3 * gap ^ 3 ≤ 16 ^ 5 * gap ^ 3 :=
    mul_le_mul_of_nonneg_right hconstant (pow_nonneg hgap_nonneg 3)
  have hsMin5_le :
      sMin ^ 5 ≤ 16 ^ 5 * gap ^ 3 :=
    hsMin5_le6.trans (hsMin6_le.trans hscaled)
  have hdivPow :
      (sMin / 16) ^ 5 ≤ gap ^ 3 := by
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 ^ 5)).2
    simpa [mul_comm] using hsMin5_le
  have hgapRpowPow :
      (gap ^ (3 / 5 : ℝ)) ^ 5 = gap ^ 3 := by
    calc
      (gap ^ (3 / 5 : ℝ)) ^ (5 : ℕ) =
          (gap ^ (3 / 5 : ℝ)) ^ (5 : ℝ) :=
        (Real.rpow_natCast (gap ^ (3 / 5 : ℝ)) 5).symm
      _ = gap ^ ((3 / 5 : ℝ) * 5) :=
        (Real.rpow_mul hgap_nonneg (3 / 5 : ℝ) 5).symm
      _ = gap ^ (3 : ℝ) := by norm_num
      _ = gap ^ (3 : ℕ) := Real.rpow_natCast gap 3
  apply
    (pow_le_pow_iff_left₀
      (div_nonneg hsMin_nonneg (by norm_num))
      (Real.rpow_nonneg hgap_nonneg _)
      (by norm_num : (5 : ℕ) ≠ 0)).1
  rw [hgapRpowPow]
  exact hdivPow

/-- The source admissibility packet yields both the master quadratic width
and the three-fifths gap lower bound used by the horizontal tail. -/
theorem lemma79EprimeMasterWidth_and_threeFifths_of_currentScale_admissible
    {n m p fpGap : ℕ}
    {old : TaoSection7Triangle} {entry : TaoSection7RenewalPoint}
    {M sMin : ℝ}
    (hscale :
      TaoSection7Lemma710CurrentScaleControls
        n old entry.toPoint M (fpGap : ℝ))
    (hM : M = (m : ℝ))
    (hadmissible :
      TaoSection7Case3EStarUsedOffsetAdmissible m p sMin) :
    sMin ^ 2 ≤ 100 * (fpGap : ℝ) ∧
      sMin / 16 ≤ (fpGap : ℝ) ^ (3 / 5 : ℝ) := by
  have hmaster :=
    lemma79EprimeMasterWidth_of_currentScale_admissible
      hscale hM hadmissible
  exact
    ⟨hmaster,
      lemma79_sMin_div_sixteen_le_gap_threeFifths
        (Nat.cast_nonneg fpGap) hadmissible.2.1 hmaster⟩

/-- The base-`Kcut` source schedule specializes the master-width packet at
the literal large-triangle threshold. -/
theorem lemma79EprimeMasterWidth_and_threeFifths_of_baseKcutSchedule
    {allowed : Finset ℕ}
    {n base m Kcut p fpGap : ℕ}
    {old : TaoSection7Triangle} {entry : TaoSection7RenewalPoint}
    (hscale :
      TaoSection7Lemma710CurrentScaleControls
        n old entry.toPoint (m : ℝ) (fpGap : ℝ))
    (hschedule :
      TaoSection7Case3BaseKcutAdmissibilitySchedule
        allowed base m Kcut)
    (hp : p ∈ allowed) :
    let sMin :=
      taoSection7Case3LargeTriangleBoundWithBase
        (base : ℝ) Kcut p
    sMin ^ 2 ≤ 100 * (fpGap : ℝ) ∧
      sMin / 16 ≤ (fpGap : ℝ) ^ (3 / 5 : ℝ) := by
  dsimp only
  exact
    lemma79EprimeMasterWidth_and_threeFifths_of_currentScale_admissible
      hscale rfl (hschedule.admissible hp)

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
