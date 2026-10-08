import Erdos1135.ND.Band.A5ReferenceCellGuards
import Erdos1135.ND.Fourier.FixedTotalRatioTelescope

/-!
# Finite center and eta guards for the A5 reference schedule

This leaf fixes the scalar majorants used by every retained terminal cell.
It keeps the strict terminal width and the real `(t2)` lower floor visible;
eventual decay of the majorants is a separate scalar step.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The common real lower floor for every physical length in a `(t2)` cell. -/
def ndA5ReferenceNuFloor (B : ℕ) : ℝ :=
  (340 / 100000 : ℝ) * Real.log B

/-- Cell-independent majorant for the normalized center displacement. -/
noncomputable def ndA5ReferenceCenterBar (B : ℕ) (C : ℝ) : ℝ :=
  (ndA5ReferenceLevel B : ℝ) * ndA5TubeWidth B C /
    ndA5ReferenceNuFloor B

/-- Cell-independent majorant for the complete R1/D6 eta parameter. -/
noncomputable def ndA5ReferenceEtaBar (B : ℕ) (C : ℝ) : ℝ :=
  let m := ndA5ReferenceLevel B
  57 * ndFixedTotalRatioScale m * ndA5TubeWidth B C /
      ndA5ReferenceNuFloor B +
    1021 * ndFixedTotalRatioScale m ^ 2 /
      ndA5ReferenceNuFloor B +
    8 / (m : ℝ) ^ 3

/-- The exact coefficient multiplying the reference after true absorption. -/
noncomputable def ndA5ReferenceAbsorbBar (B : ℕ) (C : ℝ) : ℝ :=
  (43 / 25 : ℝ) * ndA5ReferenceEtaBar B C

/-- The scalar eta cutoff supplies the global absorption bounds independently
of whether a later finite family of terminal cells is empty. -/
theorem ndA5ReferenceAbsorbBar_bounds_of_etaBar_le
    {B : ℕ} {C : ℝ}
    (hC : 0 < C)
    (hm : 150 ≤ ndA5ReferenceLevel B)
    (hfloor : 0 < ndA5ReferenceNuFloor B)
    (hetaBar : ndA5ReferenceEtaBar B C ≤ 25 / 86) :
    0 ≤ ndA5ReferenceAbsorbBar B C ∧
    ndA5ReferenceAbsorbBar B C ≤ 1 / 2 := by
  have heta0 : 0 ≤ ndA5ReferenceEtaBar B C := by
    unfold ndA5ReferenceEtaBar
    have hm0 : (0 : ℝ) < ndA5ReferenceLevel B := by
      exact_mod_cast (by omega : 0 < ndA5ReferenceLevel B)
    have hscale0 := ndFixedTotalRatioScale_nonneg (ndA5ReferenceLevel B)
    have hwidth0 : 0 ≤ ndA5TubeWidth B C := by
      unfold ndA5TubeWidth
      positivity
    positivity
  constructor
  · unfold ndA5ReferenceAbsorbBar
    positivity
  · unfold ndA5ReferenceAbsorbBar
    calc
      (43 / 25 : ℝ) * ndA5ReferenceEtaBar B C ≤
          (43 / 25 : ℝ) * (25 / 86) :=
        mul_le_mul_of_nonneg_left hetaBar (by norm_num)
      _ = 1 / 2 := by norm_num

/-- Strict terminal membership and the `(t2)` lower floor dominate both the
normalized center displacement and the full cell eta by common scalars. -/
theorem ndA5Reference_cell_majorants
    {B n L : ℕ} {C : ℝ}
    (hm : 150 ≤ ndA5ReferenceLevel B)
    (ht2 : NDA5T2ScaleFacts B n C)
    (hL : L ∈ ndA5TerminalTotals B C n)
    (hfloor : 0 < ndA5ReferenceNuFloor B) :
    ndFixedTotalRatioCenterOffset (ndA5ReferenceLevel B)
        (n - Tao.taoSection5M0 B) L ≤ ndA5ReferenceCenterBar B C ∧
    ndFixedTotalRatioEps (ndA5ReferenceLevel B)
        (n - Tao.taoSection5M0 B) L +
        8 / (ndA5ReferenceLevel B : ℝ) ^ 3 ≤
      ndA5ReferenceEtaBar B C := by
  let m := ndA5ReferenceLevel B
  let nu := n - Tao.taoSection5M0 B
  let W := ndA5TubeWidth B C
  let F := ndA5ReferenceNuFloor B
  let S := ndFixedTotalRatioScale m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hnuPos : (0 : ℝ) < (nu : ℝ) := by
    exact_mod_cast ht2.nu_pos
  have hFpos : 0 < F := by
    simpa only [F] using hfloor
  have hFnu : F ≤ (nu : ℝ) := by
    simpa only [F, nu, ndA5ReferenceNuFloor] using ht2.nu_lower
  have hD : |(L : ℝ) - 2 * (nu : ℝ)| ≤ W := by
    simpa only [nu, W] using
      (mem_ndA5TerminalTotals_iff.mp hL).2.2.le
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hD
  have hS0 : 0 ≤ S := by
    simpa only [S] using ndFixedTotalRatioScale_nonneg m
  constructor
  · unfold ndFixedTotalRatioCenterOffset ndA5ReferenceCenterBar
    change (m : ℝ) / (nu : ℝ) * |(L : ℝ) - 2 * (nu : ℝ)| ≤
      (m : ℝ) * W / F
    have hdiv : (m : ℝ) / (nu : ℝ) ≤ (m : ℝ) / F :=
      div_le_div_of_nonneg_left hm0 hFpos hFnu
    calc
      (m : ℝ) / (nu : ℝ) * |(L : ℝ) - 2 * (nu : ℝ)| ≤
          (m : ℝ) / F * |(L : ℝ) - 2 * (nu : ℝ)| :=
        mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
      _ ≤ (m : ℝ) / F * W :=
        mul_le_mul_of_nonneg_left hD (div_nonneg hm0 hFpos.le)
      _ = (m : ℝ) * W / F := by ring
  · rw [← ndFixedTotalRatio_raw_eq_ratioEps hm ht2.nu_pos]
    change
      57 * S * |(L : ℝ) - 2 * (nu : ℝ)| / (nu : ℝ) +
          1021 * S ^ 2 / (nu : ℝ) + 8 / (m : ℝ) ^ 3 ≤
        57 * S * W / F + 1021 * S ^ 2 / F + 8 / (m : ℝ) ^ 3
    have hfirstNum :
        57 * S * |(L : ℝ) - 2 * (nu : ℝ)| ≤ 57 * S * W :=
      mul_le_mul_of_nonneg_left hD (mul_nonneg (by norm_num) hS0)
    have hfirst :
        57 * S * |(L : ℝ) - 2 * (nu : ℝ)| / (nu : ℝ) ≤
          57 * S * W / F := by
      calc
        _ ≤ 57 * S * W / (nu : ℝ) :=
          div_le_div_of_nonneg_right hfirstNum hnuPos.le
        _ ≤ 57 * S * W / F :=
          div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg (by norm_num) hS0) hW0) hFpos hFnu
    have hsecond :
        1021 * S ^ 2 / (nu : ℝ) ≤ 1021 * S ^ 2 / F :=
      div_le_div_of_nonneg_left (by positivity) hFpos hFnu
    linarith

/-- Once the common eta bar is at most `25/86`, every terminal cell has the
local eta guard required by descent and the full absorption coefficient is
nonnegative and at most one half. -/
theorem ndA5Reference_cell_guards_of_etaBar_le
    {B n L : ℕ} {C : ℝ}
    (hm : 150 ≤ ndA5ReferenceLevel B)
    (ht2 : NDA5T2ScaleFacts B n C)
    (hL : L ∈ ndA5TerminalTotals B C n)
    (hfloor : 0 < ndA5ReferenceNuFloor B)
    (hetaBar : ndA5ReferenceEtaBar B C ≤ 25 / 86) :
    ndFixedTotalRatioCenterOffset (ndA5ReferenceLevel B)
        (n - Tao.taoSection5M0 B) L ≤ ndA5ReferenceCenterBar B C ∧
    0 ≤ ndFixedTotalRatioEps (ndA5ReferenceLevel B)
          (n - Tao.taoSection5M0 B) L +
          8 / (ndA5ReferenceLevel B : ℝ) ^ 3 ∧
    ndFixedTotalRatioEps (ndA5ReferenceLevel B)
          (n - Tao.taoSection5M0 B) L +
          8 / (ndA5ReferenceLevel B : ℝ) ^ 3 ≤ 1 ∧
    (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps (ndA5ReferenceLevel B)
              (n - Tao.taoSection5M0 B) L +
            8 / (ndA5ReferenceLevel B : ℝ) ^ 3) ≤
        ndA5ReferenceAbsorbBar B C ∧
    0 ≤ ndA5ReferenceAbsorbBar B C ∧
    ndA5ReferenceAbsorbBar B C ≤ 1 / 2 := by
  have hmajor := ndA5Reference_cell_majorants hm ht2 hL hfloor
  let eta :=
    ndFixedTotalRatioEps (ndA5ReferenceLevel B)
        (n - Tao.taoSection5M0 B) L +
      8 / (ndA5ReferenceLevel B : ℝ) ^ 3
  have heta0 : 0 ≤ eta := by
    dsimp only [eta]
    rw [← ndFixedTotalRatio_raw_eq_ratioEps hm ht2.nu_pos]
    have hS0 := ndFixedTotalRatioScale_nonneg (ndA5ReferenceLevel B)
    positivity
  have hetaMajor : eta ≤ ndA5ReferenceEtaBar B C := by
    simpa only [eta] using hmajor.2
  have hetaOne : eta ≤ 1 := by
    exact hetaMajor.trans (hetaBar.trans (by norm_num))
  have hcoefficient :
      (43 / 25 : ℝ) * eta ≤ ndA5ReferenceAbsorbBar B C := by
    unfold ndA5ReferenceAbsorbBar
    exact mul_le_mul_of_nonneg_left hetaMajor (by norm_num)
  have habsorb0 : 0 ≤ ndA5ReferenceAbsorbBar B C := by
    unfold ndA5ReferenceAbsorbBar
    exact mul_nonneg (by norm_num) (heta0.trans hetaMajor)
  have habsorbHalf : ndA5ReferenceAbsorbBar B C ≤ 1 / 2 := by
    unfold ndA5ReferenceAbsorbBar
    calc
      (43 / 25 : ℝ) * ndA5ReferenceEtaBar B C ≤
          (43 / 25 : ℝ) * (25 / 86) :=
        mul_le_mul_of_nonneg_left hetaBar (by norm_num)
      _ = 1 / 2 := by norm_num
  exact ⟨hmajor.1, by simpa only [eta] using heta0,
    by simpa only [eta] using hetaOne,
    by simpa only [eta] using hcoefficient, habsorb0, habsorbHalf⟩

end
end ND
end Erdos1135
