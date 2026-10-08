/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.PassageSum
import Erdos1135SecondScale.Tao.Section5.PassNormalizer

/-!
# Section 5 Ideal Passage Center

This leaf combines the denominator-preserving ideal passage sum with the exact
passage normalizer.  It stops before comparing the ideal affine atoms with the
genuine passage event.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The complete ideal passage sum is centered at Tao's limiting passage
constant times the branch-independent Common-Z term. -/
theorem abs_taoSection5_idealAffineAtomSum_sub_two_div_log_mul_commonZ_le_of_mixing
    {A B : ℕ} {Cmix : ℝ}
    (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (hmix : syracFineScaleMixingAt A Cmix) :
    let D := logFinsetMass
      (oddLogWindow (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch))
    let I := {n // n ∈ taoSection5PassTimes B branch}
    let r := (Fintype.card I : ℝ) / D
    let Z := taoSection5PayloadFreeCommonZ (taoSection5M0 B)
      (taoSection5EPrime B E)
    |(∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
          taoSection5IdealAffineAtomMass (facts.residue.mass_pos branch) i) -
        (2 / Real.log (4 / 3 : ℝ)) * Z| ≤
      r * (5 * taoSection5PowerInteriorDelta B +
          5 * (Cmix / (taoSection5M0 B : ℝ) ^ A)) +
        5 * (184000 * Real.rpow (Real.log B) (-1 / 5 : ℝ)) := by
  classical
  dsimp only
  let D := logFinsetMass
    (oddLogWindow (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch))
  let r := (Fintype.card {n // n ∈ taoSection5PassTimes B branch} : ℝ) / D
  let Z := taoSection5PayloadFreeCommonZ (taoSection5M0 B)
    (taoSection5EPrime B E)
  let S := ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
    taoSection5IdealAffineAtomMass (facts.residue.mass_pos branch) i
  let e := 5 * taoSection5PowerInteriorDelta B +
    5 * (Cmix / (taoSection5M0 B : ℝ) ^ A)
  let eta := 184000 * Real.rpow (Real.log B) (-1 / 5 : ℝ)
  change |S - (2 / Real.log (4 / 3 : ℝ)) * Z| ≤ r * e + 5 * eta
  have hpass : |S - r * Z| ≤ r * e := by
    simpa only [S, r, D, Z, e] using
      (abs_taoSection5_idealAffineAtomSum_sub_commonZ_le_of_mixing
        branch E (facts.residue.mass_pos branch) facts.geometry.schedule
        lost failure hmix)
  have hnormalizer :
      |r - 2 / Real.log (4 / 3 : ℝ)| ≤ eta := by
    simpa only [r, D, eta] using
      (abs_taoSection5_passTimeRatio_sub_two_div_log_four_thirds_le
        facts branch)
  have hm0Guard :
      taoSection5M0 B + taoSection5M0 B ≤ taoSection5N0 B := by
    obtain ⟨n, hn⟩ := facts.geometry.schedule.nonempty branch
    have hrange := facts.geometry.schedule.range branch n hn
    omega
  have hZ : Z ∈ Set.Icc (0 : ℝ) 5 := by
    simpa only [Z] using
      (taoSection5PayloadFreeCommonZ_ePrime_mem_Icc_five
        (E := E) lost hm0Guard)
  have heta : 0 ≤ eta := by
    dsimp only [eta]
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (by nlinarith [facts.log_large]) _)
  have hscaledNormalizer :
      |(r - 2 / Real.log (4 / 3 : ℝ)) * Z| ≤ 5 * eta := by
    rw [abs_mul, abs_of_nonneg hZ.1]
    calc
      |r - 2 / Real.log (4 / 3 : ℝ)| * Z ≤ eta * Z :=
        mul_le_mul_of_nonneg_right hnormalizer hZ.1
      _ ≤ eta * 5 := mul_le_mul_of_nonneg_left hZ.2 heta
      _ = 5 * eta := by ring
  calc
    |S - (2 / Real.log (4 / 3 : ℝ)) * Z| =
        |(S - r * Z) +
          (r - 2 / Real.log (4 / 3 : ℝ)) * Z| := by
            congr 1
            ring
    _ ≤ |S - r * Z| +
        |(r - 2 / Real.log (4 / 3 : ℝ)) * Z| := abs_add_le _ _
    _ ≤ r * e + 5 * eta := add_le_add hpass hscaledNormalizer

/-- Given the public passage-ratio cap, the ideal passage-center error has a
branch-uniform scalar bound. -/
theorem abs_taoSection5_idealAffineAtomSum_sub_two_div_log_mul_commonZ_le_capped_of_mixing
    {A B : ℕ} {Cmix : ℝ}
    (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (hmix : syracFineScaleMixingAt A Cmix) (hCmix : 0 ≤ Cmix)
    (hratio :
      (Fintype.card {n // n ∈ taoSection5PassTimes B branch} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B branch)
              (taoSection5SourceHi B branch)) ≤ 9) :
    let Z := taoSection5PayloadFreeCommonZ (taoSection5M0 B)
      (taoSection5EPrime B E)
    |(∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
          taoSection5IdealAffineAtomMass (facts.residue.mass_pos branch) i) -
        (2 / Real.log (4 / 3 : ℝ)) * Z| ≤
      45 * taoSection5PowerInteriorDelta B +
        45 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
        920000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) := by
  classical
  dsimp only
  let D := logFinsetMass
    (oddLogWindow (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch))
  let r := (Fintype.card {n // n ∈ taoSection5PassTimes B branch} : ℝ) / D
  let Z := taoSection5PayloadFreeCommonZ (taoSection5M0 B)
    (taoSection5EPrime B E)
  let S := ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
    taoSection5IdealAffineAtomMass (facts.residue.mass_pos branch) i
  let mix := Cmix / (taoSection5M0 B : ℝ) ^ A
  let e := 5 * taoSection5PowerInteriorDelta B + 5 * mix
  let eta := 184000 * Real.rpow (Real.log B) (-1 / 5 : ℝ)
  change |S - (2 / Real.log (4 / 3 : ℝ)) * Z| ≤
    45 * taoSection5PowerInteriorDelta B + 45 * mix +
      920000 * Real.rpow (Real.log B) (-1 / 5 : ℝ)
  have hcenter :
      |S - (2 / Real.log (4 / 3 : ℝ)) * Z| ≤ r * e + 5 * eta := by
    simpa only [S, r, D, Z, mix, e, eta] using
      (abs_taoSection5_idealAffineAtomSum_sub_two_div_log_mul_commonZ_le_of_mixing
        facts lost failure branch E hmix)
  have hr : r ≤ 9 := by
    simpa only [r, D] using hratio
  have hmixNonneg : 0 ≤ mix := by
    dsimp only [mix]
    exact div_nonneg hCmix (by positivity)
  have he : 0 ≤ e := by
    dsimp only [e]
    exact add_nonneg
      (mul_nonneg (by norm_num) facts.geometry.delta_pos.le)
      (mul_nonneg (by norm_num) hmixNonneg)
  calc
    |S - (2 / Real.log (4 / 3 : ℝ)) * Z| ≤ r * e + 5 * eta := hcenter
    _ ≤ 9 * e + 5 * eta :=
      add_le_add (mul_le_mul_of_nonneg_right hr he) (le_refl _)
    _ = 45 * taoSection5PowerInteriorDelta B + 45 * mix +
        920000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) := by
      dsimp only [e, eta]
      ring

end

end Tao
end Erdos1135SecondScale
