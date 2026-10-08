/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Geom2CenteredMoment
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# High Total Weight For Positive Geom(2) Lists

This neutral leaf bounds the high total-weight event needed in the repaired summation for Tao's
Lemma 5.3.  Exact-length support is used before rewriting total weight as centered weight.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The total valuation weight exceeds the square-root scale of `B`. -/
def taoGeom2HighWeightEvent (B : ℕ) : Set (List ℕ+) :=
  {as | (B : ℝ) ^ (1 / 2 : ℝ) < (2 : ℝ) ^ taoTupleWeight as}

/-- The complement of the strict real high-weight event gives the exact
natural inequality `4^weight ≤ B`; equality stays on the low branch. -/
theorem four_pow_taoTupleWeight_le_of_not_mem_highWeightEvent
    {B : ℕ} {bs : List ℕ+}
    (hlow : bs ∉ taoGeom2HighWeightEvent B) :
    4 ^ taoTupleWeight bs ≤ B := by
  change ¬(B : ℝ) ^ (1 / 2 : ℝ) <
    (2 : ℝ) ^ taoTupleWeight bs at hlow
  have hroot :
      (2 : ℝ) ^ taoTupleWeight bs ≤ Real.sqrt (B : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact le_of_not_gt hlow
  have hsq :
      ((2 : ℝ) ^ taoTupleWeight bs) ^ 2 ≤ (B : ℝ) := by
    calc
      ((2 : ℝ) ^ taoTupleWeight bs) ^ 2 ≤
          (Real.sqrt (B : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).2 hroot
      _ = (B : ℝ) := Real.sq_sqrt (by positivity)
  have hfourReal :
      ((4 ^ taoTupleWeight bs : ℕ) : ℝ) ≤ (B : ℝ) := by
    calc
      ((4 ^ taoTupleWeight bs : ℕ) : ℝ) =
          (4 : ℝ) ^ taoTupleWeight bs := by norm_num
      _ = ((2 : ℝ) ^ taoTupleWeight bs) ^ 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
          ← pow_mul, ← pow_mul]
        congr 1; omega
      _ ≤ (B : ℝ) := hsq
  exact_mod_cast hfourReal

private theorem log_two_lt_seven_tenths :
    Real.log (2 : ℝ) < 7 / 10 := by
  exact (Real.log_two_lt_d9).trans (by norm_num)

/-- On exact-length support, high raw weight enters the centered upper tail used below. -/
theorem geom2PNatListPMF_supported_highWeight_centeredWeight_gt
    {B n : ℕ} (hB : 1 < B)
    (hn : (n : ℝ) ≤ Real.log B / 100000)
    {as : List ℕ+} (has : as ∈ (geom2PNatListPMF n).support)
    (hhigh : as ∈ taoGeom2HighWeightEvent B) :
    (7 / 10 : ℝ) * Real.log B < taoGeom2CenteredListWeight as := by
  have hBpos : 0 < (B : ℝ) := by positivity
  have hlogBpos : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast hB)
  have hlogHigh := Real.log_lt_log
    (Real.rpow_pos_of_pos hBpos (1 / 2 : ℝ)) hhigh
  rw [Real.log_rpow hBpos, Real.log_pow] at hlogHigh
  have hweightNonneg : 0 ≤ (taoTupleWeight as : ℝ) := Nat.cast_nonneg _
  have hlogTwoWeight :
      (taoTupleWeight as : ℝ) * Real.log 2 ≤
        (taoTupleWeight as : ℝ) * (7 / 10 : ℝ) :=
    mul_le_mul_of_nonneg_left log_two_lt_seven_tenths.le hweightNonneg
  have hlength : as.length = n := geom2PNatListPMF_support_length_eq has
  unfold taoGeom2CenteredListWeight
  rw [hlength]
  nlinarith

/-- The high-weight event has the explicit centered-Chernoff exponential bound. -/
theorem geom2PNatListPMF_highWeightEvent_le_exp
    {B n : ℕ} (hB : 1 < B)
    (hn : (n : ℝ) ≤ Real.log B / 100000) :
    ((geom2PNatListPMF n).toOuterMeasure
      (taoGeom2HighWeightEvent B)).toReal ≤
        Real.exp (-(7 / 40 : ℝ) * Real.log B + (n : ℝ) / 2) := by
  let E : Set (List ℕ+) :=
    {as | (7 / 10 : ℝ) * Real.log B < taoGeom2CenteredListWeight as}
  have hfinite : (geom2PNatListPMF n).toOuterMeasure E ≠ ⊤ := by
    apply ne_of_lt
    calc
      (geom2PNatListPMF n).toOuterMeasure E ≤
          (geom2PNatListPMF n).toOuterMeasure Set.univ :=
        (geom2PNatListPMF n).toOuterMeasure.mono (Set.subset_univ E)
      _ = 1 := ((geom2PNatListPMF n).toOuterMeasure_apply_eq_one_iff
        Set.univ).2 (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  have hnative :
      (geom2PNatListPMF n).toOuterMeasure (taoGeom2HighWeightEvent B) ≤
        (geom2PNatListPMF n).toOuterMeasure E := by
    apply (geom2PNatListPMF n).toOuterMeasure_mono
    rintro as ⟨hhigh, has⟩
    exact geom2PNatListPMF_supported_highWeight_centeredWeight_gt
      hB hn has hhigh
  have hreal := ENNReal.toReal_mono hfinite hnative
  have htail := geom2PNatListPMF_centeredWeight_upperTail_le
    n (t := (1 / 4 : ℝ))
      (lambda := (7 / 10 : ℝ) * Real.log B) (by norm_num) (by norm_num)
  change ((geom2PNatListPMF n).toOuterMeasure E).toReal ≤ _ at htail
  have hexponent :
      -(1 / 4 : ℝ) * ((7 / 10 : ℝ) * Real.log B) +
          8 * (1 / 4 : ℝ) ^ 2 * (n : ℝ) =
        -(7 / 40 : ℝ) * Real.log B + (n : ℝ) / 2 := by
    ring
  rw [hexponent] at htail
  exact hreal.trans htail

/-- The preceding exponential estimate in a form ready for Section 5 power arithmetic. -/
theorem geom2PNatListPMF_highWeightEvent_le_rpow
    {B n : ℕ} (hB : 1 < B)
    (hn : (n : ℝ) ≤ Real.log B / 100000) :
    ((geom2PNatListPMF n).toOuterMeasure
      (taoGeom2HighWeightEvent B)).toReal ≤
        (B : ℝ) ^ (-(34999 / 200000 : ℝ)) := by
  have hlogNonneg : 0 ≤ Real.log (B : ℝ) :=
    (Real.log_pos (by exact_mod_cast hB)).le
  refine (geom2PNatListPMF_highWeightEvent_le_exp hB hn).trans ?_
  rw [Real.rpow_def_of_pos (by positivity : 0 < (B : ℝ))]
  apply Real.exp_le_exp.mpr
  have hscaled := mul_le_mul_of_nonneg_right hn (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith

end

end Tao
end Erdos1135SecondScale
