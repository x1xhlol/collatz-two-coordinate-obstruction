import Erdos1135.Tao.Section5.AffineSourceLaw
import Erdos1135.Tao.Section5.AffineTypicalityRemoval
import Erdos1135.Tao.Section5.CommonZ
import Erdos1135.Tao.Section5.WeightedMixing

/-!
# Section 5 Fixed-Time Mixing And Common Z

This leaf consumes the unrestricted affine source law at one primitive time.
It compares the full affine coefficient expectation with Tao's branch-free
Common-Z term, then restores the already-paid prefix-typicality error.
Passage-time summation and source-window normalization remain downstream.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- The unrestricted affine expectation is exactly the fine Syracuse weighted
term at the same modulus. -/
theorem taoSection5FullAffineCoefficientExpectation_eq_fineSyracWeightedTerm
    (B q : ℕ) (E : Set ℕ) :
    taoSection5FullAffineCoefficientExpectation B q E =
      taoSection5FineSyracWeightedTerm q
        (taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E)) := by
  unfold taoSection5FullAffineCoefficientExpectation
    taoSection5FineSyracWeightedTerm syracPMFMassVector
  rw [← syracPMF_eq_geom2PNatListPMF_map_taoAffineOffsetZMod]

/-- The repaired endpoint coefficient has the exact pointwise bound `5`. -/
theorem taoSection5PayloadFreeCoefficient_ePrime_supBound_five
    {B q : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    TaoSection5CoefficientSupBound q
      (taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E)) 5 := by
  refine ⟨by norm_num, ?_⟩
  intro X
  have hcoeff :=
    taoSection5PayloadFreeCoefficient_ePrime_mem_Icc_five
      lost (E := E) (X := X) hindex
  rw [abs_of_nonneg hcoeff.1]
  exact hcoeff.2

/-- Tao's branch-independent Common-Z term is a nonnegative expectation
bounded by the repaired coefficient constant `5`. -/
theorem taoSection5PayloadFreeCommonZ_ePrime_mem_Icc_five
    {B m : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (hindex : taoSection5M0 B + m ≤ taoSection5N0 B) :
    taoSection5PayloadFreeCommonZ m (taoSection5EPrime B E) ∈
      Set.Icc (0 : ℝ) 5 := by
  rw [taoSection5PayloadFreeCommonZ_eq_fineSyracWeightedTerm]
  unfold taoSection5FineSyracWeightedTerm
  constructor
  · apply Finset.sum_nonneg
    intro X _hX
    exact mul_nonneg
      (taoSection5PayloadFreeCoefficient_ePrime_mem_Icc_five
        lost (E := E) (X := X) hindex).1
      ENNReal.toReal_nonneg
  · calc
      (∑ X : ZMod (3 ^ m),
          taoSection5PayloadFreeCoefficient m (taoSection5EPrime B E) X *
            syracPMFMassVector m X) ≤
        ∑ X : ZMod (3 ^ m), 5 * syracPMFMassVector m X := by
          apply Finset.sum_le_sum
          intro X _hX
          exact mul_le_mul_of_nonneg_right
            (taoSection5PayloadFreeCoefficient_ePrime_mem_Icc_five
              lost (E := E) (X := X) hindex).2
            ENNReal.toReal_nonneg
      _ = 5 * ∑ X : ZMod (3 ^ m), syracPMFMassVector m X := by
        rw [Finset.mul_sum]
      _ = 5 := by
        rw [show (∑ X : ZMod (3 ^ m), syracPMFMassVector m X) = 1 by
          exact pmf_sum_toReal (syracPMF m)]
        norm_num

/-- A later fixed-time index guard implies the smaller same-level guard needed
to bound Common Z. -/
theorem taoSection5PayloadFreeCommonZ_ePrime_mem_Icc_five_of_le
    {B m q : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) (hmq : m ≤ q) :
    taoSection5PayloadFreeCommonZ m (taoSection5EPrime B E) ∈
      Set.Icc (0 : ℝ) 5 := by
  apply taoSection5PayloadFreeCommonZ_ePrime_mem_Icc_five lost
  omega

/-- At one primitive time, the unrestricted affine expectation differs from
the common lower-level term by at most five times the full-L1 oscillation. -/
theorem abs_taoSection5FullAffineCoefficientExpectation_sub_commonZ_le
    {B m q : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B)
    (hmq : m ≤ q) :
    |taoSection5FullAffineCoefficientExpectation B q E -
        taoSection5PayloadFreeCommonZ m
          (taoSection5EPrime B E)| ≤
      5 * syracFineScaleOscillation m q := by
  let c : ZMod (3 ^ q) → ℝ :=
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E)
  have hfine :
      taoSection5FullAffineCoefficientExpectation B q E =
        taoSection5FineSyracWeightedTerm q c := by
    exact taoSection5FullAffineCoefficientExpectation_eq_fineSyracWeightedTerm B q E
  have hcoarse :=
    taoSection5PayloadFreeCoarseSyracWeightedTerm_coefficient_eq_commonZ
      hmq (taoSection5EPrime B E)
  have hcoarse' :
      taoSection5CoarseSyracWeightedTerm m q c =
        taoSection5PayloadFreeCommonZ m
          (taoSection5EPrime B E) := by
    simpa [c, taoSection5CoarseSyracWeightedTerm,
      taoSection5PayloadFreeCoarseSyracWeightedTerm] using hcoarse
  calc
    |taoSection5FullAffineCoefficientExpectation B q E -
        taoSection5PayloadFreeCommonZ m
          (taoSection5EPrime B E)| =
      taoSection5WeightedMixingError m q c := by
        rw [hfine, ← hcoarse']
        rfl
    _ ≤ 5 * syracFineScaleOscillation m q :=
      taoSection5WeightedMixingError_le_sup_mul_oscillation
        (taoSection5PayloadFreeCoefficient_ePrime_supBound_five lost hindex)

/-- A supplied Proposition 1.14 bound gives the fixed-time full-affine/Common-Z
comparison with no extra factor two or power of three. -/
theorem abs_taoSection5FullAffineCoefficientExpectation_sub_commonZ_le_of_mixing
    {A B m q : ℕ} {Cmix : ℝ} {E : Set ℕ}
    (lost : TaoSection5PassLostWindowFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B)
    (hm : 1 ≤ m) (hmq : m ≤ q)
    (hmix : syracFineScaleMixingAt A Cmix) :
    |taoSection5FullAffineCoefficientExpectation B q E -
        taoSection5PayloadFreeCommonZ m
          (taoSection5EPrime B E)| ≤
      5 * (Cmix / (m : ℝ) ^ A) := by
  exact (abs_taoSection5FullAffineCoefficientExpectation_sub_commonZ_le
      lost hindex hmq).trans
    (mul_le_mul_of_nonneg_left
      (syracFineScaleMixingAt.apply hmix hm hmq) (by norm_num))

/-- Restoring chronological prefix typicality adds exactly the previously
paid `5 * delta` error. -/
theorem abs_taoSection5TypicalAffineCoefficientSum_sub_commonZ_le
    {B m q : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B)
    (hmq : m ≤ q) :
    |taoSection5TypicalAffineCoefficientSum B q E -
        taoSection5PayloadFreeCommonZ m
          (taoSection5EPrime B E)| ≤
      5 * taoSection5PowerInteriorDelta B +
        5 * syracFineScaleOscillation m q := by
  have htriangle :
      |taoSection5TypicalAffineCoefficientSum B q E -
          taoSection5PayloadFreeCommonZ m
            (taoSection5EPrime B E)| ≤
        |taoSection5TypicalAffineCoefficientSum B q E -
            taoSection5FullAffineCoefficientExpectation B q E| +
          |taoSection5FullAffineCoefficientExpectation B q E -
            taoSection5PayloadFreeCommonZ m
              (taoSection5EPrime B E)| := by
    calc
      |taoSection5TypicalAffineCoefficientSum B q E -
          taoSection5PayloadFreeCommonZ m
            (taoSection5EPrime B E)| =
        |(taoSection5TypicalAffineCoefficientSum B q E -
            taoSection5FullAffineCoefficientExpectation B q E) +
          (taoSection5FullAffineCoefficientExpectation B q E -
            taoSection5PayloadFreeCommonZ m
              (taoSection5EPrime B E))| := by
                congr 1
                ring
      _ ≤ _ := abs_add_le _ _
  exact htriangle.trans (add_le_add
    (abs_taoSection5TypicalAffineCoefficientSum_sub_full_le_five_mul_delta
      lost failure hindex)
    (abs_taoSection5FullAffineCoefficientExpectation_sub_commonZ_le
      lost hindex hmq))

/-- Fixed-time typical/Common-Z comparison after applying a supplied mixing
bound. -/
theorem abs_taoSection5TypicalAffineCoefficientSum_sub_commonZ_le_of_mixing
    {A B m q : ℕ} {Cmix : ℝ} {E : Set ℕ}
    (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B)
    (hm : 1 ≤ m) (hmq : m ≤ q)
    (hmix : syracFineScaleMixingAt A Cmix) :
    |taoSection5TypicalAffineCoefficientSum B q E -
        taoSection5PayloadFreeCommonZ m
          (taoSection5EPrime B E)| ≤
      5 * taoSection5PowerInteriorDelta B +
        5 * (Cmix / (m : ℝ) ^ A) := by
  have hosc :
      5 * syracFineScaleOscillation m q ≤
        5 * (Cmix / (m : ℝ) ^ A) :=
    mul_le_mul_of_nonneg_left
      (syracFineScaleMixingAt.apply hmix hm hmq) (by norm_num)
  exact (abs_taoSection5TypicalAffineCoefficientSum_sub_commonZ_le
      lost failure hindex hmq).trans
    (add_le_add_right hosc (5 * taoSection5PowerInteriorDelta B))

end

end Tao
end Erdos1135
