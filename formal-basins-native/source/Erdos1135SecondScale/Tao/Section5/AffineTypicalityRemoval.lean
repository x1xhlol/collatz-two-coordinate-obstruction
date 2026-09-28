/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.GatedSubmassComplement
import Erdos1135SecondScale.Tao.Section5.AffineIdealSumRegroup
import Erdos1135SecondScale.Tao.Section5.EndpointCoefficientBound
import Erdos1135SecondScale.Tao.Section5.PrefixTypicalityTransport

/-!
# Section 5 Affine Typicality Removal

This leaf compares the fixed-length chronological typical tuple sum produced
by the affine regrouping with the unrestricted iid Geom(2) affine-residue
expectation.  The rejected contribution costs exactly `5 * delta`.  Tuple
reversal and the Syracuse source-law identification remain downstream.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The fixed-`q` chronological typical tuple sum from the ideal affine
regrouping. -/
def taoSection5TypicalAffineCoefficientSum
    (B q : ℕ) (E : Set ℕ) : ℝ :=
  ∑ as : {as // as ∈ taoSection5TypicalTuples B q},
    geom2PNatListMass as.1 *
      taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E)
        (taoAffineOffsetZMod q as.1)

/-- The accepted gated version of the chronological typical tuple sum. -/
def taoSection5AcceptedAffineCoefficientExpectation
    (B q : ℕ) (E : Set ℕ) : ℝ :=
  ∑ X : ZMod (3 ^ q),
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X *
      taoGatedSubmass (geom2PNatListPMF q)
        (taoSection5TypicalTuple B q) (taoAffineOffsetZMod q) X

/-- The unrestricted affine-residue expectation before tuple reversal. -/
def taoSection5FullAffineCoefficientExpectation
    (B q : ℕ) (E : Set ℕ) : ℝ :=
  ∑ X : ZMod (3 ^ q),
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X *
      (((geom2PNatListPMF q).map (taoAffineOffsetZMod q)) X).toReal

/-- The weighted contribution rejected by the chronological typicality gate. -/
def taoSection5RejectedAffineCoefficientExpectation
    (B q : ℕ) (E : Set ℕ) : ℝ :=
  ∑ X : ZMod (3 ^ q),
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X *
      taoGatedSubmass (geom2PNatListPMF q)
        (fun as => ¬ taoSection5TypicalTuple B q as)
        (taoAffineOffsetZMod q) X

/-- The finite tuple sum is exactly the accepted gated iid expectation. -/
theorem taoSection5TypicalAffineCoefficientSum_eq_accepted
    (B q : ℕ) (E : Set ℕ) :
    taoSection5TypicalAffineCoefficientSum B q E =
      taoSection5AcceptedAffineCoefficientExpectation B q E := by
  classical
  let I : Finset (List ℕ+) := taoSection5TypicalTuples B q
  let f : List ℕ+ → ZMod (3 ^ q) := taoAffineOffsetZMod q
  let c : ZMod (3 ^ q) → ℝ :=
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E)
  let massTerm : List ℕ+ → ℝ := fun as =>
    geom2PNatListMass as * c (f as)
  let atomTerm : List ℕ+ → ℝ := fun as =>
    (geom2PNatListPMF q as).toReal * c (f as)
  have hfinite :
      (∑ as : {as // as ∈ I}, massTerm as.1) =
        ∑ as ∈ I, atomTerm as := by
    rw [Finset.sum_coe_sort I massTerm]
    apply Finset.sum_congr rfl
    intro as has
    have htyp : taoSection5TypicalTuple B q as :=
      mem_taoSection5TypicalTuples_iff.mp has
    have hmass := geom2PNatListPMF_apply_length_toReal as
    rw [htyp.1] at hmass
    dsimp only [massTerm, atomTerm]
    rw [hmass]
  have hweighted := sum_mul_taoGatedSubmass_mem_eq
    (geom2PNatListPMF q) I f c
  have hgate : (fun as : List ℕ+ => as ∈ I) =
      taoSection5TypicalTuple B q := by
    funext as
    apply propext
    exact mem_taoSection5TypicalTuples_iff
  unfold taoSection5TypicalAffineCoefficientSum
    taoSection5AcceptedAffineCoefficientExpectation
  change (∑ as : {as // as ∈ I}, massTerm as.1) = _
  rw [hfinite]
  simpa only [atomTerm, hgate, f, c] using hweighted

/-- The unrestricted expectation splits exactly into accepted and rejected
chronological contributions. -/
theorem taoSection5FullAffineCoefficientExpectation_eq_typical_add_rejected
    (B q : ℕ) (E : Set ℕ) :
    taoSection5FullAffineCoefficientExpectation B q E =
      taoSection5TypicalAffineCoefficientSum B q E +
        taoSection5RejectedAffineCoefficientExpectation B q E := by
  rw [taoSection5TypicalAffineCoefficientSum_eq_accepted]
  unfold taoSection5FullAffineCoefficientExpectation
    taoSection5AcceptedAffineCoefficientExpectation
    taoSection5RejectedAffineCoefficientExpectation
  calc
    (∑ X : ZMod (3 ^ q),
        taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X *
          (((geom2PNatListPMF q).map (taoAffineOffsetZMod q)) X).toReal) =
      ∑ X : ZMod (3 ^ q),
        taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X *
          (taoGatedSubmass (geom2PNatListPMF q)
              (taoSection5TypicalTuple B q) (taoAffineOffsetZMod q) X +
            taoGatedSubmass (geom2PNatListPMF q)
              (fun as => ¬ taoSection5TypicalTuple B q as)
              (taoAffineOffsetZMod q) X) := by
        apply Finset.sum_congr rfl
        intro X _hX
        rw [taoGatedSubmass_map_apply_split]
    _ = (∑ X : ZMod (3 ^ q),
          taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X *
            taoGatedSubmass (geom2PNatListPMF q)
              (taoSection5TypicalTuple B q) (taoAffineOffsetZMod q) X) +
        ∑ X : ZMod (3 ^ q),
          taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X *
            taoGatedSubmass (geom2PNatListPMF q)
              (fun as => ¬ taoSection5TypicalTuple B q as)
              (taoAffineOffsetZMod q) X := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro X _hX
      ring

/-- The rejected weighted expectation is nonnegative. -/
theorem taoSection5RejectedAffineCoefficientExpectation_nonneg
    {B q : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    0 ≤ taoSection5RejectedAffineCoefficientExpectation B q E := by
  unfold taoSection5RejectedAffineCoefficientExpectation
  apply Finset.sum_nonneg
  intro X _hX
  exact mul_nonneg
    (taoSection5PayloadFreeCoefficient_ePrime_mem_Icc_five lost hindex).1
    (taoGatedSubmass_nonneg _ _ _ _)

/-- The rejected weighted expectation costs at most `5 * delta`. -/
theorem taoSection5RejectedAffineCoefficientExpectation_le_five_mul_delta
    {B q : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    taoSection5RejectedAffineCoefficientExpectation B q E ≤
      5 * taoSection5PowerInteriorDelta B := by
  have hq : q ≤ taoSection5N0 B := by omega
  have hfailure := failure.short_notTypical_le_delta hq
  unfold taoSection5RejectedAffineCoefficientExpectation
  calc
    (∑ X : ZMod (3 ^ q),
        taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X *
          taoGatedSubmass (geom2PNatListPMF q)
            (fun as => ¬ taoSection5TypicalTuple B q as)
            (taoAffineOffsetZMod q) X) ≤
      ∑ X : ZMod (3 ^ q),
        5 * taoGatedSubmass (geom2PNatListPMF q)
          (fun as => ¬ taoSection5TypicalTuple B q as)
          (taoAffineOffsetZMod q) X := by
        apply Finset.sum_le_sum
        intro X _hX
        exact mul_le_mul_of_nonneg_right
          (taoSection5PayloadFreeCoefficient_ePrime_mem_Icc_five
            lost hindex).2
          (taoGatedSubmass_nonneg _ _ _ _)
    _ = 5 * ∑ X : ZMod (3 ^ q),
        taoGatedSubmass (geom2PNatListPMF q)
          (fun as => ¬ taoSection5TypicalTuple B q as)
          (taoAffineOffsetZMod q) X := by
      rw [Finset.mul_sum]
    _ = 5 * taoGatedRejectedMass (geom2PNatListPMF q)
        (taoSection5TypicalTuple B q) (taoAffineOffsetZMod q) := by
      rw [taoGatedSubmass_complement_sum_eq_rejectedMass]
    _ = 5 * ((geom2PNatListPMF q).toOuterMeasure
        {as | ¬ taoSection5TypicalTuple B q as}).toReal := by
      rw [taoGatedRejectedMass_eq_toOuterMeasure]
    _ ≤ 5 * taoSection5PowerInteriorDelta B :=
      mul_le_mul_of_nonneg_left hfailure (by norm_num)

/-- The full-minus-typical defect lies in the exact local error interval. -/
theorem taoSection5FullAffineCoefficientExpectation_sub_typical_mem_Icc
    {B q : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    taoSection5FullAffineCoefficientExpectation B q E -
        taoSection5TypicalAffineCoefficientSum B q E ∈
      Set.Icc 0 (5 * taoSection5PowerInteriorDelta B) := by
  have hsplit :=
    taoSection5FullAffineCoefficientExpectation_eq_typical_add_rejected B q E
  have hnonneg :=
    taoSection5RejectedAffineCoefficientExpectation_nonneg
      (E := E) lost hindex
  have hupper :=
    taoSection5RejectedAffineCoefficientExpectation_le_five_mul_delta
      (E := E) lost failure hindex
  constructor <;> linarith

/-- Paper-facing absolute comparison between the chronological typical sum
and the unrestricted iid affine expectation. -/
theorem abs_taoSection5TypicalAffineCoefficientSum_sub_full_le_five_mul_delta
    {B q : ℕ} {E : Set ℕ} (lost : TaoSection5PassLostWindowFacts B)
    (failure : TaoSection5PassTypicalFailureFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    |taoSection5TypicalAffineCoefficientSum B q E -
        taoSection5FullAffineCoefficientExpectation B q E| ≤
      5 * taoSection5PowerInteriorDelta B := by
  have hdefect :=
    taoSection5FullAffineCoefficientExpectation_sub_typical_mem_Icc
      (E := E) lost failure hindex
  rw [abs_of_nonpos (by linarith [hdefect.1])]
  linarith [hdefect.2]

end

end Tao
end Erdos1135SecondScale
