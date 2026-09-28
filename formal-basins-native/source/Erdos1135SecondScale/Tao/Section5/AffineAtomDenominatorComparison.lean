/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.AffineAtomReciprocalMass
import Erdos1135SecondScale.Tao.Section5.AffineDenominatorRatio
import Erdos1135SecondScale.Tao.Section5.PassAtomMass

/-!
# Section 5 Aggregate Affine Denominator Comparison

This leaf replaces `M - F` by `M` only after summing the complete dependent
atom family.  The error is charged to the exact disjoint atom-union mass, with
no atom-count or pass-time-count loss.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Exact reciprocal-form atom term before any denominator replacement. -/
noncomputable def taoSection5ExactAffineAtomMass
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (i : TaoSection5ClosedAffineAtomIndex B branch E) : ℝ :=
  if (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
      taoAffineOffsetZMod (i.1.1 - taoSection5M0 B) i.2.1.1 then
    (((3 : ℝ) ^ (i.1.1 - taoSection5M0 B) *
          geom2PNatListMass i.2.1.1) /
        ((i.2.2.1 : ℝ) - (taoOffsetList i.2.1.1 : ℝ))) /
      logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))
  else 0

/-- Exact reciprocal expansion of the complete disjoint affine-atom union.
This theorem precedes and does not use the denominator replacement. -/
theorem taoSection5_affineAtomUnionMass_eq_sum_exact
    {B : ℕ} (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))) :
    let μ := oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass
    (μ.toOuterMeasure
        (taoSection5ClosedAffineAtomUnion B branch E)).toReal =
      ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
        taoSection5ExactAffineAtomMass hmass i := by
  classical
  dsimp only
  rw [taoSection5ClosedAffineAtomUnion_outerMass_eq_sum
    partitionFacts branch E]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [taoSection5ClosedAffineAtom_outerMass_eq_reciprocal
    affineFacts hmass i]
  rfl

/-- The denominator-simplified atom term.  It keeps the compatibility branch,
the one geometric list mass, and the exact source normalizer. -/
noncomputable def taoSection5IdealAffineAtomMass
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (i : TaoSection5ClosedAffineAtomIndex B branch E) : ℝ :=
  if (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
      taoAffineOffsetZMod (i.1.1 - taoSection5M0 B) i.2.1.1 then
    (((3 : ℝ) ^ (i.1.1 - taoSection5M0 B) *
          geom2PNatListMass i.2.1.1) / (i.2.2.1 : ℝ)) /
      logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))
  else 0

/-- Replacing one compatible denominator has exact relative defect `F / M`.
Both sides vanish for an incompatible atom. -/
theorem taoSection5_affineAtomMass_sub_ideal_eq
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (i : TaoSection5ClosedAffineAtomIndex B branch E) :
    ((oddLogWindowOddNatPMF
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
          (taoSection5ClosedAffineAtom i)).toReal -
        taoSection5IdealAffineAtomMass hmass i =
      ((taoOffsetList i.2.1.1 : ℝ) / (i.2.2.1 : ℝ)) *
        ((oddLogWindowOddNatPMF
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch) hmass).toOuterMeasure
            (taoSection5ClosedAffineAtom i)).toReal := by
  classical
  rw [taoSection5ClosedAffineAtom_outerMass_eq_reciprocal facts hmass i]
  unfold taoSection5IdealAffineAtomMass
  by_cases hcompat :
      (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
        taoAffineOffsetZMod
          (i.1.1 - taoSection5M0 B) i.2.1.1
  · simp only [if_pos hcompat]
    obtain ⟨N, _hwindow, hAtom⟩ :=
      exists_taoSection5ClosedAffineAtom_eq_singleton_of_compatible
        facts i hcompat
    have hAff :
        taoAffList i.2.1.1 (N.1 : ℚ) = (i.2.2.1 : ℚ) := by
      change N ∈ taoSection5ClosedAffineAtom i
      rw [hAtom]
      exact Set.mem_singleton N
    have htyp := mem_taoSection5TypicalTuples_iff.mp i.2.1.2
    have hdenPos := taoAffList_denominator_pos htyp.1 hAff
    have hMdata := mem_taoSection5EPrime_iff.mp i.2.2.2
    have hMpos : 0 < (i.2.2.1 : ℝ) := by
      exact_mod_cast Odd.pos hMdata.2.2.1
    field_simp [hdenPos.ne', hMpos.ne', hmass.ne']
    ring
  · simp only [if_neg hcompat]
    ring

/-- Pointwise denominator defect is nonnegative and bounded by the uniform
ratio times the actual atom mass. -/
theorem taoSection5_affineAtomMass_sub_ideal_nonneg_le
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (i : TaoSection5ClosedAffineAtomIndex B branch E) :
    0 ≤
        ((oddLogWindowOddNatPMF
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch) hmass).toOuterMeasure
            (taoSection5ClosedAffineAtom i)).toReal -
          taoSection5IdealAffineAtomMass hmass i ∧
      ((oddLogWindowOddNatPMF
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch) hmass).toOuterMeasure
            (taoSection5ClosedAffineAtom i)).toReal -
          taoSection5IdealAffineAtomMass hmass i ≤
        taoSection5AffineDenominatorRatio B *
          ((oddLogWindowOddNatPMF
            (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch) hmass).toOuterMeasure
              (taoSection5ClosedAffineAtom i)).toReal := by
  rw [taoSection5_affineAtomMass_sub_ideal_eq facts hmass i]
  have hratio := taoSection5_affineOffset_div_endpoint_nonneg_le
    facts i.1.2 i.2.1.2 i.2.2.2
  have hmassNonneg :
      0 ≤ ((oddLogWindowOddNatPMF
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
          (taoSection5ClosedAffineAtom i)).toReal :=
    ENNReal.toReal_nonneg
  exact ⟨mul_nonneg hratio.1 hmassNonneg,
    mul_le_mul_of_nonneg_right hratio.2 hmassNonneg⟩

/-- Aggregate denominator comparison through the exact disjoint atom-union
mass.  The right side retains that mass rather than replacing it by one. -/
theorem taoSection5_affineAtomUnionMass_sub_idealSum_nonneg_le
    {B : ℕ} (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))) :
    let μ := oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass
    0 ≤ (μ.toOuterMeasure
          (taoSection5ClosedAffineAtomUnion B branch E)).toReal -
        ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
          taoSection5IdealAffineAtomMass hmass i ∧
      (μ.toOuterMeasure
          (taoSection5ClosedAffineAtomUnion B branch E)).toReal -
          ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
            taoSection5IdealAffineAtomMass hmass i ≤
        taoSection5AffineDenominatorRatio B *
          (μ.toOuterMeasure
            (taoSection5ClosedAffineAtomUnion B branch E)).toReal := by
  classical
  dsimp only
  let μ := oddLogWindowOddNatPMF
    (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch) hmass
  have hsum := taoSection5ClosedAffineAtomUnion_outerMass_eq_sum
    partitionFacts branch E μ
  have hpoint := fun i : TaoSection5ClosedAffineAtomIndex B branch E =>
    taoSection5_affineAtomMass_sub_ideal_nonneg_le affineFacts hmass i
  constructor
  · rw [hsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _hi => (hpoint i).1
  · calc
      (μ.toOuterMeasure
          (taoSection5ClosedAffineAtomUnion B branch E)).toReal -
            ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
              taoSection5IdealAffineAtomMass hmass i =
          ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
            ((μ.toOuterMeasure (taoSection5ClosedAffineAtom i)).toReal -
              taoSection5IdealAffineAtomMass hmass i) := by
        rw [hsum, Finset.sum_sub_distrib]
      _ ≤ ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
          taoSection5AffineDenominatorRatio B *
            (μ.toOuterMeasure (taoSection5ClosedAffineAtom i)).toReal :=
        Finset.sum_le_sum fun i _hi => (hpoint i).2
      _ = taoSection5AffineDenominatorRatio B *
          ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
            (μ.toOuterMeasure (taoSection5ClosedAffineAtom i)).toReal := by
        rw [Finset.mul_sum]
      _ = taoSection5AffineDenominatorRatio B *
          (μ.toOuterMeasure
            (taoSection5ClosedAffineAtomUnion B branch E)).toReal := by
        rw [← hsum]

/-- The complete aggregate denominator defect is at most the scalar ratio,
using only that an event under a PMF has mass at most one. -/
theorem taoSection5_affineAtomUnionMass_sub_idealSum_le_ratio
    {B : ℕ} (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))) :
    let μ := oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass
    (μ.toOuterMeasure
        (taoSection5ClosedAffineAtomUnion B branch E)).toReal -
        ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
          taoSection5IdealAffineAtomMass hmass i ≤
      taoSection5AffineDenominatorRatio B := by
  dsimp only
  let μ := oddLogWindowOddNatPMF
    (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch) hmass
  have haggregate :=
    (taoSection5_affineAtomUnionMass_sub_idealSum_nonneg_le
      partitionFacts affineFacts branch E hmass).2
  have huniv : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have houter :
      μ.toOuterMeasure (taoSection5ClosedAffineAtomUnion B branch E) ≤ 1 := by
    calc
      μ.toOuterMeasure (taoSection5ClosedAffineAtomUnion B branch E) ≤
          μ.toOuterMeasure Set.univ :=
        μ.toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := huniv
  have hmassOne :
      (μ.toOuterMeasure
        (taoSection5ClosedAffineAtomUnion B branch E)).toReal ≤ 1 := by
    have hreal := ENNReal.toReal_mono ENNReal.one_ne_top houter
    simpa using hreal
  exact haggregate.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmassOne
      (taoSection5AffineDenominatorRatio_nonneg affineFacts))

/-- Explicit power-rate corollary for the aggregate denominator defect. -/
theorem taoSection5_affineAtomUnionMass_sub_idealSum_le_rpow_neg_four_fifths
    {B : ℕ} (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))) :
    let μ := oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass
    (μ.toOuterMeasure
        (taoSection5ClosedAffineAtomUnion B branch E)).toReal -
        ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
          taoSection5IdealAffineAtomMass hmass i ≤
      (B : ℝ) ^ (-(4 / 5 : ℝ)) :=
  (taoSection5_affineAtomUnionMass_sub_idealSum_le_ratio
    partitionFacts affineFacts branch E hmass).trans
      (taoSection5AffineDenominatorRatio_le_rpow_neg_four_fifths affineFacts)

/-- Absolute-value form of the aggregate denominator error rate. -/
theorem taoSection5_abs_affineAtomUnionMass_sub_idealSum_le_rpow_neg_four_fifths
    {B : ℕ} (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))) :
    let μ := oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass
    |(μ.toOuterMeasure
        (taoSection5ClosedAffineAtomUnion B branch E)).toReal -
        ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
          taoSection5IdealAffineAtomMass hmass i| ≤
      (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
  dsimp only
  rw [abs_of_nonneg
    (taoSection5_affineAtomUnionMass_sub_idealSum_nonneg_le
      partitionFacts affineFacts branch E hmass).1]
  exact taoSection5_affineAtomUnionMass_sub_idealSum_le_rpow_neg_four_fifths
    partitionFacts affineFacts branch E hmass

end

end Tao
end Erdos1135SecondScale
