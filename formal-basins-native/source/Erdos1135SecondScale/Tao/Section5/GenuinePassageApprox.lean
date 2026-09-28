/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Finite
import Erdos1135SecondScale.Tao.Section5.AffineAtomDenominatorComparison
import Erdos1135SecondScale.Tao.Section5.PowerInteriorBoundaryMass
import Erdos1135SecondScale.Tao.Section5.PassTypicalFailure

/-!
# Section 5 Genuine Passage Approximation

This leaf lifts the complete ideal affine-atom sum to the genuine passage
event while preserving the one-sided error.  The artificial no-hit endpoint
and later full-L1 comparison are deliberately absent.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The genuine passage-event mass lies above the ideal affine-atom sum, and
their difference pays each closed-prefix, source-boundary, and denominator
defect exactly once. -/
theorem taoSection5_genuinePassageMass_sub_idealSum_nonneg_le
    {B : ℕ}
    (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (boundaryFacts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (failureFacts : TaoSection5PassTypicalFailureFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ) :
    let hmass := boundaryFacts.residue.mass_pos branch
    let μ := oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass
    let P := (μ.toOuterMeasure (taoSection5PassEvent B E)).toReal
    let I := ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
      taoSection5IdealAffineAtomMass hmass i
    0 ≤ P - I ∧
      P - I ≤
        32002 * taoSection5PowerInteriorDelta B +
          (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
  classical
  dsimp only
  let lo := taoSection5SourceLo B branch
  let hi := taoSection5SourceHi B branch
  let hmass := boundaryFacts.residue.mass_pos branch
  let p := oddLogWindowPMF lo hi hmass
  let f : {N : ℕ // N ∈ oddLogWindow lo hi} → TaoOddNat :=
    oddLogWindowValueToOddNat
  let μ := oddLogWindowOddNatPMF lo hi hmass
  let P := (μ.toOuterMeasure (taoSection5PassEvent B E)).toReal
  let U := (μ.toOuterMeasure
    (taoSection5ClosedAffineAtomUnion B branch E)).toReal
  let I := ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
    taoSection5IdealAffineAtomMass hmass i
  change 0 ≤ P - I ∧
    P - I ≤ 32002 * taoSection5PowerInteriorDelta B +
      (B : ℝ) ^ (-(4 / 5 : ℝ))
  have hclosedSubset :=
    taoSection5ClosedGoodInteriorPassEvent_subset_atomUnion
      partitionFacts branch E
  have hpassDiff :
      f ⁻¹' taoSection5PassEvent B E \
          f ⁻¹' taoSection5ClosedAffineAtomUnion B branch E ⊆
        f ⁻¹' ((taoSection5ClosedGoodEvent B)ᶜ ∪
          (taoSection5PowerInteriorEvent B branch)ᶜ) := by
    intro N hN
    change f N ∈ (taoSection5ClosedGoodEvent B)ᶜ ∪
      (taoSection5PowerInteriorEvent B branch)ᶜ
    by_cases hgood : f N ∈ taoSection5ClosedGoodEvent B
    · by_cases hinterior : f N ∈ taoSection5PowerInteriorEvent B branch
      · exfalso
        exact hN.2 (hclosedSubset ⟨⟨hN.1, hgood⟩, hinterior⟩)
      · exact Or.inr hinterior
    · exact Or.inl hgood
  have hpassSubUnion :
      P - U ≤
        (μ.toOuterMeasure ((taoSection5ClosedGoodEvent B)ᶜ ∪
          (taoSection5PowerInteriorEvent B branch)ᶜ)).toReal := by
    change
      (((p.map f).toOuterMeasure (taoSection5PassEvent B E)).toReal -
          ((p.map f).toOuterMeasure
            (taoSection5ClosedAffineAtomUnion B branch E)).toReal) ≤
        ((p.map f).toOuterMeasure ((taoSection5ClosedGoodEvent B)ᶜ ∪
          (taoSection5PowerInteriorEvent B branch)ᶜ)).toReal
    exact pmfMapOuterMass_diff_le_of_preimage_diff_subset p f hpassDiff
  have hunion :
      (μ.toOuterMeasure ((taoSection5ClosedGoodEvent B)ᶜ ∪
          (taoSection5PowerInteriorEvent B branch)ᶜ)).toReal ≤
        (μ.toOuterMeasure (taoSection5ClosedGoodEvent B)ᶜ).toReal +
          (μ.toOuterMeasure
            (taoSection5PowerInteriorEvent B branch)ᶜ).toReal := by
    change
      ((p.map f).toOuterMeasure ((taoSection5ClosedGoodEvent B)ᶜ ∪
          (taoSection5PowerInteriorEvent B branch)ᶜ)).toReal ≤
        ((p.map f).toOuterMeasure (taoSection5ClosedGoodEvent B)ᶜ).toReal +
          ((p.map f).toOuterMeasure
            (taoSection5PowerInteriorEvent B branch)ᶜ).toReal
    simpa only [pmfProb_eq_toOuterMeasure_toReal,
      PMF.toOuterMeasure_map_apply, Set.preimage_union] using
        (pmfProb_union_le_add p
          (f ⁻¹' (taoSection5ClosedGoodEvent B)ᶜ)
          (f ⁻¹' (taoSection5PowerInteriorEvent B branch)ᶜ))
  have hclosed :
      (μ.toOuterMeasure (taoSection5ClosedGoodEvent B)ᶜ).toReal ≤
        2 * taoSection5PowerInteriorDelta B := by
    simpa only [μ, lo, hi] using failureFacts.closedGood_compl_le branch
  have hinterior :
      (μ.toOuterMeasure
          (taoSection5PowerInteriorEvent B branch)ᶜ).toReal ≤
        32000 * taoSection5PowerInteriorDelta B := by
    change
      ((p.map f).toOuterMeasure
          (taoSection5PowerInteriorEvent B branch)ᶜ).toReal ≤
        32000 * taoSection5PowerInteriorDelta B
    rw [PMF.toOuterMeasure_map_apply,
      ← pmfProb_eq_toOuterMeasure_toReal]
    calc
      pmfProb p (f ⁻¹' (taoSection5PowerInteriorEvent B branch)ᶜ) =
          logFinsetProb (oddLogWindow lo hi)
            ((↑(taoSection5PowerInterior B branch) : Set ℕ)ᶜ) := by
        simpa only [p, f, taoSection5PowerInteriorEvent,
          oddLogWindowValueToOddNat, Set.mem_preimage, Set.mem_compl_iff,
          Set.mem_setOf_eq] using
            (pmfProb_oddLogWindowPMF lo hi hmass
              ((↑(taoSection5PowerInterior B branch) : Set ℕ)ᶜ))
      _ ≤ 32000 * taoSection5PowerInteriorDelta B := by
        simpa only [lo, hi] using boundaryFacts.discarded_prob_le branch
  have hpassSubUnionMass :
      P - U ≤ 32002 * taoSection5PowerInteriorDelta B := by
    calc
      P - U ≤
          (μ.toOuterMeasure ((taoSection5ClosedGoodEvent B)ᶜ ∪
            (taoSection5PowerInteriorEvent B branch)ᶜ)).toReal :=
        hpassSubUnion
      _ ≤ (μ.toOuterMeasure (taoSection5ClosedGoodEvent B)ᶜ).toReal +
          (μ.toOuterMeasure
            (taoSection5PowerInteriorEvent B branch)ᶜ).toReal := hunion
      _ ≤ 2 * taoSection5PowerInteriorDelta B +
          32000 * taoSection5PowerInteriorDelta B :=
        add_le_add hclosed hinterior
      _ = 32002 * taoSection5PowerInteriorDelta B := by ring
  have hAtomPass : U ≤ P := by
    have hpre :
        f ⁻¹' taoSection5ClosedAffineAtomUnion B branch E ⊆
          f ⁻¹' taoSection5PassEvent B E :=
      Set.preimage_mono
        (taoSection5ClosedAffineAtomUnion_subset_passEvent
          partitionFacts branch E)
    have hmono := pmfProb_mono p hpre
    change
      ((p.map f).toOuterMeasure
          (taoSection5ClosedAffineAtomUnion B branch E)).toReal ≤
        ((p.map f).toOuterMeasure (taoSection5PassEvent B E)).toReal
    simpa only [pmfProb_eq_toOuterMeasure_toReal,
      PMF.toOuterMeasure_map_apply] using hmono
  have hdenomNonneg : 0 ≤ U - I := by
    simpa only [U, I, μ, lo, hi] using
      (taoSection5_affineAtomUnionMass_sub_idealSum_nonneg_le
        partitionFacts affineFacts branch E hmass).1
  have hdenomRate :
      U - I ≤ (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
    simpa only [U, I, μ, lo, hi] using
      (taoSection5_affineAtomUnionMass_sub_idealSum_le_rpow_neg_four_fifths
        partitionFacts affineFacts branch E hmass)
  constructor
  · exact sub_nonneg.mpr ((sub_nonneg.mp hdenomNonneg).trans hAtomPass)
  · calc
      P - I = (P - U) + (U - I) := by ring
      _ ≤ 32002 * taoSection5PowerInteriorDelta B +
          (B : ℝ) ^ (-(4 / 5 : ℝ)) :=
        add_le_add hpassSubUnionMass hdenomRate

end

end Tao
end Erdos1135SecondScale
