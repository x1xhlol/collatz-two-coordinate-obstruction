/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.GatedSubmassPartition
import Erdos1135SecondScale.Tao.Section5.PassEventPartition

/-!
# Section 5 Exact Affine-Atom Mass

This leaf turns the checked pairwise-disjoint dependent affine-atom family
into exact finite additivity for an arbitrary PMF on odd sources.  Each term
is the actual source-event mass.  There is no geometric multiplier, affine
reciprocal rewrite, source-window support claim, or common-normalizer step.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Native finite additivity for the committed dependent affine-atom union.
The source carrier may be infinite; all sets are measurable in its discrete
measurable space. -/
theorem taoSection5ClosedAffineAtomUnion_outerMeasure_eq_sum
    {B : ℕ} (facts : TaoSection5PassEventPartitionFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (μ : PMF TaoOddNat) :
    μ.toOuterMeasure (taoSection5ClosedAffineAtomUnion B branch E) =
      ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
        μ.toOuterMeasure (taoSection5ClosedAffineAtom i) := by
  classical
  let I := TaoSection5ClosedAffineAtomIndex B branch E
  let F : I → Set TaoOddNat := fun i => taoSection5ClosedAffineAtom i
  have hpair : Set.PairwiseDisjoint (Set.univ : Set I) F := by
    simpa only [I, F] using
      taoSection5ClosedAffineAtoms_pairwiseDisjoint facts branch E
  have hpairFin :
      Set.PairwiseDisjoint ((Finset.univ : Finset I) : Set I) F := by
    simpa using hpair
  have houter :
      μ.toOuterMeasure (⋃ i : I, F i) =
        ∑ i : I, μ.toOuterMeasure (F i) := by
    simpa using
      taoPMFToOuterMeasure_biUnion_finset_eq_sum
        μ (Finset.univ : Finset I) F hpairFin
  simpa only [taoSection5ClosedAffineAtomUnion, I, F] using houter

/-- Real-valued finite additivity, obtained only after the native identity.
No atom is evaluated or rewritten. -/
theorem taoSection5ClosedAffineAtomUnion_outerMass_eq_sum
    {B : ℕ} (facts : TaoSection5PassEventPartitionFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (μ : PMF TaoOddNat) :
    (μ.toOuterMeasure
        (taoSection5ClosedAffineAtomUnion B branch E)).toReal =
      ∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
        (μ.toOuterMeasure (taoSection5ClosedAffineAtom i)).toReal := by
  rw [taoSection5ClosedAffineAtomUnion_outerMeasure_eq_sum
    facts branch E μ]
  rw [ENNReal.toReal_sum]
  intro i hi
  apply ne_of_lt
  calc
    μ.toOuterMeasure (taoSection5ClosedAffineAtom i) ≤
        μ.toOuterMeasure Set.univ :=
      μ.toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2
      (Set.subset_univ _)
    _ < ⊤ := ENNReal.one_lt_top

end

end Tao
end Erdos1135SecondScale
