/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case3FixedParameters
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarCountable

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

structure TaoSection7Case3CanonicalEStarData
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon)
    (S0 : ℕ) : Prop where
  event_toReal_le :
    ∀ (n m J fpGap : ℕ)
      (entry : TaoSection7RenewalPoint)
      (family : Set TaoSection7Triangle)
      (old : TaoSection7Triangle) (M : ℝ),
      S0 ≤ fpGap →
      fixed.Pmax ≤ J →
      old.cornerL - entry.l = (fpGap : ℤ) →
      old.Mem entry.toPoint →
      TaoSection7TriangleFamilyPairwiseDisjoint family →
      old ∈ family →
      TaoSection7Lemma710CurrentScaleControls
        n old entry.toPoint M (fpGap : ℝ) →
      2 ≤ m →
      M = (m : ℝ) →
      TaoSection7Case3BaseKcutAllowedCapAdmissibility
        (Finset.range (fixed.Pmax + 1))
        8 m (4 * fixed.Aweight) fixed.Pmax →
      ((lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarEvent
            entry family 8 (4 * fixed.Aweight) fixed.T fixed.R)).toReal ≤
        (fixed.Aweight : ℝ) ^ 2 /
          ((4 : ℝ) ^ (4 * fixed.Aweight))

end

end Tao

end Erdos1135Predecessor
