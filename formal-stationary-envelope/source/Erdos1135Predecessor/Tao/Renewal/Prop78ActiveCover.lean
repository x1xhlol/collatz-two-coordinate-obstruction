/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Lemma74CanonicalFamily
import Erdos1135Predecessor.Tao.Renewal.Prop78CaseAssembly

namespace Erdos1135Predecessor

namespace Tao

structure TaoSection7Prop78ActiveCoverData
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) where
  family : Set TaoSection7Triangle
  cover :
    TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family
  pairwiseDisjoint :
    TaoSection7TriangleFamilyPairwiseDisjoint family
  rightEdge :
    TaoSection7TriangleFamilyRightEdgeInStrip ((n / 2 : ℕ) : ℝ) family
  separated :
    TaoSection7TriangleFamilySeparatedBy
      (taoSection7TriangleSeparation epsilon) family

namespace TaoSection7Prop78ActiveCoverData

noncomputable def of_canonical
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7Prop78ActiveCoverData n xi epsilon := by
  let packet := taoSection7CanonicalFamilyPacket hxi hscalar
  exact
    { family := taoSection7CanonicalTriangleFamily hxi hscalar
      cover := packet.cover
      pairwiseDisjoint := packet.pairwiseDisjoint
      rightEdge := packet.floorRightEdge
      separated := packet.separated }

end TaoSection7Prop78ActiveCoverData

theorem taoSection7_prop78_monotonicity_740_of_activeCover_caseBounds
    {n A C m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hm_low : C ≤ m)
    (hm_hi : m ≤ n / 2)
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    (hcases :
      TaoSection7Prop78BoundaryCaseBounds
        n A m xi epsilon hactive.family) :
    taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
      taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon :=
  taoSection7_prop78_monotonicity_740_of_caseBounds
    (n := n) (A := A) (C := C) (m := m) (xi := xi)
    (epsilon := epsilon) (family := hactive.family)
    hepsilon hC hm_low hm_hi hactive.cover hcases

end Tao

end Erdos1135Predecessor
