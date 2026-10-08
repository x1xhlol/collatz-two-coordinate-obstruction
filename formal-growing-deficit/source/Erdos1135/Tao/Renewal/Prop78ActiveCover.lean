import Erdos1135.Tao.Renewal.Prop78CaseAssembly
import Erdos1135.Tao.Fourier.Lemma74CanonicalFamily

/-!
# Section 7 Proposition 7.8 Active Triangle Cover Socket

This module names the active source triangle cover supplied by Tao's Lemma 7.4
and connects that cover to the Proposition 7.8 case-assembly socket.  It does
not prove Lemma 7.4, any boundary case estimate, `(7.41)`, Proposition 7.8,
Proposition 7.3, Proposition 7.1, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

/--
Data extracted from the source-facing Lemma 7.4 triangle-family statement at
the cutoff `J = n / 2`.

The `cover` field is the exact active source-black cover consumed by
`Prop78CaseAssembly`; the remaining fields keep the stronger Lemma 7.4
right-edge/disjointness/separation data visible for future case producers.
-/
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

/-- Build the active-cover socket directly from the canonical Lemma 7.4
family packet, retaining the definitionally fixed range family. -/
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

/--
Extract the named Prop. 7.8 active-cover data from the source-facing Lemma 7.4
right-edge decomposition statement.
-/
noncomputable def of_lemma74
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hlemma74 :
      TaoSection7Lemma74BlackTriangleRightEdgeDecompositionStatement
        n xi epsilon) :
    TaoSection7Prop78ActiveCoverData n xi epsilon := by
  classical
  let family : Set TaoSection7Triangle := Classical.choose hlemma74
  have hspec := Classical.choose_spec hlemma74
  exact
    { family := family
      cover := hspec.1
      pairwiseDisjoint := hspec.2.1
      rightEdge := hspec.2.2.1
      separated := hspec.2.2.2 }

end TaoSection7Prop78ActiveCoverData

/--
Assemble the pointwise `(7.41)` boundary hypothesis from a named active cover
and supplied case bounds for that same cover family.
-/
theorem taoSection7Prop78_boundary741_of_activeCover_caseBounds
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    (hcases :
      TaoSection7Prop78BoundaryCaseBounds
        n A m xi epsilon hactive.family) :
    ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon :=
  taoSection7Prop78_boundary741_of_caseBounds
    (n := n) (A := A) (m := m) (xi := xi) (epsilon := epsilon)
    (family := hactive.family) hactive.cover hcases

/--
Source-range monotonicity `(7.40)` from named Lemma 7.4 active-cover data and
supplied case bounds for that same family.
-/
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
end Erdos1135
