import Erdos1135.Tao.Fourier.Lemma74CanonicalCoherence

/-!
# Lemma 7.4 Canonical Triangle Family

This proof leaf assembles the canonical triangles into one definitionally fixed
range family.  It proves exact cover, overlap uniqueness, disjointness, strip
bounds, Claim (*), and separation without selecting a second family.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- The image of the canonical triangle constructor over all active black points. -/
def taoSection7CanonicalTriangleFamily
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    Set TaoSection7Triangle :=
  Set.range (taoSection7CanonicalTriangle hxi hscalar)

/-- Two canonical-family triangles containing a common point are equal. -/
theorem taoSection7CanonicalTriangleFamily_eq_of_common_mem
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    {Delta Gamma : TaoSection7Triangle}
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    (hGamma : Gamma ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    {r : TaoSection7Point} (hrDelta : Delta.Mem r) (hrGamma : Gamma.Mem r) :
    Delta = Gamma := by
  rcases hDelta with ⟨p, rfl⟩
  rcases hGamma with ⟨q, rfl⟩
  let s : TaoSection7CanonicalBlackPoint n xi epsilon :=
    ⟨r, taoSection7CanonicalTriangle_blackOn hxi hscalar p r hrDelta⟩
  have hsP := taoSection7CanonicalTriangle_eq_of_mem hxi hscalar p s (by
    simpa [s] using hrDelta)
  have hsQ := taoSection7CanonicalTriangle_eq_of_mem hxi hscalar q s (by
    simpa [s] using hrGamma)
  exact hsP.symm.trans hsQ

theorem taoSection7CanonicalTriangleFamily_pairwiseDisjoint
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7TriangleFamilyPairwiseDisjoint
      (taoSection7CanonicalTriangleFamily hxi hscalar) := by
  intro Delta Gamma hDelta hGamma hne r hrDelta hrGamma
  exact hne (taoSection7CanonicalTriangleFamily_eq_of_common_mem
    hxi hscalar hDelta hGamma hrDelta hrGamma)

theorem taoSection7CanonicalTriangleFamily_cover
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2))
      (taoSection7CanonicalTriangleFamily hxi hscalar) := by
  intro r
  constructor
  · intro hr
    let p : TaoSection7CanonicalBlackPoint n xi epsilon := ⟨r, hr⟩
    exact ⟨taoSection7CanonicalTriangle hxi hscalar p, ⟨p, rfl⟩,
      taoSection7CanonicalTriangle_source_mem hxi hscalar p⟩
  · rintro ⟨Delta, ⟨p, rfl⟩, hr⟩
    exact taoSection7CanonicalTriangle_blackOn hxi hscalar p r hr

/-- Exact cover makes every triangle in the family black on its members. -/
theorem TaoSection7TriangleFamilyCoverBlack.blackOn
    {black : TaoSection7Point → Prop} {family : Set TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family) :
    TaoSection7TriangleFamilyBlackOn black family := by
  intro Delta hDelta p hp
  exact (hcover p).2 ⟨Delta, hDelta, hp⟩

theorem taoSection7CanonicalTriangleFamily_claimStar
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7TriangleFamilyClaimStar
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2))
      (taoSection7TriangleSeparation epsilon)
      (taoSection7CanonicalTriangleFamily hxi hscalar) := by
  rintro Delta ⟨p, rfl⟩
  exact taoSection7CanonicalTriangle_claimStar hxi hscalar p

theorem taoSection7CanonicalTriangleFamily_rightEdge
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7TriangleFamilyRightEdgeInStrip
      (taoSection7TriangleRightBound n epsilon)
      (taoSection7CanonicalTriangleFamily hxi hscalar) := by
  rintro Delta ⟨p, rfl⟩
  exact taoSection7CanonicalTriangle_rightEdge hxi hscalar p

theorem taoSection7CanonicalTriangleFamily_inStrip
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7TriangleFamilyInStrip
      (taoSection7TriangleRightBound n epsilon)
      (taoSection7CanonicalTriangleFamily hxi hscalar) := by
  rintro Delta ⟨p, rfl⟩ q hq
  change q.jReal ≤ taoSection7TriangleRightBound n epsilon
  exact (taoSection7CanonicalTriangle_member_jReal_le_rightEdge
    hxi hscalar p hq).trans
      (taoSection7CanonicalTriangle_rightEdge hxi hscalar p)

/-- The source separation margin repairs the odd-`n` gap between `n / 2` in
the reals and the cast of natural-number division. -/
theorem taoSection7TriangleRightBound_le_natHalf
    {n : ℕ} {epsilon : ℝ}
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    taoSection7TriangleRightBound n epsilon ≤ ((n / 2 : ℕ) : ℝ) := by
  have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
  have hdecomp : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
  have hnat : n ≤ 2 * (n / 2) + 1 := by omega
  have hcast : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnat
  unfold taoSection7TriangleRightBound
  have hrho := hscalar.separation_one
  linarith

theorem taoSection7CanonicalTriangleFamily_floorRightEdge
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7TriangleFamilyRightEdgeInStrip ((n / 2 : ℕ) : ℝ)
      (taoSection7CanonicalTriangleFamily hxi hscalar) := by
  intro Delta hDelta
  exact (taoSection7CanonicalTriangleFamily_rightEdge
    hxi hscalar hDelta).trans (taoSection7TriangleRightBound_le_natHalf hscalar)

theorem taoSection7CanonicalTriangleFamily_separated
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7TriangleFamilySeparatedBy
      (taoSection7TriangleSeparation epsilon)
      (taoSection7CanonicalTriangleFamily hxi hscalar) :=
  TaoSection7TriangleFamilySeparatedBy.of_claimStar
    (taoSection7CanonicalTriangleFamily_claimStar hxi hscalar)
    (taoSection7CanonicalTriangleFamily_cover hxi hscalar).blackOn
    (taoSection7CanonicalTriangleFamily_pairwiseDisjoint hxi hscalar)

/-- One strong packet for every downstream view of the canonical family. -/
structure TaoSection7CanonicalFamilyPacket
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) : Prop where
  cover : TaoSection7TriangleFamilyCoverBlack
    (taoSection7SourceBlackInDomain n xi epsilon (n / 2))
    (taoSection7CanonicalTriangleFamily hxi hscalar)
  pairwiseDisjoint : TaoSection7TriangleFamilyPairwiseDisjoint
    (taoSection7CanonicalTriangleFamily hxi hscalar)
  claimStar : TaoSection7TriangleFamilyClaimStar
    (taoSection7SourceBlackInDomain n xi epsilon (n / 2))
    (taoSection7TriangleSeparation epsilon)
    (taoSection7CanonicalTriangleFamily hxi hscalar)
  rightEdge : TaoSection7TriangleFamilyRightEdgeInStrip
    (taoSection7TriangleRightBound n epsilon)
    (taoSection7CanonicalTriangleFamily hxi hscalar)
  inStrip : TaoSection7TriangleFamilyInStrip
    (taoSection7TriangleRightBound n epsilon)
    (taoSection7CanonicalTriangleFamily hxi hscalar)
  floorRightEdge : TaoSection7TriangleFamilyRightEdgeInStrip ((n / 2 : ℕ) : ℝ)
    (taoSection7CanonicalTriangleFamily hxi hscalar)
  separated : TaoSection7TriangleFamilySeparatedBy
    (taoSection7TriangleSeparation epsilon)
    (taoSection7CanonicalTriangleFamily hxi hscalar)

theorem taoSection7CanonicalFamilyPacket
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    TaoSection7CanonicalFamilyPacket hxi hscalar where
  cover := taoSection7CanonicalTriangleFamily_cover hxi hscalar
  pairwiseDisjoint := taoSection7CanonicalTriangleFamily_pairwiseDisjoint hxi hscalar
  claimStar := taoSection7CanonicalTriangleFamily_claimStar hxi hscalar
  rightEdge := taoSection7CanonicalTriangleFamily_rightEdge hxi hscalar
  inStrip := taoSection7CanonicalTriangleFamily_inStrip hxi hscalar
  floorRightEdge := taoSection7CanonicalTriangleFamily_floorRightEdge hxi hscalar
  separated := taoSection7CanonicalTriangleFamily_separated hxi hscalar

end

end Tao
end Erdos1135
