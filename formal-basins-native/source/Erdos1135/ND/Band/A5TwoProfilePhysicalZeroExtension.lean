import Erdos1135.ND.Band.A5FirstShiftSourceIngress
import Erdos1135.ND.Band.A5TwoProfileRawQ

/-!
# A5 two-profile physical-window zero extension

This leaf extends each original-endpoint interior two-profile sum from its two
intrinsic tubes to the original positive physical window.  The carriers are
not equal: the additional physical times contribute zero through the raw-Q
support indicator.  In particular, the proof-local endpoint `M / 2` used for
the shifted analytic packet never replaces the original endpoint `M`.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- The reciprocal two-profile sum may be zero-extended to the original
physical window in an interior original endpoint. -/
theorem
    sum_ndA5NominalStrictBandRawQ_physicalNuWindow_eq_fullTube_union_of_sourceGuards
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch) :
    let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
    let W := ndA5TubeWidth B C
    (∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch A W nu r) =
      ∑ nu ∈ ndA5FullTube A W ∪ ndA5FullTube (A + 1) W,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch A W nu r := by
  classical
  dsimp only
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let I1 := ndA5FullTube (A + 1) W
  let J := ndA5PhysicalNuWindow B branch C j
  have hTube0 : NDA5InteriorTubeFacts B j branch C M :=
    ndA5InteriorTubeFacts_of_guards
      hB hlogB hC hM hpadding hshift hj
  have hI0 : I0 ⊆ J := by
    simpa only [A, W, I0, J] using
      ndA5FullTube_subset_physicalNuWindow hTube0
  have hI1 : I1 ⊆ J := by
    simpa only [A, W, I1, J] using
      ndA5FullTube_add_one_subset_physicalNuWindow_of_sourceGuards
        hB hlogB hC hM hpadding hshift hj
  have hUnion : I0 ∪ I1 ⊆ J := Finset.union_subset hI0 hI1
  have hsum :
      (∑ nu ∈ I0 ∪ I1,
          ∑ r ∈ Finset.range 2,
            ndA5NominalStrictBandRawQTerm B branch A W nu r) =
        ∑ nu ∈ J,
          ∑ r ∈ Finset.range 2,
            ndA5NominalStrictBandRawQTerm B branch A W nu r := by
    apply Finset.sum_subset hUnion
    intro nu _hnuJ hnuUnion
    have hnu0 : nu ∉ I0 := by
      intro hnu
      exact hnuUnion (Finset.mem_union_left I1 hnu)
    have hnu1 : nu ∉ I1 := by
      intro hnu
      exact hnuUnion (Finset.mem_union_right I0 hnu)
    rw [sum_ndA5NominalStrictBandRawQ_eq_base_add_firstShift hB hlogB]
    simp [A, W, I0, I1, hnu0, hnu1]
  simpa only [A, W, I0, I1, J] using hsum.symm

/-- The flat two-profile sum has the same zero extension.  The exponential
factor remains attached to each original raw-Q summand. -/
theorem
    sum_ndA5NominalStrictBandFlatRawQ_physicalNuWindow_eq_fullTube_union_of_sourceGuards
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch) :
    let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
    let W := ndA5TubeWidth B C
    (∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch A W nu r) =
      ∑ nu ∈ ndA5FullTube A W ∪ ndA5FullTube (A + 1) W,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch A W nu r := by
  classical
  dsimp only
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let I1 := ndA5FullTube (A + 1) W
  let J := ndA5PhysicalNuWindow B branch C j
  have hTube0 : NDA5InteriorTubeFacts B j branch C M :=
    ndA5InteriorTubeFacts_of_guards
      hB hlogB hC hM hpadding hshift hj
  have hI0 : I0 ⊆ J := by
    simpa only [A, W, I0, J] using
      ndA5FullTube_subset_physicalNuWindow hTube0
  have hI1 : I1 ⊆ J := by
    simpa only [A, W, I1, J] using
      ndA5FullTube_add_one_subset_physicalNuWindow_of_sourceGuards
        hB hlogB hC hM hpadding hshift hj
  have hUnion : I0 ∪ I1 ⊆ J := Finset.union_subset hI0 hI1
  have hsum :
      (∑ nu ∈ I0 ∪ I1,
          ∑ r ∈ Finset.range 2,
            ndA5NominalStrictBandFlatRawQTerm B branch A W nu r) =
        ∑ nu ∈ J,
          ∑ r ∈ Finset.range 2,
            ndA5NominalStrictBandFlatRawQTerm B branch A W nu r := by
    apply Finset.sum_subset hUnion
    intro nu _hnuJ hnuUnion
    have hnu0 : nu ∉ I0 := by
      intro hnu
      exact hnuUnion (Finset.mem_union_left I1 hnu)
    have hnu1 : nu ∉ I1 := by
      intro hnu
      exact hnuUnion (Finset.mem_union_right I0 hnu)
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.cast_zero, Nat.cast_one, zero_add]
    simp [ndA5NominalStrictBandFlatRawQTerm,
      ndA5NominalStrictBandRawQTerm, A, W, I0, I1, hnu0, hnu1]
  simpa only [A, W, I0, I1, J] using hsum.symm

end
end ND
end Erdos1135
