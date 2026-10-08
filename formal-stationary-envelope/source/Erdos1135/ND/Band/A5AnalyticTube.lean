import Erdos1135.ND.Band.A5Physical

/-!
# A5 Carrier-Neutral Analytic Tube Facts

This leaf separates the intrinsic full-tube geometry and pointwise analytic
facts from physical padded-window membership.  It keeps the frozen interior
records unchanged and exposes an explicit forgetting adapter for later
arbitrary-phase A6 consumers.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Pointwise analytic data on an arbitrary affine phase. -/
structure NDA5AnalyticCellFacts (B nu : ℕ) (C A : ℝ) : Prop where
  t2 : NDA5T2ScaleFacts B (nu + Tao.taoSection5M0 B) C
  level : NDA5PhysicalLevelFacts A nu

/-- Intrinsic analytic data on a complete full tube at an arbitrary phase. -/
structure NDA5AnalyticTubeFacts (B : ℕ) (C A : ℝ) : Prop where
  one_half_le_C : (1 / 2 : ℝ) ≤ C
  nonempty : (ndA5FullTube A (ndA5TubeWidth B C)).Nonempty
  pointwise : ∀ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
    NDA5AnalyticCellFacts B nu C A

/-- A nonempty strict full tube has positive width. -/
theorem NDA5AnalyticTubeFacts.width_pos
    {B : ℕ} {C A : ℝ} (h : NDA5AnalyticTubeFacts B C A) :
    0 < ndA5TubeWidth B C := by
  obtain ⟨nu, hnu⟩ := h.nonempty
  have hstrict := (Finset.mem_filter.mp hnu).2
  exact (abs_nonneg (ndA5StrictAffineSweep A nu : ℝ)).trans_lt hstrict

/-- Pointwise `(t2)` positivity prevents clipping at the natural left edge. -/
theorem NDA5AnalyticTubeFacts.lo_pos
    {B : ℕ} {C A : ℝ} (h : NDA5AnalyticTubeFacts B C A) :
    0 < ndA5TubeLo A (ndA5TubeWidth B C) := by
  let W := ndA5TubeWidth B C
  have hEq := ndA5FullTube_eq_Icc h.width_pos h.nonempty
  have hlohi : ndA5TubeLo A W ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact h.nonempty
  have hloMem : ndA5TubeLo A W ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr hlohi
  have hcell : NDA5AnalyticCellFacts B (ndA5TubeLo A W) C A :=
    h.pointwise (ndA5TubeLo A W) (by simpa [W] using hloMem)
  have hshift :
      ndA5TubeLo A W + Tao.taoSection5M0 B - Tao.taoSection5M0 B =
        ndA5TubeLo A W := by omega
  have hpos := hcell.t2.nu_pos
  rw [hshift] at hpos
  simpa [W] using hpos

/-- Exact signed endpoint crossings, derived from intrinsic tube geometry. -/
theorem NDA5AnalyticTubeFacts.endpoint_crossings
    {B : ℕ} {C A : ℝ} (h : NDA5AnalyticTubeFacts B C A) :
    ndA5StrictAffineSweep A
          (ndA5TubeLo A (ndA5TubeWidth B C)) =
        (ndA5TubeRadius (ndA5TubeWidth B C) : ℤ) ∧
      ndA5StrictAffineSweep A
          (ndA5TubeHi A (ndA5TubeWidth B C)) =
        -(ndA5TubeRadius (ndA5TubeWidth B C) : ℤ) :=
  ndA5FullTube_endpoint_crossings h.width_pos h.nonempty h.lo_pos

/-- Frozen full-tube cardinality error, derived rather than stored. -/
theorem NDA5AnalyticTubeFacts.card_error
    {B : ℕ} {C A : ℝ} (h : NDA5AnalyticTubeFacts B C A) :
    |((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) -
        2 * ndA5TubeWidth B C / ndA5PhaseDelta| ≤
      2 + 1 / ndA5PhaseDelta :=
  ndA5FullTube_card_error h.width_pos h.nonempty h.lo_pos

/-- Forget the physical-window fields of an existing interior cell. -/
def NDA5InteriorCellFacts.toAnalytic
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (h : NDA5InteriorCellFacts B j nu branch C M) :
    NDA5AnalyticCellFacts B nu C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M) where
  t2 := h.t2
  level := h.level

/-- Forget physical-window membership while retaining intrinsic tube data. -/
def NDA5InteriorTubeFacts.toAnalytic
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (h : NDA5InteriorTubeFacts B j branch C M) :
    NDA5AnalyticTubeFacts B C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M) where
  one_half_le_C := by
    obtain ⟨nu, hnu⟩ := h.nonempty
    exact (h.pointwise nu hnu).one_half_le_C
  nonempty := h.nonempty
  pointwise := fun nu hnu =>
    NDA5InteriorCellFacts.toAnalytic (h.pointwise nu hnu)

end

end ND
end Erdos1135
