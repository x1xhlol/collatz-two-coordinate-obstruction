import Erdos1135.ND.Band.A5Physical
import Erdos1135.ND.Fourier.FiberConditioning

/-!
# A5 Raw Tube and Physical-Band Masses

This leaf freezes the first probability carrier shared by A5 X.3 and A6.
The pointwise weight contains the strict intrinsic tube indicator, while the
global band mass is separately restricted to the physical padded window.
Only in the checked interior regime are the two raw masses identified.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- Positive physical times in the padded window, shifted back by `m0`.
The strict filter prevents natural subtraction from aliasing every
`n <= m0` at zero. -/
noncomputable def ndA5PhysicalNuWindow
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (C : ℝ) (j : ℕ) :
    Finset ℕ :=
  ((ndA5PaddedBandWindow B branch C j).filter
      (fun n => Tao.taoSection5M0 B < n)).image
    (fun n => n - Tao.taoSection5M0 B)

/-- Exact membership in the shifted positive physical carrier. -/
theorem mem_ndA5PhysicalNuWindow_iff
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ} :
    nu ∈ ndA5PhysicalNuWindow B branch C j ↔
      0 < nu ∧
        nu + Tao.taoSection5M0 B ∈
          ndA5PaddedBandWindow B branch C j := by
  classical
  constructor
  · intro hnu
    rcases Finset.mem_image.mp hnu with ⟨n, hn, hnEq⟩
    rcases Finset.mem_filter.mp hn with ⟨hnWindow, hm0n⟩
    have hshift : nu + Tao.taoSection5M0 B = n := by omega
    constructor
    · omega
    · simpa [hshift] using hnWindow
  · rintro ⟨hnuPos, hshifted⟩
    apply Finset.mem_image.mpr
    refine ⟨nu + Tao.taoSection5M0 B, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hshifted, by omega⟩
    · omega

/-- The source weight
`P(sigma_nu = L_nu) * 1{|d_nu| < W}`.  The physical window is
deliberately not part of this intrinsic pointwise definition. -/
noncomputable def ndA5RawQ (A W : ℝ) (nu : ℕ) : ℝ :=
  if nu ∈ ndA5FullTube A W then
    ndGeom2EndpointMass nu (ndA5PhysicalLevel A nu)
  else 0

@[simp] theorem ndA5RawQ_of_mem
    {A W : ℝ} {nu : ℕ} (hnu : nu ∈ ndA5FullTube A W) :
    ndA5RawQ A W nu =
      ndGeom2EndpointMass nu (ndA5PhysicalLevel A nu) := by
  simp [ndA5RawQ, hnu]

@[simp] theorem ndA5RawQ_of_not_mem
    {A W : ℝ} {nu : ℕ} (hnu : nu ∉ ndA5FullTube A W) :
    ndA5RawQ A W nu = 0 := by
  simp [ndA5RawQ, hnu]

theorem ndA5RawQ_nonneg (A W : ℝ) (nu : ℕ) :
    0 ≤ ndA5RawQ A W nu := by
  unfold ndA5RawQ
  split_ifs
  · unfold ndGeom2EndpointMass
    exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- Intrinsic raw tube mass, the unnormalized `Z` carrier of A5 X.3. -/
noncomputable def ndA5TubeRawMass (A W : ℝ) : ℝ :=
  ∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu

/-- Physical-window-restricted raw mass `G(M,j)`.  This definition remains
valid for exterior `M`; it is not globally replaced by the intrinsic tube
mass. -/
noncomputable def ndA5BandRawMass
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (M : ℝ) : ℝ :=
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  ∑ nu ∈ ndA5PhysicalNuWindow B branch C j, ndA5RawQ A W nu

/-- In an interior cell, positivity of the strict indicated endpoint mass is
exactly intrinsic full-tube membership.  Endpoint positivity alone is not a
support statement; the indicator in `ndA5RawQ` is load-bearing. -/
theorem ndA5RawQ_pos_iff_of_interior
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    0 < ndA5RawQ
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) nu ↔
      nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) := by
  constructor
  · intro hq
    by_contra hnu
    rw [ndA5RawQ_of_not_mem hnu] at hq
    exact (lt_irrefl 0) hq
  · intro hnu
    rw [ndA5RawQ_of_mem hnu]
    have hcell := hTube.pointwise nu hnu
    have hnuPos : 0 < nu := by
      simpa using hcell.t2.nu_pos
    exact ndGeom2EndpointMass_pos hnuPos hcell.level.nu_le_nat

/-- Checked interior containment embeds the intrinsic tube in the total
positive physical carrier.  No equality of carriers is claimed: the padded
window is generally larger. -/
theorem ndA5FullTube_subset_physicalNuWindow
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) ⊆
      ndA5PhysicalNuWindow B branch C j := by
  intro nu hnu
  apply mem_ndA5PhysicalNuWindow_iff.mpr
  have hcell := hTube.pointwise nu hnu
  exact ⟨by simpa using hcell.t2.nu_pos, hcell.shifted_mem⟩

/-- Interior-only common raw mass: extending the intrinsic tube sum to the
physical carrier adds only zero indicated weights. -/
theorem ndA5BandRawMass_eq_tubeRawMass_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    ndA5BandRawMass B branch C j M =
      ndA5TubeRawMass
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) := by
  classical
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  have hsubset : ndA5FullTube A W ⊆
      ndA5PhysicalNuWindow B branch C j := by
    simpa [A, W] using ndA5FullTube_subset_physicalNuWindow hTube
  have hsum :
      (∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu) =
        ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
          ndA5RawQ A W nu := by
    apply Finset.sum_subset hsubset
    intro nu _hnuPhysical hnuTube
    exact ndA5RawQ_of_not_mem hnuTube
  simpa [ndA5BandRawMass, ndA5TubeRawMass, A, W] using hsum.symm

end

end ND
end Erdos1135
