import Erdos1135.ND.Band.A6PhysicalModerateWindow

/-!
# A6 Finite Physical Interior Endpoint

This leaf composes the checked physical local/recentering error with the
native strict-multiplicity Gaussian quadrature.  It stops at an exact finite
bound; fixed-`C` eventuality and the asymptotic A6-INT wrapper remain separate.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- The native strict-fiber quadrature remainder at the physical center.
The multiplicity contribution `2 * Phi(0)` is not scaled by `1 / delta`;
only the finite Gaussian rectangle contribution carries that factor. -/
def ndA6PhysicalGaussianQuadratureError
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) : ℝ :=
  let W := ndA5TubeWidth B C
  let S := ndA6PhysicalCenter B j branch M
  (2 + 1 / ndA5PhaseDelta) * ndA6Gaussian S 0 +
    (4 * S /
        (ndA5PhaseDelta * (ndA5TubeRadius W : ℝ))) *
      ndA6Gaussian S (ndA5TubeRadius W : ℝ)

/-- The finite physical A6 interior composition.  The right side retains the
local/quadrature cross term and uses the exact native tube radius
`ceil(W)-1`; no second ceiling shift or Poisson argument is introduced. -/
theorem abs_ndA5BandRawMass_sub_invDelta_le_of_physicalModerate
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hmoderate : ndA6PhysicalModerateBudget B j branch C M ≤ 1) :
    |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤
      ndA6PhysicalUniformError B j branch C M *
          (1 / ndA5PhaseDelta +
            ndA6PhysicalGaussianQuadratureError B j branch C M) +
        ndA6PhysicalGaussianQuadratureError B j branch C M := by
  classical
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let S := ndA6PhysicalCenter B j branch M
  let H : ℝ := ∑ nu ∈ ndA5FullTube A W,
    ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)
  let epsilon := ndA6PhysicalUniformError B j branch C M
  let Q := ndA6PhysicalGaussianQuadratureError B j branch C M
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [A, W] using hTube.nonempty
  obtain ⟨nu₀, hnu₀⟩ := hne
  have hWpos : 0 < W := by
    have hstrict := (Finset.mem_filter.mp hnu₀).2
    exact (abs_nonneg (ndA5StrictAffineSweep A nu₀ : ℝ)).trans_lt hstrict
  have hcell : NDA5InteriorCellFacts B j nu₀ branch C M :=
    hTube.pointwise nu₀ (by simpa [A, W] using hnu₀)
  have hW71 : (71 : ℝ) ≤ W := by
    simpa [W] using
      ndA5TubeWidth_ge_seventy_one hcell.one_half_le_C hlogB
  have hceilReal : (71 : ℝ) ≤ (Nat.ceil W : ℝ) :=
    hW71.trans (Nat.le_ceil W)
  have hceilNat : 71 ≤ Nat.ceil W := by exact_mod_cast hceilReal
  have hR : 0 < ndA5TubeRadius W := by
    unfold ndA5TubeRadius
    omega
  have hlo : 0 < ndA5TubeLo A W := by
    simpa [A, W] using hTube.lo_pos
  have hS : 0 < S := by
    simpa [S] using
      (ndA6PhysicalCenter_pos_and_close_of_interior hlogB hTube).1
  have hlinear : 0 ≤ ndA6PhysicalLinearRatio B j branch C M := by
    unfold ndA6PhysicalLinearRatio
    exact div_nonneg hWpos.le (by positivity)
  have hcubic : 0 ≤ ndA6PhysicalCubicRatio B j branch C M := by
    unfold ndA6PhysicalCubicRatio
    exact div_nonneg (by positivity) (sq_nonneg _)
  have hepsilon : 0 ≤ epsilon := by
    dsimp [epsilon, ndA6PhysicalUniformError]
    exact add_nonneg
      (mul_nonneg (by norm_num) hlinear)
      (mul_nonneg (by norm_num) hcubic)
  have hlocal :
      |ndA5BandRawMass B branch C j M - H| ≤ epsilon * H := by
    simpa [A, W, S, H, epsilon] using
      abs_ndA5BandRawMass_sub_sum_physicalCenterGaussian_le_uniform
        hlogB hTube hmoderate
  have hquadrature : |H - 1 / ndA5PhaseDelta| ≤ Q := by
    simpa [A, W, S, H, Q, ndA6PhysicalGaussianQuadratureError] using
      abs_sum_ndA5FullTube_gaussian_sub_invDelta_le_explicit_tail
        hWpos hlo hS hR
  have hHsub : H - 1 / ndA5PhaseDelta ≤ Q :=
    (le_abs_self (H - 1 / ndA5PhaseDelta)).trans hquadrature
  have hHupper' : H ≤ Q + 1 / ndA5PhaseDelta :=
    sub_le_iff_le_add.mp hHsub
  have hHupper : H ≤ 1 / ndA5PhaseDelta + Q := by
    simpa [add_comm] using hHupper'
  change
    |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤
      epsilon * (1 / ndA5PhaseDelta + Q) + Q
  calc
    |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| =
        |(ndA5BandRawMass B branch C j M - H) +
          (H - 1 / ndA5PhaseDelta)| := by
      congr 1
      ring
    _ ≤ |ndA5BandRawMass B branch C j M - H| +
          |H - 1 / ndA5PhaseDelta| := abs_add_le _ _
    _ ≤ epsilon * H + Q := add_le_add hlocal hquadrature
    _ ≤ epsilon * (1 / ndA5PhaseDelta + Q) + Q :=
      add_le_add (mul_le_mul_of_nonneg_left hHupper hepsilon) le_rfl

section Canaries

example {W : ℝ} (hW : (71 : ℝ) ≤ W) :
    0 < ndA5TubeRadius W := by
  have hceilReal : (71 : ℝ) ≤ (Nat.ceil W : ℝ) :=
    hW.trans (Nat.le_ceil W)
  have hceilNat : 71 ≤ Nat.ceil W := by exact_mod_cast hceilReal
  unfold ndA5TubeRadius
  omega

example {G H c epsilon Q : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hlocal : |G - H| ≤ epsilon * H)
    (hquadrature : |H - c| ≤ Q) :
    |G - c| ≤ epsilon * (c + Q) + Q := by
  have hHsub : H - c ≤ Q := (le_abs_self (H - c)).trans hquadrature
  have hHupper : H ≤ c + Q := by
    have hHupper' : H ≤ Q + c := sub_le_iff_le_add.mp hHsub
    simpa [add_comm] using hHupper'
  calc
    |G - c| = |(G - H) + (H - c)| := by congr 1 <;> ring
    _ ≤ |G - H| + |H - c| := abs_add_le _ _
    _ ≤ epsilon * H + Q := add_le_add hlocal hquadrature
    _ ≤ epsilon * (c + Q) + Q :=
      add_le_add (mul_le_mul_of_nonneg_left hHupper hepsilon) le_rfl

end Canaries

end

end ND
end Erdos1135
