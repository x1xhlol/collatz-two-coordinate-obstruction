import Erdos1135.ND.Band.A6PhysicalLocalLimit

/-!
# A6 Physical Center

This leaf identifies the real Gaussian scale in frozen v10 XI.3--XI.4 and
proves its one-third recentering room from the checked interior A5 geometry.
The operational center `A / delta` is also identified with the manuscript
formula `N_j - m0 - s_M / log(4/3)`.  Eta and zeta smallness remain separate
downstream producers.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- The unrounded A6 center of an arbitrary affine phase. -/
def ndA6TubeCenter (A : ℝ) : ℝ :=
  A / ndA5PhaseDelta

/-- The physical A6 center in the step-back coordinate `nu`.  This is a real
scale; it is deliberately not rounded to a natural endpoint. -/
def ndA6PhysicalCenter
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (M : ℝ) : ℝ :=
  ndA5PhysicalPhase (ndA5BandLower B branch j) M / ndA5PhaseDelta

/-- The operational affine center is exactly the frozen manuscript center
`N_j - m0 - s_M / log(4/3)`. -/
theorem ndA6PhysicalCenter_eq_source
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {M : ℝ}
    (hB : 1 ≤ B) (hM : 0 < M) :
    ndA6PhysicalCenter B j branch M =
      Real.log (ndA5BandLower B branch j / (B : ℝ)) /
          ndA5LogFourThirds -
        (Tao.taoSection5M0 B : ℝ) -
        ndA5InteriorShift B M / ndA5LogFourThirds := by
  have h := ndA5PhysicalPhase_sub_phaseDelta_mul_eq_centered
    (B := B) (j := j) (nu := 0) (branch := branch) (M := M) hB hM
  unfold ndA6PhysicalCenter
  apply (div_eq_iff ndA5PhaseDelta_mem_Ioo.1.ne').2
  simpa [mul_comm] using h

/-- Every member of an arbitrary full tube lies within `(W+1)/delta` of its
unrounded affine center. -/
theorem abs_natCast_sub_ndA6TubeCenter_lt_of_mem_fullTube
    {A W : ℝ} {nu : ℕ} (hnu : nu ∈ ndA5FullTube A W) :
    |(nu : ℝ) - ndA6TubeCenter A| <
      (W + 1) / ndA5PhaseDelta := by
  let S := ndA6TubeCenter A
  have htube : |(ndA5StrictAffineSweep A nu : ℝ)| < W :=
    (Finset.mem_filter.mp hnu).2
  have htubeBounds := abs_lt.mp htube
  have hresidual := ndA5StrictAffineSweep_sub_affine_mem_Ioc A nu
  have haffine : |A - ndA5PhaseDelta * (nu : ℝ)| < W + 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hcentered :
      A - ndA5PhaseDelta * (nu : ℝ) =
        -ndA5PhaseDelta * ((nu : ℝ) - S) := by
    dsimp [S, ndA6TubeCenter]
    field_simp [ndA5PhaseDelta_mem_Ioo.1.ne']
    ring
  rw [hcentered, abs_mul, abs_neg,
    abs_of_pos ndA5PhaseDelta_mem_Ioo.1] at haffine
  apply (lt_div_iff₀ ndA5PhaseDelta_mem_Ioo.1).2
  simpa [S, mul_comm] using haffine

/-- Every member of a physical full tube lies within `(W+1)/delta` of the
unrounded physical center.  The source's displayed `(W+2)/delta` is a safe
weaker consequence. -/
theorem abs_natCast_sub_ndA6PhysicalCenter_lt_of_mem_fullTube
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)) :
    |(nu : ℝ) - ndA6PhysicalCenter B j branch M| <
      (ndA5TubeWidth B C + 1) / ndA5PhaseDelta := by
  simpa [ndA6PhysicalCenter, ndA6TubeCenter] using
    (abs_natCast_sub_ndA6TubeCenter_lt_of_mem_fullTube hnu)

/-- A checked analytic tube has positive center and one-third recentering room
at an arbitrary affine phase. -/
theorem ndA6TubeCenter_pos_and_close_of_analytic
    {B : ℕ} {C A : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5AnalyticTubeFacts B C A) :
    0 < ndA6TubeCenter A ∧
      ∀ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
        |(nu : ℝ) - ndA6TubeCenter A| ≤
          ndA6TubeCenter A / 3 := by
  classical
  let W := ndA5TubeWidth B C
  let S := ndA6TubeCenter A
  let lo := ndA5TubeLo A W
  let D := (W + 1) / ndA5PhaseDelta
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [W] using hTube.nonempty
  have hWpos : 0 < W := by
    simpa [W] using hTube.width_pos
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : ndA5TubeLo A W ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hloMem : lo ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr (by simpa [lo] using hlohi)
  have hcell : NDA5AnalyticCellFacts B lo C A :=
    hTube.pointwise lo (by simpa [W] using hloMem)
  have hshift :
      lo + Tao.taoSection5M0 B - Tao.taoSection5M0 B = lo := by omega
  have hWleRaw := hcell.t2.width_le_nu_div_eight
  rw [hshift] at hWleRaw
  have hWle : W ≤ (lo : ℝ) / 8 := by
    simpa [W] using hWleRaw
  have hW71 : (71 : ℝ) ≤ W := by
    simpa [W] using
      ndA5TubeWidth_ge_seventy_one hTube.one_half_le_C hlogB
  have hceilReal : (71 : ℝ) ≤ (Nat.ceil W : ℝ) :=
    hW71.trans (Nat.le_ceil W)
  have hceilNat : 71 ≤ Nat.ceil W := by exact_mod_cast hceilReal
  have hRadius : 70 ≤ ndA5TubeRadius W := by
    unfold ndA5TubeRadius
    omega
  have hcrossing :
      ndA5StrictAffineSweep A lo = (ndA5TubeRadius W : ℤ) := by
    simpa [W, lo] using hTube.endpoint_crossings.1
  have hresidual := ndA5StrictAffineSweep_sub_affine_mem_Ioc A lo
  rw [hcrossing] at hresidual
  have hRadiusReal : (1 : ℝ) < ((ndA5TubeRadius W : ℤ) : ℝ) := by
    exact_mod_cast (show 1 < ndA5TubeRadius W by omega)
  have haffinePos :
      0 < A - ndA5PhaseDelta * (lo : ℝ) := by
    linarith [hresidual.2]
  have hcenterDiff :
      A - ndA5PhaseDelta * (lo : ℝ) =
        ndA5PhaseDelta * (S - (lo : ℝ)) := by
    dsimp [S, ndA6TubeCenter]
    field_simp [ndA5PhaseDelta_mem_Ioo.1.ne']
  rw [hcenterDiff] at haffinePos
  have hloLtS : (lo : ℝ) < S := by
    rcases (mul_pos_iff.mp haffinePos) with hpositive | hnegative
    · linarith [hpositive.2]
    · exact (lt_asymm ndA5PhaseDelta_mem_Ioo.1 hnegative.1).elim
  have hloNat : 0 < lo := by
    simpa [lo, W] using hTube.lo_pos
  have hloPos : (0 : ℝ) < lo := by exact_mod_cast hloNat
  have hS : 0 < S := hloPos.trans hloLtS
  have hlogLe : ndA5LogFourThirds ≤ (1 / 3 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 4 / 3 by norm_num)
    norm_num [ndA5LogFourThirds] at h ⊢
    exact h
  have hcoef :
      (12 / 25 : ℝ) ≤ (4 / 25 : ℝ) / ndA5LogFourThirds := by
    apply (le_div_iff₀ ndA5LogFourThirds_pos).2
    nlinarith
  have hshiftTerm :
      (12 / 25 : ℝ) * W ≤
        ((4 / 25 : ℝ) * W) / ndA5LogFourThirds := by
    calc
      (12 / 25 : ℝ) * W ≤
          ((4 / 25 : ℝ) / ndA5LogFourThirds) * W :=
        mul_le_mul_of_nonneg_right hcoef hWpos.le
      _ = ((4 / 25 : ℝ) * W) / ndA5LogFourThirds := by ring
  have hmargin :
      ((4 / 25 : ℝ) * W) / ndA5LogFourThirds +
          (W + 1) / ndA5PhaseDelta ≤ 3 * W := by
    simpa [W] using
      ndA5InteriorContainmentMargin hTube.one_half_le_C hlogB
  have hDle : D ≤ (63 / 25 : ℝ) * W := by
    dsimp [D]
    nlinarith
  have hDthird : D ≤ S / 3 := by
    nlinarith
  refine ⟨by simpa [S] using hS, ?_⟩
  intro nu hnu
  have hclose :=
    abs_natCast_sub_ndA6TubeCenter_lt_of_mem_fullTube hnu
  exact hclose.le.trans (by simpa [D, S, W] using hDthird)

/-- The large checked interior tube makes the physical center positive and
places every tube index within the one-third scale-change window required by
the neutral Gaussian recentering theorem. -/
theorem ndA6PhysicalCenter_pos_and_close_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    0 < ndA6PhysicalCenter B j branch M ∧
      ∀ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
        |(nu : ℝ) - ndA6PhysicalCenter B j branch M| ≤
          ndA6PhysicalCenter B j branch M / 3 := by
  simpa [ndA6PhysicalCenter, ndA6TubeCenter] using
    (ndA6TubeCenter_pos_and_close_of_analytic hlogB
      (NDA5InteriorTubeFacts.toAnalytic hTube))

/-- Arbitrary-phase tube-center specialization of the fixed-scale XI.3/XI.4
insertion.  Only eta and zeta smallness remain as pointwise hypotheses. -/
theorem abs_ndA5TubeRawMass_sub_sum_tubeCenterGaussian_le_of_analytic
    {B : ℕ} {C A : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5AnalyticTubeFacts B C A)
    (heta : ∀ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA6LocalEta nu
        (Int.natAbs (ndA5StrictAffineSweep A nu)) ≤ 1)
    (hzeta : ∀ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA6GaussianRecenterZeta (nu : ℝ)
        (ndA6TubeCenter A)
        (ndA5StrictAffineSweep A nu : ℝ) ≤ 1) :
    |ndA5TubeRawMass A (ndA5TubeWidth B C) -
        ∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6TubeCenter A)
            (ndA5StrictAffineSweep A nu : ℝ)| ≤
      ∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
        ndA6Gaussian (ndA6TubeCenter A)
            (ndA5StrictAffineSweep A nu : ℝ) *
          (ndA6LocalRelativeError nu
                (Int.natAbs (ndA5StrictAffineSweep A nu)) *
              (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ)
                (ndA6TubeCenter A)
                (ndA5StrictAffineSweep A nu : ℝ)) +
            2 * ndA6GaussianRecenterZeta (nu : ℝ)
              (ndA6TubeCenter A)
              (ndA5StrictAffineSweep A nu : ℝ)) := by
  obtain ⟨hS, hclose⟩ :=
    ndA6TubeCenter_pos_and_close_of_analytic hlogB hTube
  exact abs_ndA5TubeRawMass_sub_sum_fixedGaussian_le_of_analytic
    hTube hS hclose heta hzeta

/-- Intrinsic physical-center specialization of the fixed-scale XI.3/XI.4
insertion.  Only eta and zeta smallness remain as pointwise hypotheses. -/
theorem abs_ndA5TubeRawMass_sub_sum_physicalCenterGaussian_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (heta : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA6LocalEta nu
        (Int.natAbs (ndA5StrictAffineSweep
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu)) ≤ 1)
    (hzeta : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA6GaussianRecenterZeta (nu : ℝ)
        (ndA6PhysicalCenter B j branch M)
        (ndA5StrictAffineSweep
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) ≤ 1) :
    |ndA5TubeRawMass
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) -
        ∑ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6PhysicalCenter B j branch M)
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)| ≤
      ∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
        ndA6Gaussian (ndA6PhysicalCenter B j branch M)
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) *
          (ndA6LocalRelativeError nu
                (Int.natAbs (ndA5StrictAffineSweep
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu)) *
              (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ)
                (ndA6PhysicalCenter B j branch M)
                (ndA5StrictAffineSweep
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)) +
            2 * ndA6GaussianRecenterZeta (nu : ℝ)
              (ndA6PhysicalCenter B j branch M)
              (ndA5StrictAffineSweep
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)) := by
  simpa [ndA6PhysicalCenter, ndA6TubeCenter] using
    (abs_ndA5TubeRawMass_sub_sum_tubeCenterGaussian_le_of_analytic
      hlogB (NDA5InteriorTubeFacts.toAnalytic hTube) heta hzeta)

/-- Physical-band specialization of the fixed-scale XI.3/XI.4 insertion,
obtained from the intrinsic estimate through the interior carrier equality. -/
theorem abs_ndA5BandRawMass_sub_sum_physicalCenterGaussian_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (heta : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA6LocalEta nu
        (Int.natAbs (ndA5StrictAffineSweep
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu)) ≤ 1)
    (hzeta : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA6GaussianRecenterZeta (nu : ℝ)
        (ndA6PhysicalCenter B j branch M)
        (ndA5StrictAffineSweep
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) ≤ 1) :
    |ndA5BandRawMass B branch C j M -
        ∑ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6PhysicalCenter B j branch M)
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)| ≤
      ∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
        ndA6Gaussian (ndA6PhysicalCenter B j branch M)
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) *
          (ndA6LocalRelativeError nu
                (Int.natAbs (ndA5StrictAffineSweep
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu)) *
              (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ)
                (ndA6PhysicalCenter B j branch M)
                (ndA5StrictAffineSweep
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)) +
            2 * ndA6GaussianRecenterZeta (nu : ℝ)
              (ndA6PhysicalCenter B j branch M)
              (ndA5StrictAffineSweep
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)) := by
  rw [ndA5BandRawMass_eq_tubeRawMass_of_interior hTube]
  exact abs_ndA5TubeRawMass_sub_sum_physicalCenterGaussian_le_of_interior
    hlogB hTube heta hzeta

section Canaries

example : ndA5LogFourThirds = ndA5PhaseDelta * Real.log 2 :=
  ndA5LogFourThirds_eq_phaseDelta_mul_logTwo

example (A nu : ℝ) :
    A - ndA5PhaseDelta * nu =
      -ndA5PhaseDelta * (nu - A / ndA5PhaseDelta) := by
  field_simp [ndA5PhaseDelta_mem_Ioo.1.ne']
  ring

end Canaries

end

end ND
end Erdos1135
