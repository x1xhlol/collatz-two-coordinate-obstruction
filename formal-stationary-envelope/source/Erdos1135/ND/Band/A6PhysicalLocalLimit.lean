import Erdos1135.ND.Band.A5NormalizerFloor
import Erdos1135.ND.Band.A5AnalyticTube
import Erdos1135.ND.Band.A6LocalLimit
import Erdos1135.ND.Band.A6GaussianRecenter

/-!
# A6 Physical Local Limit

This leaf inserts the signed local negative-binomial law into an interior A5
tube and recenters its Gaussian scale at an arbitrary fixed positive `S`.
The pointwise eta, scale-closeness, and zeta guards remain visible: their
physical eventuality and the later ceiling-shift and Poisson arguments are
separate producers.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

private theorem abs_sub_le_fixedGaussianBudget
    {p phiN phiS epsilon zeta : ℝ}
    (hlocal : |p - phiN| ≤ phiN * epsilon)
    (hrecenter : |phiN - phiS| ≤ phiS * (2 * zeta))
    (hupper : phiN ≤ phiS * (1 + 2 * zeta))
    (hepsilon : 0 ≤ epsilon) :
    |p - phiS| ≤
      phiS * (epsilon * (1 + 2 * zeta) + 2 * zeta) := by
  calc
    |p - phiS| ≤ |p - phiN| + |phiN - phiS| :=
      abs_sub_le p phiN phiS
    _ ≤ phiN * epsilon + phiS * (2 * zeta) :=
      add_le_add hlocal hrecenter
    _ ≤ (phiS * (1 + 2 * zeta)) * epsilon +
        phiS * (2 * zeta) :=
      add_le_add (mul_le_mul_of_nonneg_right hupper hepsilon) le_rfl
    _ = phiS * (epsilon * (1 + 2 * zeta) + 2 * zeta) := by ring

private theorem abs_ndA5RawQ_sub_fixedGaussian_le
    {A W S : ℝ} {nu : ℕ}
    (hnu : nu ∈ ndA5FullTube A W)
    (hnuPos : 0 < nu)
    (hWle : W ≤ (nu : ℝ) / 8)
    (hlevel : NDA5PhysicalLevelFacts A nu)
    (hS : 0 < S)
    (hclose : |(nu : ℝ) - S| ≤ S / 3)
    (heta : ndA6LocalEta nu
      (Int.natAbs (ndA5StrictAffineSweep A nu)) ≤ 1)
    (hzeta : ndA6GaussianRecenterZeta (nu : ℝ) S
      (ndA5StrictAffineSweep A nu : ℝ) ≤ 1) :
    |ndA5RawQ A W nu -
        ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)| ≤
      ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ) *
        (ndA6LocalRelativeError nu
              (Int.natAbs (ndA5StrictAffineSweep A nu)) *
            (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ) S
              (ndA5StrictAffineSweep A nu : ℝ)) +
          2 * ndA6GaussianRecenterZeta (nu : ℝ) S
            (ndA5StrictAffineSweep A nu : ℝ)) := by
  let d := Int.natAbs (ndA5StrictAffineSweep A nu)
  have htube : |(ndA5StrictAffineSweep A nu : ℝ)| < W :=
    (Finset.mem_filter.mp hnu).2
  have hdCast : (d : ℝ) = |(ndA5StrictAffineSweep A nu : ℝ)| := by
    dsimp [d]
    rw [Nat.cast_natAbs]
    norm_cast
  have hdReal : (4 : ℝ) * (d : ℝ) ≤ (nu : ℝ) := by
    rw [hdCast]
    have hnuReal : (0 : ℝ) < nu := by exact_mod_cast hnuPos
    nlinarith
  have hd : 4 * d ≤ nu := by
    exact_mod_cast hdReal
  have hdisplacement := ndA5PhysicalLevel_centralDisplacement_eq hlevel
  have hsmall :
      4 * ndGeom2CentralDisplacement nu (ndA5PhysicalLevel A nu) ≤ nu := by
    rw [hdisplacement]
    exact hd
  have hetaDisplacement :
      ndA6LocalEta nu
          (ndGeom2CentralDisplacement nu (ndA5PhysicalLevel A nu)) ≤ 1 := by
    rw [hdisplacement]
    simpa [d] using heta
  have hsignedInt :
      (ndA5PhysicalLevel A nu : ℤ) - 2 * (nu : ℤ) =
        ndA5StrictAffineSweep A nu := by
    rw [hlevel.nat_cast_eq]
    exact ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A nu
  have hsignedReal := congrArg (fun z : ℤ => (z : ℝ)) hsignedInt
  push_cast at hsignedReal
  have hlocal :
      |ndA5RawQ A W nu -
          ndA6Gaussian (nu : ℝ)
            (ndA5StrictAffineSweep A nu : ℝ)| ≤
        ndA6Gaussian (nu : ℝ)
            (ndA5StrictAffineSweep A nu : ℝ) *
          ndA6LocalRelativeError nu d := by
    have h := abs_ndGeom2EndpointMass_sub_gaussian_le
      (n := nu) (L := ndA5PhysicalLevel A nu) hnuPos
      hlevel.nu_le_nat hsmall hetaDisplacement
    rw [hdisplacement, hsignedReal] at h
    rw [ndA5RawQ_of_mem hnu]
    simpa [d] using h
  have hnuReal : (0 : ℝ) < nu := by exact_mod_cast hnuPos
  have hepsilon : 0 ≤ ndA6LocalRelativeError nu d := by
    unfold ndA6LocalRelativeError ndA6LocalEta
    positivity
  have hrecenter := abs_ndA6Gaussian_sub_le_two_mul_recenterZeta
    hnuReal hS hclose hzeta
  have hupper := ndA6Gaussian_le_one_add_two_mul_recenterZeta
    hnuReal hS hclose hzeta
  simpa [d] using abs_sub_le_fixedGaussianBudget hlocal hrecenter hupper hepsilon

/-- Arbitrary-phase intrinsic XI.3/XI.4 insertion at a fixed positive Gaussian
scale.  The load-bearing `2 * epsilon * zeta` cross term is retained. -/
theorem abs_ndA5TubeRawMass_sub_sum_fixedGaussian_le_of_analytic
    {B : ℕ} {C A S : ℝ}
    (hTube : NDA5AnalyticTubeFacts B C A)
    (hS : 0 < S)
    (hclose : ∀ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      |(nu : ℝ) - S| ≤ S / 3)
    (heta : ∀ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA6LocalEta nu
        (Int.natAbs (ndA5StrictAffineSweep A nu)) ≤ 1)
    (hzeta : ∀ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA6GaussianRecenterZeta (nu : ℝ) S
        (ndA5StrictAffineSweep A nu : ℝ) ≤ 1) :
    |ndA5TubeRawMass A (ndA5TubeWidth B C) -
        ∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)| ≤
      ∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
        ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ) *
          (ndA6LocalRelativeError nu
                (Int.natAbs (ndA5StrictAffineSweep A nu)) *
              (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ) S
                (ndA5StrictAffineSweep A nu : ℝ)) +
            2 * ndA6GaussianRecenterZeta (nu : ℝ) S
              (ndA5StrictAffineSweep A nu : ℝ)) := by
  classical
  let W := ndA5TubeWidth B C
  have hclose' : ∀ nu ∈ ndA5FullTube A W,
      |(nu : ℝ) - S| ≤ S / 3 := by
    simpa [W] using hclose
  have heta' : ∀ nu ∈ ndA5FullTube A W,
      ndA6LocalEta nu (Int.natAbs (ndA5StrictAffineSweep A nu)) ≤ 1 := by
    simpa [W] using heta
  have hzeta' : ∀ nu ∈ ndA5FullTube A W,
      ndA6GaussianRecenterZeta (nu : ℝ) S
        (ndA5StrictAffineSweep A nu : ℝ) ≤ 1 := by
    simpa [W] using hzeta
  have hpointwise : ∀ nu ∈ ndA5FullTube A W,
      |ndA5RawQ A W nu -
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)| ≤
        ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ) *
          (ndA6LocalRelativeError nu
                (Int.natAbs (ndA5StrictAffineSweep A nu)) *
              (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ) S
                (ndA5StrictAffineSweep A nu : ℝ)) +
            2 * ndA6GaussianRecenterZeta (nu : ℝ) S
              (ndA5StrictAffineSweep A nu : ℝ)) := by
    intro nu hnu
    have hcell : NDA5AnalyticCellFacts B nu C A :=
      hTube.pointwise nu (by simpa [W] using hnu)
    have hshift :
        nu + Tao.taoSection5M0 B - Tao.taoSection5M0 B = nu := by omega
    have hnuPos := hcell.t2.nu_pos
    have hWle := hcell.t2.width_le_nu_div_eight
    rw [hshift] at hnuPos hWle
    apply abs_ndA5RawQ_sub_fixedGaussian_le hnu hnuPos
      (by simpa [W] using hWle) hcell.level hS
      (hclose' nu hnu) (heta' nu hnu) (hzeta' nu hnu)
  change
    |∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu -
        ∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ nu ∈ ndA5FullTube A W,
        (ndA5RawQ A W nu -
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ))| ≤
        ∑ nu ∈ ndA5FullTube A W,
          |ndA5RawQ A W nu -
            ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      exact Finset.sum_le_sum hpointwise

/-- Physical-phase specialization of the arbitrary-phase intrinsic theorem. -/
theorem abs_ndA5TubeRawMass_sub_sum_fixedGaussian_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M S : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hS : 0 < S)
    (hclose : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      |(nu : ℝ) - S| ≤ S / 3)
    (heta : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA6LocalEta nu
        (Int.natAbs (ndA5StrictAffineSweep
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu)) ≤ 1)
    (hzeta : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA6GaussianRecenterZeta (nu : ℝ) S
        (ndA5StrictAffineSweep
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) ≤ 1) :
    |ndA5TubeRawMass
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) -
        ∑ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
          ndA6Gaussian S
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)| ≤
      ∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
        ndA6Gaussian S
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) *
          (ndA6LocalRelativeError nu
                (Int.natAbs (ndA5StrictAffineSweep
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu)) *
              (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ) S
                (ndA5StrictAffineSweep
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)) +
            2 * ndA6GaussianRecenterZeta (nu : ℝ) S
              (ndA5StrictAffineSweep
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)) := by
  exact abs_ndA5TubeRawMass_sub_sum_fixedGaussian_le_of_analytic
    (NDA5InteriorTubeFacts.toAnalytic hTube) hS hclose heta hzeta

/-- Physical-band XI.3/XI.4 insertion, obtained from the intrinsic tube
estimate through the checked interior carrier equality. -/
theorem abs_ndA5BandRawMass_sub_sum_fixedGaussian_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M S : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hS : 0 < S)
    (hclose : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      |(nu : ℝ) - S| ≤ S / 3)
    (heta : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA6LocalEta nu
        (Int.natAbs (ndA5StrictAffineSweep
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu)) ≤ 1)
    (hzeta : ∀ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA6GaussianRecenterZeta (nu : ℝ) S
        (ndA5StrictAffineSweep
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) ≤ 1) :
    |ndA5BandRawMass B branch C j M -
        ∑ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
          ndA6Gaussian S
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)| ≤
      ∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
        ndA6Gaussian S
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) *
          (ndA6LocalRelativeError nu
                (Int.natAbs (ndA5StrictAffineSweep
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu)) *
              (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ) S
                (ndA5StrictAffineSweep
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)) +
            2 * ndA6GaussianRecenterZeta (nu : ℝ) S
              (ndA5StrictAffineSweep
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)) := by
  rw [ndA5BandRawMass_eq_tubeRawMass_of_interior hTube]
  exact abs_ndA5TubeRawMass_sub_sum_fixedGaussian_le_of_interior
    hTube hS hclose heta hzeta

section Canaries

example :
    |(6 : ℝ) - 1| ≤ 1 * (1 * (1 + 2 * 1) + 2 * 1) := by
  norm_num

example : ¬ ndA6LocalEta 16 1 ≤ 1 := by
  norm_num [ndA6LocalEta]

example :
    |(64000 : ℝ) - 48000| ≤ 48000 / 3 ∧
      4 * 600 ≤ (64000 : ℕ) ∧
      ndA6LocalEta 64000 600 ≤ 1 ∧
      ndA6GaussianRecenterZeta 64000 48000 600 = 19 / 16 := by
  norm_num [ndA6LocalEta, ndA6GaussianRecenterZeta, abs_of_nonneg]

example :
    |(2 : ℝ) - 3| ≤ 3 / 3 ∧ ¬ |(3 : ℝ) - 2| ≤ 2 / 3 := by
  norm_num

end Canaries

end

end ND
end Erdos1135
