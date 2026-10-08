import Erdos1135.ND.Discrepancy.A5Padding
import Erdos1135.ND.Discrepancy.FlatPhaseProfile

/-!
# Concrete A5 Profiles after Equal Padding

This leaf specializes the checked equal-padding/zero-head Abel seam to the two
literal prefix producers already available: the open-lattice count and the
flat exponential profile.  It exports source-carrier sums minus their exact
means and stops before rate absorption or reciprocal-atom pairing.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

private theorem sum_mul_sub_mean_eq_sum_mul_centered
    (S : Finset ℕ) (w F : ℕ → ℝ) (mean : ℝ)
    (hsum : (∑ n ∈ S, w n) = 1) :
    (∑ n ∈ S, w n * F n) - mean =
      ∑ n ∈ S, w n * (F n - mean) := by
  have hmean : (∑ n ∈ S, w n * mean) = mean := by
    rw [← Finset.sum_mul, hsum, one_mul]
  calc
    (∑ n ∈ S, w n * F n) - mean =
        (∑ n ∈ S, w n * F n) -
          ∑ n ∈ S, w n * mean := by
      rw [hmean]
    _ = ∑ n ∈ S, (w n * F n - w n * mean) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ n ∈ S, w n * (F n - mean) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring

private theorem abs_sum_ndA5NormalizedQ_mul_openLattice_centered_le_of_analytic
    {B : ℕ} {C A : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5AnalyticTubeFacts B C A)
    (phi : UnitAddCircle) (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 2) :
    |∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA5NormalizedQ A (ndA5TubeWidth B C) nu *
        (ndA5OpenLatticeCount b
            (ndUnitRep (ndPhaseOrbit phi nu)) -
          b / Real.log 2)| ≤
      ndEndpointDbar c kappa
          (ndA5FullTube A (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) := by
  let W := ndA5TubeWidth B C
  let s := (ndA5FullTube A W).card
  let gamma : UnitAddCircle → ℝ := fun x =>
    ndA5OpenLatticeCount b (ndUnitRep x) - b / Real.log 2
  let Bseq : ℕ → ℝ := fun n =>
    gamma (ndPhaseOrbit (ndA5EqualPaddedAnchor phi A W) n)
  have hW : 0 < W := by
    simpa [W] using hTube.width_pos
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [W] using hTube.nonempty
  have hAbel := ndA5EqualPaddedOmega_zeroHeadAbel
    (A := A) (W := W) hne Bseq (ndEndpointDbar c kappa) 1
      (by norm_num)
      (ndEndpointDbar_nonneg hPhase)
      (antitoneOn_ndEndpointDbar hPhase)
      (by
        intro m hm hmV
        simpa [Bseq, gamma] using
          abs_sum_ndA5OpenLatticeCount_ndPhaseOrbit_le_endpointDbar
            hPhase (ndA5EqualPaddedAnchor phi A W) b hb m hm)
  have hreindex := sum_ndA5EqualPaddedOmega_phase_reindex
    hW hne phi gamma
  rw [hreindex] at hAbel
  have hfactor :=
    ndAbsAbelFactor_ndA5EqualPaddedOmega_le_of_analytic hTube
  have hfactorLocal :
      ndAbsAbelFactor (ndA5EqualPaddedOmega A W)
          (ndA5EqualPaddedLength A W) ≤
        64 * (s : ℝ) * W / (ndA5TubeLo A W : ℝ) := by
    simpa [W, s] using hfactor
  have hD := ndEndpointDbar_nonneg hPhase s
  have hscaled := mul_le_mul_of_nonneg_left
    hfactorLocal hD
  dsimp [s] at hscaled
  simp only [one_mul] at hAbel
  simpa [W, s, gamma, Bseq] using hAbel.trans hscaled

private theorem abs_sum_ndA5NormalizedQ_mul_openLattice_centered_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (phi : UnitAddCircle) (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 2) :
    |∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA5NormalizedQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) nu *
        (ndA5OpenLatticeCount b
            (ndUnitRep (ndPhaseOrbit phi nu)) -
          b / Real.log 2)| ≤
      ndEndpointDbar c kappa
          (ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
              (ndA5TubeWidth B C) : ℝ)) := by
  simpa using
    abs_sum_ndA5NormalizedQ_mul_openLattice_centered_le_of_analytic
      hPhase (NDA5InteriorTubeFacts.toAnalytic hTube) phi b hb

private theorem abs_sum_ndA5NormalizedQ_mul_flat_centered_le_of_analytic
    {B : ℕ} {C A : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5AnalyticTubeFacts B C A)
    (phi : UnitAddCircle) (beta : ℝ)
    (hbeta : beta ∈ Set.Icc (0 : ℝ) 2) :
    |∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA5NormalizedQ A (ndA5TubeWidth B C) nu *
        ndA5CenteredFlatPhaseProfile beta
          (ndUnitRep (ndPhaseOrbit phi nu))| ≤
      (2 * Real.exp beta - 1) *
        ndEndpointDbar c kappa
          (ndA5FullTube A (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) := by
  let W := ndA5TubeWidth B C
  let s := (ndA5FullTube A W).card
  let Q := 2 * Real.exp beta - 1
  let gamma : UnitAddCircle → ℝ := fun x =>
    ndA5CenteredFlatPhaseProfile beta (ndUnitRep x)
  let Bseq : ℕ → ℝ := fun n =>
    gamma (ndPhaseOrbit (ndA5EqualPaddedAnchor phi A W) n)
  have hW : 0 < W := by
    simpa [W] using hTube.width_pos
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [W] using hTube.nonempty
  have hQ : 0 ≤ Q := by
    have hexp : 1 ≤ Real.exp beta := Real.one_le_exp hbeta.1
    dsimp [Q]
    linarith
  have hAbel := ndA5EqualPaddedOmega_zeroHeadAbel
    (A := A) (W := W) hne Bseq (ndEndpointDbar c kappa) Q
      hQ
      (ndEndpointDbar_nonneg hPhase)
      (antitoneOn_ndEndpointDbar hPhase)
      (by
        intro m hm hmV
        simpa [Bseq, gamma, Q] using
          abs_sum_ndA5CenteredFlatPhaseProfile_ndPhaseOrbit_le_endpointDbar
            hPhase (ndA5EqualPaddedAnchor phi A W) beta hbeta m hm)
  have hreindex := sum_ndA5EqualPaddedOmega_phase_reindex
    hW hne phi gamma
  rw [hreindex] at hAbel
  have hfactor :=
    ndAbsAbelFactor_ndA5EqualPaddedOmega_le_of_analytic hTube
  have hfactorLocal :
      ndAbsAbelFactor (ndA5EqualPaddedOmega A W)
          (ndA5EqualPaddedLength A W) ≤
        64 * (s : ℝ) * W / (ndA5TubeLo A W : ℝ) := by
    simpa [W, s] using hfactor
  have hQD : 0 ≤ Q * ndEndpointDbar c kappa s :=
    mul_nonneg hQ (ndEndpointDbar_nonneg hPhase s)
  have hscaled := mul_le_mul_of_nonneg_left
    hfactorLocal hQD
  dsimp [s] at hscaled
  simpa [W, s, Q, gamma, Bseq] using hAbel.trans hscaled

private theorem abs_sum_ndA5NormalizedQ_mul_flat_centered_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (phi : UnitAddCircle) (beta : ℝ)
    (hbeta : beta ∈ Set.Icc (0 : ℝ) 2) :
    |∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA5NormalizedQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) nu *
        ndA5CenteredFlatPhaseProfile beta
          (ndUnitRep (ndPhaseOrbit phi nu))| ≤
      (2 * Real.exp beta - 1) *
        ndEndpointDbar c kappa
          (ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
              (ndA5TubeWidth B C) : ℝ)) := by
  simpa using
    abs_sum_ndA5NormalizedQ_mul_flat_centered_le_of_analytic
      hPhase (NDA5InteriorTubeFacts.toAnalytic hTube) phi beta hbeta

/-- The normalized source carrier applied to the literal open-lattice count,
centered at its exact mean.  The prefix coefficient is exactly one. -/
theorem abs_sum_ndA5NormalizedQ_mul_openLattice_sub_mean_le_of_analytic
    {B : ℕ} {C A : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5AnalyticTubeFacts B C A)
    (phi : UnitAddCircle) (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 2) :
    |(∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA5NormalizedQ A (ndA5TubeWidth B C) nu *
        ndA5OpenLatticeCount b
          (ndUnitRep (ndPhaseOrbit phi nu))) -
      b / Real.log 2| ≤
      ndEndpointDbar c kappa
          (ndA5FullTube A (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) := by
  have hsum := sum_ndA5NormalizedQ_eq_one_of_analytic hTube
  rw [sum_mul_sub_mean_eq_sum_mul_centered _ _ _ _ hsum]
  exact abs_sum_ndA5NormalizedQ_mul_openLattice_centered_le_of_analytic
    hPhase hTube phi b hb

theorem abs_sum_ndA5NormalizedQ_mul_openLattice_sub_mean_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (phi : UnitAddCircle) (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 2) :
    |(∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA5NormalizedQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) nu *
        ndA5OpenLatticeCount b
          (ndUnitRep (ndPhaseOrbit phi nu))) -
      b / Real.log 2| ≤
      ndEndpointDbar c kappa
          (ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
              (ndA5TubeWidth B C) : ℝ)) := by
  simpa using
    abs_sum_ndA5NormalizedQ_mul_openLattice_sub_mean_le_of_analytic
      hPhase (NDA5InteriorTubeFacts.toAnalytic hTube) phi b hb

/-- The normalized source carrier applied to the literal flat profile,
centered at its exact deterministic mean. -/
theorem abs_sum_ndA5NormalizedQ_mul_flat_sub_mean_le_of_analytic
    {B : ℕ} {C A : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5AnalyticTubeFacts B C A)
    (phi : UnitAddCircle) (beta : ℝ)
    (hbeta : beta ∈ Set.Icc (0 : ℝ) 2) :
    |(∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA5NormalizedQ A (ndA5TubeWidth B C) nu *
        ndA5FlatPhaseProfile beta
          (ndUnitRep (ndPhaseOrbit phi nu))) -
      ndA5FlatPhaseMean beta| ≤
      (2 * Real.exp beta - 1) *
        ndEndpointDbar c kappa
          (ndA5FullTube A (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) := by
  have hsum := sum_ndA5NormalizedQ_eq_one_of_analytic hTube
  rw [sum_mul_sub_mean_eq_sum_mul_centered _ _ _ _ hsum]
  exact abs_sum_ndA5NormalizedQ_mul_flat_centered_le_of_analytic
    hPhase hTube phi beta hbeta

theorem abs_sum_ndA5NormalizedQ_mul_flat_sub_mean_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (phi : UnitAddCircle) (beta : ℝ)
    (hbeta : beta ∈ Set.Icc (0 : ℝ) 2) :
    |(∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA5NormalizedQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) nu *
        ndA5FlatPhaseProfile beta
          (ndUnitRep (ndPhaseOrbit phi nu))) -
      ndA5FlatPhaseMean beta| ≤
      (2 * Real.exp beta - 1) *
        ndEndpointDbar c kappa
          (ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
              (ndA5TubeWidth B C) : ℝ)) := by
  simpa using
    abs_sum_ndA5NormalizedQ_mul_flat_sub_mean_le_of_analytic
      hPhase (NDA5InteriorTubeFacts.toAnalytic hTube) phi beta hbeta

end

end ND
end Erdos1135
