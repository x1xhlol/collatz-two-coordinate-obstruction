import Erdos1135.ND.Band.A5FirstShiftSourceIngress
import Erdos1135.ND.Band.A6PhysicalInteriorEventual
import Erdos1135.ND.Discrepancy.A5TwoProfileFlat

/-!
# A5 Two-Profile A6 Centering

This leaf converts both checked raw two-profile endpoints from their common
base mass `Z0` to the deterministic centers in frozen v10.  A6 is used only
for the base physical mass.  The shifted analytic packet remains an original
J3 source packet, but no shifted mass, shifted normalizer, or shifted A6
estimate is introduced.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- A single nonnegative profile scale transports a raw center through the
base A6 mass estimate. -/
private theorem abs_sub_div_logFourThirds_le_of_mass_center
    {R Z x E EA6 : ℝ} (hx : 0 ≤ x)
    (hR : |R - Z * (x / Real.log 2)| ≤ E)
    (hZ : |Z - 1 / ndA5PhaseDelta| ≤ EA6) :
    |R - x / ndA5LogFourThirds| ≤
      E + (x / Real.log 2) * EA6 := by
  let mu := x / Real.log 2
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hmu : 0 ≤ mu := by
    dsimp [mu]
    exact div_nonneg hx hlogTwo.le
  have hscale :
      x / ndA5LogFourThirds =
        mu * (1 / ndA5PhaseDelta) := by
    dsimp [mu]
    rw [ndA5LogFourThirds_eq_phaseDelta_mul_logTwo]
    field_simp [hlogTwo.ne', ndA5PhaseDelta_mem_Ioo.1.ne']
    <;> ring
  calc
    |R - x / ndA5LogFourThirds| =
        |(R - Z * mu) +
          mu * (Z - 1 / ndA5PhaseDelta)| := by
      rw [hscale]
      congr 1
      ring
    _ ≤ |R - Z * mu| +
          |mu * (Z - 1 / ndA5PhaseDelta)| :=
      abs_add_le _ _
    _ = |R - Z * mu| +
          mu * |Z - 1 / ndA5PhaseDelta| := by
      rw [abs_mul, abs_of_nonneg hmu]
    _ ≤ E + mu * EA6 :=
      add_le_add hR (mul_le_mul_of_nonneg_left hZ hmu)

/-- The reciprocal two-profile endpoint centered at `beta / log(4/3)`.
Only the base physical mass is compared with `1 / delta`; the existing
profile errors retain their original `Z0` factors. -/
theorem
    abs_sum_ndA5NominalStrictBandRawQ_sub_beta_div_logFourThirds_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C M EA6 c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube0 : NDA5InteriorTubeFacts B j branch C M)
    (hTube1 : NDA5AnalyticTubeFacts B C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1))
    (hA6 :
      |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤ EA6) :
    |(∑ nu ∈
        ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C) ∪
          ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1)
            (ndA5TubeWidth B C),
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C) nu r) -
      ndA5BandBeta B branch / ndA5LogFourThirds| ≤
      (ndA5TubeRawMass
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) *
        (ndEndpointDbar c kappa
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
                (ndA5TubeWidth B C) : ℝ))) +
        (2 *
            (ndA5TubeWidth B C /
              (ndA5TubeLo
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                (ndA5TubeWidth B C) : ℝ)) *
            ndA5TubeRawMass
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
              (ndA5TubeWidth B C) +
          24 / Real.sqrt (Tao.taoSection5N0 B : ℝ))) +
        (ndA5BandBeta B branch / Real.log 2) * EA6 := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let I1 := ndA5FullTube (A + 1) W
  let Z0 := ndA5TubeRawMass A W
  let beta := ndA5BandBeta B branch
  let R := ∑ nu ∈ I0 ∪ I1,
    ∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandRawQTerm B branch A W nu r
  let E := Z0 *
      (ndEndpointDbar c kappa I0.card *
        (64 * (I0.card : ℝ) * W /
          (ndA5TubeLo A W : ℝ))) +
    (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
      24 / Real.sqrt (Tao.taoSection5N0 B : ℝ))
  have hTube1' : NDA5AnalyticTubeFacts B C (A + 1) := by
    simpa [A] using hTube1
  have hProfile0 :=
    abs_sum_ndA5NominalStrictBandRawQ_sub_mass_mul_mean_le_of_analytic
      (branch := branch) hPhase hB hlogB hTube0.toAnalytic hTube1'
  have hProfile : |R - Z0 * (beta / Real.log 2)| ≤ E := by
    simpa [R, E, A, W, I0, I1, Z0, beta] using hProfile0
  have hA6Z : |Z0 - 1 / ndA5PhaseDelta| ≤ EA6 := by
    have hA6' := hA6
    rw [ndA5BandRawMass_eq_tubeRawMass_of_interior hTube0] at hA6'
    simpa [A, W, Z0] using hA6'
  have hbeta0 : 0 ≤ beta := by
    simpa [beta] using ndA5BandBeta_nonneg hB branch
  have hcentered :=
    abs_sub_div_logFourThirds_le_of_mass_center
      (R := R) (Z := Z0) (x := beta) (E := E) (EA6 := EA6)
      hbeta0 hProfile hA6Z
  simpa [R, E, A, W, I0, I1, Z0, beta] using hcentered

/-- The flat two-profile endpoint centered at
`(exp beta - 1) / log(4/3)`.  The A6 charge is exactly the checked flat mean
times the base A6 error. -/
theorem
    abs_sum_ndA5NominalStrictBandFlatRawQ_sub_exp_sub_one_div_logFourThirds_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C M EA6 c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube0 : NDA5InteriorTubeFacts B j branch C M)
    (hTube1 : NDA5AnalyticTubeFacts B C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1))
    (hA6 :
      |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤ EA6) :
    |(∑ nu ∈
        ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C) ∪
          ndA5FullTube
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1)
            (ndA5TubeWidth B C),
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C) nu r) -
      (Real.exp (ndA5BandBeta B branch) - 1) /
        ndA5LogFourThirds| ≤
      (ndA5TubeRawMass
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) *
        ((2 * Real.exp (ndA5BandBeta B branch) - 1) *
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
                (ndA5TubeWidth B C) : ℝ))) +
        Real.exp (ndA5BandBeta B branch) *
          (2 *
              (ndA5TubeWidth B C /
                (ndA5TubeLo
                  (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                  (ndA5TubeWidth B C) : ℝ)) *
              ndA5TubeRawMass
                (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                (ndA5TubeWidth B C) +
            24 / Real.sqrt (Tao.taoSection5N0 B : ℝ))) +
        ndA5FlatPhaseMean (ndA5BandBeta B branch) * EA6 := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let I1 := ndA5FullTube (A + 1) W
  let Z0 := ndA5TubeRawMass A W
  let beta := ndA5BandBeta B branch
  let R := ∑ nu ∈ I0 ∪ I1,
    ∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandFlatRawQTerm B branch A W nu r
  let E := Z0 *
      ((2 * Real.exp beta - 1) *
        ndEndpointDbar c kappa I0.card *
        (64 * (I0.card : ℝ) * W /
          (ndA5TubeLo A W : ℝ))) +
    Real.exp beta *
      (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
        24 / Real.sqrt (Tao.taoSection5N0 B : ℝ))
  have hTube1' : NDA5AnalyticTubeFacts B C (A + 1) := by
    simpa [A] using hTube1
  have hProfile0 :=
    abs_sum_ndA5NominalStrictBandFlatRawQ_sub_mass_mul_mean_le_of_analytic
      (branch := branch) hPhase hB hlogB hTube0.toAnalytic hTube1'
  have hProfile :
      |R - Z0 * ((Real.exp beta - 1) / Real.log 2)| ≤ E := by
    simpa [R, E, A, W, I0, I1, Z0, beta,
      ndA5FlatPhaseMean] using hProfile0
  have hA6Z : |Z0 - 1 / ndA5PhaseDelta| ≤ EA6 := by
    have hA6' := hA6
    rw [ndA5BandRawMass_eq_tubeRawMass_of_interior hTube0] at hA6'
    simpa [A, W, Z0] using hA6'
  have hbeta0 : 0 ≤ beta := by
    simpa [beta] using ndA5BandBeta_nonneg hB branch
  have hx0 : 0 ≤ Real.exp beta - 1 :=
    sub_nonneg.mpr (Real.one_le_exp hbeta0)
  have hcentered :=
    abs_sub_div_logFourThirds_le_of_mass_center
      (R := R) (Z := Z0) (x := Real.exp beta - 1)
      (E := E) (EA6 := EA6) hx0 hProfile hA6Z
  simpa [R, E, A, W, I0, I1, Z0, beta,
    ndA5FlatPhaseMean] using hcentered

/-- Fixed-`C` paired reciprocal and flat A6 centers.  The two conclusions use
the same base physical A6 estimate and the same original-J3 shifted packet. -/
theorem eventually_ndA5TwoProfileA6
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa : ℝ} (hPhase : PhaseGap c kappa) :
    ∀ᶠ B : ℕ in Filter.atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ),
        j < ndA5BandCount B branch →
          ∀ M : ℝ, 0 < M →
            |ndA5InteriorShift B M| ≤
                (4 / 25 : ℝ) * ndA5TubeWidth B C →
              (|(∑ nu ∈
                  ndA5FullTube
                      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                      (ndA5TubeWidth B C) ∪
                    ndA5FullTube
                      (ndA5PhysicalPhase
                        (ndA5BandLower B branch j) M + 1)
                      (ndA5TubeWidth B C),
                  ∑ r ∈ Finset.range 2,
                    ndA5NominalStrictBandRawQTerm B branch
                      (ndA5PhysicalPhase
                        (ndA5BandLower B branch j) M)
                      (ndA5TubeWidth B C) nu r) -
                ndA5BandBeta B branch / ndA5LogFourThirds| ≤
                (ndA5TubeRawMass
                    (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                    (ndA5TubeWidth B C) *
                  (ndEndpointDbar c kappa
                      (ndA5FullTube
                        (ndA5PhysicalPhase
                          (ndA5BandLower B branch j) M)
                        (ndA5TubeWidth B C)).card *
                    (64 *
                      ((ndA5FullTube
                        (ndA5PhysicalPhase
                          (ndA5BandLower B branch j) M)
                        (ndA5TubeWidth B C)).card : ℝ) *
                      ndA5TubeWidth B C /
                        (ndA5TubeLo
                          (ndA5PhysicalPhase
                            (ndA5BandLower B branch j) M)
                          (ndA5TubeWidth B C) : ℝ))) +
                  (2 *
                      (ndA5TubeWidth B C /
                        (ndA5TubeLo
                          (ndA5PhysicalPhase
                            (ndA5BandLower B branch j) M)
                          (ndA5TubeWidth B C) : ℝ)) *
                      ndA5TubeRawMass
                        (ndA5PhysicalPhase
                          (ndA5BandLower B branch j) M)
                        (ndA5TubeWidth B C) +
                    24 / Real.sqrt (Tao.taoSection5N0 B : ℝ))) +
                  (ndA5BandBeta B branch / Real.log 2) *
                    (3650000 * (C + C ^ 3) * ndA6PhysicalRate B)) ∧
              (|(∑ nu ∈
                  ndA5FullTube
                      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                      (ndA5TubeWidth B C) ∪
                    ndA5FullTube
                      (ndA5PhysicalPhase
                        (ndA5BandLower B branch j) M + 1)
                      (ndA5TubeWidth B C),
                  ∑ r ∈ Finset.range 2,
                    ndA5NominalStrictBandFlatRawQTerm B branch
                      (ndA5PhysicalPhase
                        (ndA5BandLower B branch j) M)
                      (ndA5TubeWidth B C) nu r) -
                (Real.exp (ndA5BandBeta B branch) - 1) /
                  ndA5LogFourThirds| ≤
                (ndA5TubeRawMass
                    (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
                    (ndA5TubeWidth B C) *
                  ((2 * Real.exp (ndA5BandBeta B branch) - 1) *
                    ndEndpointDbar c kappa
                      (ndA5FullTube
                        (ndA5PhysicalPhase
                          (ndA5BandLower B branch j) M)
                        (ndA5TubeWidth B C)).card *
                    (64 *
                      ((ndA5FullTube
                        (ndA5PhysicalPhase
                          (ndA5BandLower B branch j) M)
                        (ndA5TubeWidth B C)).card : ℝ) *
                      ndA5TubeWidth B C /
                        (ndA5TubeLo
                          (ndA5PhysicalPhase
                            (ndA5BandLower B branch j) M)
                          (ndA5TubeWidth B C) : ℝ))) +
                  Real.exp (ndA5BandBeta B branch) *
                    (2 *
                        (ndA5TubeWidth B C /
                          (ndA5TubeLo
                            (ndA5PhysicalPhase
                              (ndA5BandLower B branch j) M)
                            (ndA5TubeWidth B C) : ℝ)) *
                        ndA5TubeRawMass
                          (ndA5PhysicalPhase
                            (ndA5BandLower B branch j) M)
                          (ndA5TubeWidth B C) +
                      24 / Real.sqrt (Tao.taoSection5N0 B : ℝ))) +
                  ndA5FlatPhaseMean (ndA5BandBeta B branch) *
                    (3650000 * (C + C ^ 3) * ndA6PhysicalRate B)) := by
  have hCpos : 0 < C := by linarith
  have hlog : ∀ᶠ B : ℕ in Filter.atTop,
      (300000 : ℝ) ≤ Real.log B :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto
        (fun B : ℕ => (B : ℝ)) Filter.atTop Filter.atTop)).eventually_ge_atTop
          300000
  filter_upwards
    [Filter.eventually_ge_atTop (1 : ℕ), hlog,
      eventually_three_mul_ndA5TubeWidth_le_log C hCpos,
      eventually_a6PhysicalInterior C hC]
      with B hB hlogB hpadding hA6
  intro branch j hj M hM hshift
  have hTube0 : NDA5InteriorTubeFacts B j branch C M :=
    ndA5InteriorTubeFacts_of_guards
      hB hlogB hC hM hpadding hshift hj
  have hTube1 : NDA5AnalyticTubeFacts B C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1) :=
    ndA5AnalyticTubeFacts_add_one_of_sourceGuards
      hB hlogB hC hM hpadding hshift hj
  have hA6' := hA6 branch j hj M hM hshift
  exact
    ⟨abs_sum_ndA5NominalStrictBandRawQ_sub_beta_div_logFourThirds_le_of_interior
        hPhase hB hlogB hTube0 hTube1 hA6',
      abs_sum_ndA5NominalStrictBandFlatRawQ_sub_exp_sub_one_div_logFourThirds_le_of_interior
        hPhase hB hlogB hTube0 hTube1 hA6'⟩

end

end ND
end Erdos1135
