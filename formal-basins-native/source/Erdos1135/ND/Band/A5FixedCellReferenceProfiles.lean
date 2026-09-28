import Erdos1135.ND.Band.A5FixedCellTerminalDescent

/-!
# A5 Fixed-Cell Low-Reference Profiles

This leaf sums the already reconstructed fixed-cell Syracuse references over
terminal totals.  The result is fiber-free and exposes the same low-level
Syracuse kernel in the harmonic and flat profiles.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- The terminal-total sum of harmonic low references is the two strict raw
profiles weighted by the unconditioned level-`m` Syracuse law.  The low power
is `3^m`; strict activity remains at the original physical cell. -/
theorem sum_ndA5TerminalTotals_harmonicReference_eq_lowProfile
    {B n m : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : NDA5T2ScaleFacts B n C) :
    let nu := n - Tao.taoSection5M0 B
    let z := ndA5BandLower B branch j
    let W := ndA5TubeWidth B C
    let H := Tao.logFinsetMass (ndA5OddBand B branch j)
    (∑ L : {L // L ∈ ndA5TerminalTotals B C n},
        ndGeom2EndpointMass nu L.1 *
          ndPMFWeightedExpectation (Tao.syracPMF m)
            (fun X =>
              Tao.taoSection5PayloadFreeCoefficient m
                  (ndA5FixedCellEndpoints B branch j E nu L.1) X / H)) =
      ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((3 : ℝ) ^ m / ((M : ℝ) * H)) *
            ∑ r ∈ Finset.range 2,
              ndA5NominalStrictBandRawQTerm B branch
                (ndA5PhysicalPhase z M) W nu r) := by
  classical
  dsimp only
  let nu := n - Tao.taoSection5M0 B
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  calc
    _ = ∑ L : {L // L ∈ ndA5TerminalTotals B C n},
        ndGeom2EndpointMass nu L.1 *
          ∑ M ∈ Tao.taoSection5EPrime B E,
            (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
              (((3 : ℝ) ^ m / ((M : ℝ) * H)) *
                @ite ℝ
                  (ndA5NominalStrictBandLevel
                    (ndA5BandBeta B branch)
                    (ndA5PhysicalPhase z M) nu (L.1 : ℤ))
                  (Classical.propDecidable _) 1 0) := by
      apply Finset.sum_congr rfl
      intro L _hL
      rw [ndPMFWeightedExpectation_ndA5FixedCellHarmonicReference_low]
    _ = ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((3 : ℝ) ^ m / ((M : ℝ) * H)) *
            ∑ L : {L // L ∈ ndA5TerminalTotals B C n},
              ndGeom2EndpointMass nu L.1 *
                @ite ℝ
                  (ndA5NominalStrictBandLevel
                    (ndA5BandBeta B branch)
                  (ndA5PhysicalPhase z M) nu (L.1 : ℤ))
                  (Classical.propDecidable _) 1 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro M _hM
      apply Finset.sum_congr rfl
      intro L _hL
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro M _hM
      rw [sum_ndA5TerminalTotals_harmonicStrict_eq_range_two
        (branch := branch) (A := ndA5PhysicalPhase z M)
        hB hlogB ht2]

/-- The terminal-total sum of flat low references has the same level-`m`
Syracuse kernel and a single exponential inside the named flat raw profile. -/
theorem sum_ndA5TerminalTotals_flatReference_eq_lowProfile
    {B n m : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : NDA5T2ScaleFacts B n C)
    (hmnu : m ≤ n - Tao.taoSection5M0 B) :
    let nu := n - Tao.taoSection5M0 B
    let z := ndA5BandLower B branch j
    let W := ndA5TubeWidth B C
    let card := ((ndA5OddBand B branch j).card : ℝ)
    (∑ L : {L // L ∈ ndA5TerminalTotals B C n},
        ndGeom2EndpointMass nu L.1 *
          ndPMFWeightedExpectation (Tao.syracPMF m)
            (ndA5FixedCellFlatCoarseTest hmnu B branch j E L.1)) =
      ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((z * (3 : ℝ) ^ m) / ((M : ℝ) * card)) *
            ∑ r ∈ Finset.range 2,
              ndA5NominalStrictBandFlatRawQTerm B branch
                (ndA5PhysicalPhase z M) W nu r) := by
  classical
  dsimp only
  let nu := n - Tao.taoSection5M0 B
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let card := ((ndA5OddBand B branch j).card : ℝ)
  calc
    _ = ∑ L : {L // L ∈ ndA5TerminalTotals B C n},
        ndGeom2EndpointMass nu L.1 *
          ∑ M ∈ Tao.taoSection5EPrime B E,
            (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
              (((z * (3 : ℝ) ^ m) / ((M : ℝ) * card)) *
                @ite ℝ
                  (ndA5NominalStrictBandLevel
                    (ndA5BandBeta B branch)
                    (ndA5PhysicalPhase z M) nu (L.1 : ℤ))
                  (Classical.propDecidable _)
                  (Real.exp
                    (ndA5NominalAffinePosition z M nu L.1)) 0) := by
      apply Finset.sum_congr rfl
      intro L _hL
      rw [ndPMFWeightedExpectation_ndA5FixedCellFlatReference_low hmnu]
    _ = ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((z * (3 : ℝ) ^ m) / ((M : ℝ) * card)) *
            ∑ L : {L // L ∈ ndA5TerminalTotals B C n},
              ndGeom2EndpointMass nu L.1 *
                @ite ℝ
                  (ndA5NominalStrictBandLevel
                    (ndA5BandBeta B branch)
                    (ndA5PhysicalPhase z M) nu (L.1 : ℤ))
                  (Classical.propDecidable _)
                  (Real.exp
                    (ndA5NominalAffinePosition z M nu L.1)) 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro M _hM
      apply Finset.sum_congr rfl
      intro L _hL
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro M _hM
      rw [sum_ndA5TerminalTotals_flatStrict_eq_range_two
        (branch := branch) (z := z) (M := (M : ℝ))
        hB hlogB ht2]

end

end ND
end Erdos1135
