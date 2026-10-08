import Erdos1135.Tao.Section5.BranchPassEvent

/-!
# Section 5 Branch Passage Full-L1 Comparison

This leaf applies the neutral finite Hahn theorem once to the arbitrary-event
comparison between the two canonical Section 5 passage laws. It records the
raw full-L1 ledger and stops before rate absorption or Proposition 1.11
packaging.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- The two canonical Section 5 passage laws satisfy the raw full-L1 bound
obtained by applying one Hahn factor `2` to the no-hit-free event estimate. -/
theorem taoSection5_passWindowTV_alpha_alphaSq_le_capped_of_mixing
    {A B : ℕ} {Cmix : ℝ}
    (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (boundaryFacts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (failureFacts : TaoSection5PassTypicalFailureFacts B)
    (hmix : syracFineScaleMixingAt A Cmix) (hCmix : 0 ≤ Cmix)
    (hratioAlpha :
      (Fintype.card {n // n ∈ taoSection5PassTimes B .alpha} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B .alpha)
              (taoSection5SourceHi B .alpha)) ≤ 9)
    (hratioAlphaSq :
      (Fintype.card {n // n ∈ taoSection5PassTimes B .alphaSq} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B .alphaSq)
              (taoSection5SourceHi B .alphaSq)) ≤ 9) :
    let hB := boundaryFacts.residue.one_le_B
    let hmassAlpha := boundaryFacts.residue.mass_pos .alpha
    let hmassAlphaSq := boundaryFacts.residue.mass_pos .alphaSq
    syracusePassWindowTV B
        (taoSection5SourceLo B .alpha)
        (taoSection5SourceHi B .alpha)
        (taoSection5SourceLo B .alphaSq)
        (taoSection5SourceHi B .alphaSq)
        hB hmassAlpha hmassAlphaSq ≤
      64184 * taoSection5PowerInteriorDelta B +
        180 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
        3680000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
        2 * (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
  dsimp only
  let hB := boundaryFacts.residue.one_le_B
  let hmassAlpha := boundaryFacts.residue.mass_pos .alpha
  let hmassAlphaSq := boundaryFacts.residue.mass_pos .alphaSq
  let p := syracusePassLocationLaw
    (taoSection5SourceLo B .alpha)
    (taoSection5SourceHi B .alpha) B hB hmassAlpha
  let q := syracusePassLocationLaw
    (taoSection5SourceLo B .alphaSq)
    (taoSection5SourceHi B .alphaSq) B hB hmassAlphaSq
  let ε := 32092 * taoSection5PowerInteriorDelta B +
    90 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
    1840000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
    (B : ℝ) ^ (-(4 / 5 : ℝ))
  change taoTV p q ≤
    64184 * taoSection5PowerInteriorDelta B +
      180 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
      3680000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
      2 * (B : ℝ) ^ (-(4 / 5 : ℝ))
  have hevent : ∀ E : Set {M : ℕ // M ≤ B},
      |pmfProb p E - pmfProb q E| ≤ ε := by
    intro E
    simpa only [p, q, ε, hB, hmassAlpha, hmassAlphaSq] using
      (abs_taoSection5_totalPassMass_sub_totalPassMass_le_capped_of_mixing
        partitionFacts affineFacts boundaryFacts failureFacts
        .alpha .alphaSq E hmix hCmix hratioAlpha hratioAlphaSq)
  calc
    taoTV p q ≤ 2 * ε :=
      taoTV_le_two_mul_of_event_discrepancy p q hevent
    _ = 64184 * taoSection5PowerInteriorDelta B +
        180 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
        3680000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
        2 * (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
      dsimp only [ε]
      ring

end

end Tao
end Erdos1135
