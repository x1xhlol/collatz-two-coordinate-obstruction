import Erdos1135.ND.Band.A5PhysicalPaddingRate
import Erdos1135.ND.Band.A6PhysicalInteriorRate

/-!
# A6 Eventual Physical Interior Endpoint

This leaf intersects the checked fixed-`C` padding and physical interior
producers.  It removes the final B-scale premise while preserving every
pointwise source admissibility guard.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Fixed-`C` physical A6 interior estimate with no remaining eventual
padding premise.  Valid-band, positive-shift, and interior-shift hypotheses
remain visible at their source-facing binders. -/
theorem eventually_a6PhysicalInterior
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in Filter.atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ),
        j < ndA5BandCount B branch →
          ∀ M : ℝ, 0 < M →
            |ndA5InteriorShift B M| ≤
                (4 / 25 : ℝ) * ndA5TubeWidth B C →
              |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤
                3650000 * (C + C ^ 3) * ndA6PhysicalRate B := by
  have hCpos : 0 < C := by linarith
  filter_upwards
    [eventually_three_mul_ndA5TubeWidth_le_log C hCpos,
      eventually_a6PhysicalInterior_of_sourceGuards C hC]
      with B hpadding hsource
  exact hsource hpadding

end

end ND
end Erdos1135
