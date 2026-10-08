import Erdos1135.ND.PhaseGap
import Erdos1135.NumberTheory.Rhin.FiniteAbsorption
import Erdos1135.NumberTheory.Rhin.LiteralLargeHeight

/-!
# Rhin-to-PhaseGap adapter

This is the sole module that translates the number-theory Rhin definitions
into the ND `PhaseGap` vocabulary.  The theorem-variable adapters expose the
eventual and global bounds; `existsPhaseGapRhin` consumes the literal
large-height producer and supplies the unconditional existential witness.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Translate the P1 number-theory specialization into the ND names and the
phase exponent `1 - 143/10`. -/
theorem existsEventualPhaseGapRhin_of_largeHeightBound
    (hRhin : NumberTheory.Rhin.LargeHeightBound) :
    ∃ factor : ℝ, 0 < factor ∧
      ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ q : ℕ, threshold ≤ q →
          factor * Real.rpow (q : ℝ) (1 - (143 / 10 : ℝ)) ≤
            nearestIntegerNorm ((q : ℝ) * logTwoThree) := by
  rcases NumberTheory.Rhin.largeFrequencyPhaseBound_of_largeHeightBound
      hRhin with
    ⟨factor, hFactor, threshold, hTwoThreshold, hGap⟩
  refine ⟨factor, hFactor, threshold, hTwoThreshold, ?_⟩
  intro q hq
  simpa only [nearestIntegerNorm, logTwoThree,
    NumberTheory.Rhin.nearestIntegerNorm,
    NumberTheory.Rhin.logTwoThree,
    show (1 - (143 / 10 : ℝ)) = -(133 / 10 : ℝ) by norm_num] using
      hGap q hq

/-- Conditional G8a closure: a checked `LargeHeightBound` supplies the global
existential `PhaseGap` witness without a numerical low-frequency table. -/
theorem existsPhaseGapRhin_of_largeHeightBound
    (hRhin : NumberTheory.Rhin.LargeHeightBound) :
    ∃ c : ℝ, PhaseGap c (143 / 10 : ℝ) := by
  rcases NumberTheory.Rhin.existsGlobalPhaseBound_of_largeHeightBound
      hRhin with
    ⟨c, hcPos, hcOne, hGap⟩
  refine ⟨c, hcPos, hcOne, by norm_num, ?_⟩
  intro q hq
  simpa only [nearestIntegerNorm, logTwoThree,
    NumberTheory.Rhin.nearestIntegerNorm,
    NumberTheory.Rhin.logTwoThree,
    show (1 - (143 / 10 : ℝ)) = -(133 / 10 : ℝ) by norm_num] using
      hGap q hq

/-- G8a: the checked literal construction supplies an existential global
phase-gap witness without a numerical low-frequency table. -/
theorem existsPhaseGapRhin :
    ∃ c : ℝ, PhaseGap c (143 / 10 : ℝ) :=
  existsPhaseGapRhin_of_largeHeightBound
    NumberTheory.Rhin.literalRhinLargeHeightBound

end


end ND
end Erdos1135
