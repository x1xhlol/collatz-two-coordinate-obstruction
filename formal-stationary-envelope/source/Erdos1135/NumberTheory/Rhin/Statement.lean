import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rhin's linear-form statement

This file records the number-theoretic surface used by the G8 Rhin lane.  It
does not assert Rhin's proposition.

On printed p. 160 of Georges Rhin, *Approximants de Padé et mesures
effectives d'irrationalité* (1987), the proposition uses

`Λ = u₀ + u₁ log 2 + u₂ log 3` and `H = max (|u₁|, |u₂|) ≥ 2`.

Equation (7) states `|Λ| ≥ H⁻¹³·³`.  Equation (8) states the sharper
`|Λ| ≥ H⁻⁷·⁶¹⁶` only above an effectively calculable threshold.  The G8a
consumer below deliberately asks for less than equation (7): an unspecified
positive factor and an unspecified finite threshold at exponent `133 / 10`.
This weakening is sufficient because the completed adapter absorbs the finite
range using pointwise nonvanishing, without reconstructing Rhin's historical
table.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

/-- The integer linear form in `1`, `log 2`, and `log 3` from Rhin's
proposition on printed p. 160. -/
def linearForm (u₀ u₁ u₂ : ℤ) : ℝ :=
  (u₀ : ℝ) + (u₁ : ℝ) * Real.log 2 + (u₂ : ℝ) * Real.log 3

/-- Rhin's height, which excludes the constant coefficient `u₀`. -/
def linearFormHeight (u₁ u₂ : ℤ) : ℕ :=
  max u₁.natAbs u₂.natAbs

/-- The exact mathematical surface of Rhin's printed equation (7), retained
as a proposition rather than asserted as a theorem. -/
def PrintedUniformBound : Prop :=
  ∀ u₀ u₁ u₂ : ℤ,
    2 ≤ linearFormHeight u₁ u₂ →
      Real.rpow (linearFormHeight u₁ u₂ : ℝ) (-(133 / 10 : ℝ)) ≤
        |linearForm u₀ u₁ u₂|

/-- The weaker large-height interface consumed by G8a.

The factor and threshold are existential because G8a needs no displayed
constant and closes the complementary finite range abstractly. -/
def LargeHeightBound : Prop :=
  ∃ factor : ℝ, 0 < factor ∧
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ u₀ u₁ u₂ : ℤ,
        threshold ≤ linearFormHeight u₁ u₂ →
          factor *
              Real.rpow (linearFormHeight u₁ u₂ : ℝ)
                (-(133 / 10 : ℝ)) ≤
            |linearForm u₀ u₁ u₂|

/-- The G8a large-height interface is genuinely weaker than Rhin's printed
uniform equation (7); no finite-height table is used in this implication. -/
theorem largeHeightBound_of_printedUniformBound
    (hRhin : PrintedUniformBound) :
    LargeHeightBound := by
  refine ⟨1, by norm_num, 2, le_rfl, ?_⟩
  intro u₀ u₁ u₂ hHeight
  simpa using hRhin u₀ u₁ u₂ hHeight

end

end Rhin
end NumberTheory
end Erdos1135
