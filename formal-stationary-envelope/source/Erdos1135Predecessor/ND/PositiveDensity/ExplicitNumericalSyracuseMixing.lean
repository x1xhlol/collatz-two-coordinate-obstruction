/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitNumericalPrimitiveDecay
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitSection6Mixing

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

noncomputable section

@[irreducible] def explicitSection6MixingCoefficientAt (C : ℕ) : ℕ :=
  2 * (C * 20 ^ 6409) + 2 + 2 ^ 481

private theorem coefficient_cast (C B W : ℕ) :
    ((2 * (C * 20 ^ B) + 2 + 2 ^ W : ℕ) : ℝ) =
      2 * ((C : ℝ) * 20 ^ B) + 2 + 2 ^ W := by
  push_cast
  rfl

theorem explicitSection6_mixing_nat (C : ℕ)
    (hdecay : syracPMFPrimitivePolynomialDecayAt 6409 (C : ℝ)) :
    syracFineScaleMixingAt 6 (explicitSection6MixingCoefficientAt C : ℝ) := by
  have h := explicitSection6_mixing hdecay (Nat.cast_nonneg C)
  delta explicitSection6MixingCoefficientAt
  exact (congrArg (syracFineScaleMixingAt 6) (coefficient_cast C 6409 481)).mpr h

@[irreducible] def explicitSyracuseMixingCoefficient : ℕ :=
  explicitSection6MixingCoefficientAt explicitRenewalPrimitiveCoefficient

theorem explicitSyracuseMixing_six :
    syracFineScaleMixingAt 6 (explicitSyracuseMixingCoefficient : ℝ) := by
  delta explicitSyracuseMixingCoefficient
  exact explicitSection6_mixing_nat _ explicitRenewal_numericalPrimitiveDecay

end

end Erdos1135Predecessor.ND.PositiveDensity
