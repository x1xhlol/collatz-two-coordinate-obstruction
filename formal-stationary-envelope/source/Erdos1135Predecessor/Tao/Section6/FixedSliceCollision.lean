/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.AmbientTailDecay
import Erdos1135Predecessor.Tao.Section6.FiniteFourierCollision
import Erdos1135Predecessor.Tao.Section6.GatedSourceConvolution
import Erdos1135Predecessor.Tao.Section6.HeadSubmass

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoSection6FixedSliceOscillation_sq_le
    {B : ℕ} {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt B C)
    (hC : 0 ≤ C)
    {CA : ℝ} {T k l m : ℕ}
    (hmn : m ≤ T + (k + 1))
    (hhead : k + 1 ≤ m)
    (hm : 9 * (T + (k + 1)) ≤ 10 * m)
    (hk : 20 * k ≤ 17 * (T + (k + 1)))
    (hheadL2 :
      (∑ y : ZMod (3 ^ (T + (k + 1))),
        (taoSection6HeadSubmass CA (T + (k + 1)) k l y) ^ 2) ≤
          (1 / 2 : ℝ) ^ l) :
    taoZModPowOscillation m (T + (k + 1))
        (taoSection6GatedSourceSubmass CA T k l) ^ 2 ≤
      (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        (1 / 2 : ℝ) ^ l := by
  let tau : ZMod (3 ^ (T + (k + 1))) → ℝ := fun z =>
    (taoSection6AmbientTailPMF (k + 1) T l z).toReal
  have hsource :
      taoSection6GatedSourceSubmass CA T k l =
        taoZModRawConvolution
          (taoSection6HeadSubmass CA (T + (k + 1)) k l) tau := by
    funext x
    simpa [tau] using
      taoSection6GatedSourceSubmass_eq_rawConvolution CA T k l x
  rw [hsource]
  have htail : ∀ xi : ZMod (3 ^ (T + (k + 1))),
      ¬zmodThreePowMultiple
          (T + (k + 1)) (T + (k + 1) - m) xi →
        ‖ZMod.dft (fun x => ((tau x : ℝ) : ℂ)) xi‖ ≤
          taoSection6TailDecayDelta C B (T + (k + 1)) := by
    intro xi hxi
    simpa [tau, pmfComplexMass] using
      hdecay.dft_taoSection6AmbientTailPMF_le
        hC hhead hm hk xi hxi
  have hcollision :=
    taoZModPowOscillation_rawConvolution_sq_le
      hmn
      (taoSection6HeadSubmass CA (T + (k + 1)) k l)
      tau
      (taoSection6TailDecayDelta_nonneg hC B (T + (k + 1)))
      htail
  calc
    taoZModPowOscillation m (T + (k + 1))
        (taoZModRawConvolution
          (taoSection6HeadSubmass CA (T + (k + 1)) k l)
          tau) ^ 2 ≤
      (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        ∑ y : ZMod (3 ^ (T + (k + 1))),
          (taoSection6HeadSubmass CA (T + (k + 1)) k l y) ^ 2 :=
      hcollision
    _ ≤ (taoSection6TailDecayDelta C B (T + (k + 1))) ^ 2 *
        (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        (1 / 2 : ℝ) ^ l := by
      exact mul_le_mul_of_nonneg_left hheadL2
        (mul_nonneg (sq_nonneg _) (by positivity))

end

end Tao

end Erdos1135Predecessor
