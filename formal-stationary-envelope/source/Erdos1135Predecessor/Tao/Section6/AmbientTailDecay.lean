/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.AmbientTailDFT
import Erdos1135Predecessor.Tao.Section6.ConductorFrequency

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

def taoSection6TailDecayDelta (C : ℝ) (B n : ℕ) : ℝ :=
  C * (20 : ℝ) ^ B / (n : ℝ) ^ B

theorem taoSection6TailDecayDelta_nonneg
    {C : ℝ} (hC : 0 ≤ C) (B n : ℕ) :
    0 ≤ taoSection6TailDecayDelta C B n := by
  unfold taoSection6TailDecayDelta
  positivity

theorem syracPMFPrimitivePolynomialDecayAt.dft_taoSection6AmbientTailPMF_le
    {B : ℕ} {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt B C)
    (hC : 0 ≤ C)
    {T k l m : ℕ}
    (hhead : k + 1 ≤ m)
    (hm : 9 * (T + (k + 1)) ≤ 10 * m)
    (hk : 20 * k ≤ 17 * (T + (k + 1)))
    (xi : ZMod (3 ^ (T + (k + 1))))
    (hxi : ¬zmodThreePowMultiple
      (T + (k + 1)) (T + (k + 1) - m) xi) :
    ‖ZMod.dft
        (pmfComplexMass
          (taoSection6AmbientTailPMF (k + 1) T l)) xi‖ ≤
      taoSection6TailDecayDelta C B (T + (k + 1)) := by
  rw [dft_taoSection6AmbientTailPMF]
  obtain ⟨r, j, hj, hrj, hfull, hr, hmkr, hnr, hbound⟩ :=
    hdecay.tail_scaled_frequency_le
      (n := T + (k + 1)) (m := m) (k := k) (T := T) (l := l)
      (by omega) hhead hm hk hxi
  have hn_pos : 0 < T + (k + 1) := by omega
  have hr_real_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hn_real_pos : 0 < ((T + (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hn_pos
  have hnr_real :
      ((T + (k + 1) : ℕ) : ℝ) ≤ (20 : ℝ) * (r : ℝ) := by
    exact_mod_cast hnr
  have hpow :
      (((T + (k + 1) : ℕ) : ℝ) ^ B) ≤
        (20 : ℝ) ^ B * (r : ℝ) ^ B := by
    calc
      (((T + (k + 1) : ℕ) : ℝ) ^ B) ≤
          ((20 : ℝ) * (r : ℝ)) ^ B := by gcongr
      _ = (20 : ℝ) ^ B * (r : ℝ) ^ B := by rw [mul_pow]
  have hr_pow_pos : 0 < (r : ℝ) ^ B := pow_pos hr_real_pos B
  have hn_pow_pos :
      0 < (((T + (k + 1) : ℕ) : ℝ) ^ B) :=
    pow_pos hn_real_pos B
  calc
    ‖ZMod.dft (pmfComplexMass (syracPMF T))
        (taoSection6TailScaledFrequency
          (by omega : T ≤ T + (k + 1)) l xi)‖ ≤
      C / (r : ℝ) ^ B := hbound
    _ ≤ C * (20 : ℝ) ^ B /
        (((T + (k + 1) : ℕ) : ℝ) ^ B) := by
      apply (div_le_div_iff₀ hr_pow_pos hn_pow_pos).2
      calc
        C * (((T + (k + 1) : ℕ) : ℝ) ^ B) ≤
            C * ((20 : ℝ) ^ B * (r : ℝ) ^ B) :=
          mul_le_mul_of_nonneg_left hpow hC
        _ = (C * (20 : ℝ) ^ B) * (r : ℝ) ^ B := by ring
    _ = taoSection6TailDecayDelta C B (T + (k + 1)) := rfl

end

end Tao

end Erdos1135Predecessor
