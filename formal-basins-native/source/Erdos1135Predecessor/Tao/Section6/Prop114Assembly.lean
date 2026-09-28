/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.DecayStatement
import Erdos1135Predecessor.Tao.Fourier.MixingStatement
import Erdos1135Predecessor.Tao.Section6.Corollary63
import Erdos1135Predecessor.Tao.Section6.GlobalOscillationBound
import Erdos1135Predecessor.Tao.Section6.HighRegimeAllScale

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem syracFineScaleMixingAt_of_large_and_global
    {A M0 : ℕ} {C : ℝ}
    (hlarge : ∀ n m : ℕ, M0 ≤ m → m ≤ n →
      syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A) :
    syracFineScaleMixingAt A
      (max C (2 * (M0 : ℝ) ^ A)) := by
  intro n m hm hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : 0 < (m : ℝ) ^ A := pow_pos hmR A
  by_cases hcut : M0 ≤ m
  · exact (hlarge n m hcut hmn).trans
      (div_le_div_of_nonneg_right
        (le_max_left C (2 * (M0 : ℝ) ^ A)) hden.le)
  · have hmM0 : m ≤ M0 := (Nat.lt_of_not_ge hcut).le
    have hmM0R : (m : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hmM0
    have hpow : (m : ℝ) ^ A ≤ (M0 : ℝ) ^ A :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) hmM0R A
    have hscaled : 2 * (m : ℝ) ^ A ≤ 2 * (M0 : ℝ) ^ A :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    exact (syracFineScaleOscillation_le_two hmn).trans <|
      (le_div_iff₀ hden).2 <|
        hscaled.trans (le_max_right C (2 * (M0 : ℝ) ^ A))

end

end Tao

end Erdos1135Predecessor
