import Erdos1135.ND.Band.A5ReferenceIntegerRoom
import Erdos1135.ND.Band.A5TerminalAtoms
import Erdos1135.ND.Fourier.FiberEndpointFloor

/-!
# Terminal-cell guards for the common A5 reference schedule

This leaf proves the frozen WC-1 conversion from the original strict terminal
width to the fixed-total M1 window.  It deliberately retains the terminal
membership witness rather than replacing it by the weaker `nu / 8` bound.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Frozen WC-1: a strict A5 terminal total lies in the conditioned-M1 window
with constant `7.71 * C`. -/
theorem ndA5ReferenceM1Window_of_t2_terminal
    {B n L : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (ht2 : NDA5T2ScaleFacts B n C)
    (hnuLarge : 11800 ≤ n - Tao.taoSection5M0 B)
    (hL : L ∈ ndA5TerminalTotals B C n) :
    ndSection7M1Window ((771 / 100 : ℝ) * C)
      (n - Tao.taoSection5M0 B) L := by
  let nu := n - Tao.taoSection5M0 B
  let n0 := Tao.taoSection5N0 B
  have hnuPos : 0 < nu := by
    simpa only [nu] using ht2.nu_pos
  have hnuPosR : (0 : ℝ) < (nu : ℝ) := by
    exact_mod_cast hnuPos
  have hnuOneR : (1 : ℝ) ≤ (nu : ℝ) := by
    exact_mod_cast hnuPos
  have hn0Upper :
      (n0 : ℝ) ≤ (4244 / 100 : ℝ) * (nu : ℝ) := by
    apply (div_le_iff₀ hnuPosR).mp
    simpa only [n0, nu] using ht2.n0_div_nu_upper
  have hn0Lower :
      (1374 / 100 : ℝ) * (nu : ℝ) ≤ (n0 : ℝ) := by
    apply (le_div_iff₀ hnuPosR).mp
    simpa only [n0, nu] using ht2.n0_div_nu_lower
  have hn0Pos : (0 : ℝ) < (n0 : ℝ) := by
    nlinarith
  have hn0One : (1 : ℝ) ≤ (n0 : ℝ) := by
    nlinarith
  have hlogNu0 : 0 ≤ Real.log (nu : ℝ) :=
    Real.log_nonneg hnuOneR
  have hlogN00 : 0 ≤ Real.log (n0 : ℝ) :=
    Real.log_nonneg hn0One
  have hnuLargeR : (11800 : ℝ) ≤ (nu : ℝ) := by
    exact_mod_cast hnuLarge
  have hcoeffPow :
      (4244 / 100 : ℝ) ^ 5 ≤ (nu : ℝ) ^ 2 := by
    calc
      (4244 / 100 : ℝ) ^ 5 ≤ (11800 : ℝ) ^ 2 := by
        norm_num
      _ ≤ (nu : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hnuLargeR 2
  have hlogPow :
      Real.log ((4244 / 100 : ℝ) ^ 5) ≤
        Real.log ((nu : ℝ) ^ 2) :=
    Real.log_le_log (by positivity) hcoeffPow
  rw [Real.log_pow, Real.log_pow] at hlogPow
  norm_num at hlogPow
  have hlogCoeffLe :
      Real.log (4244 / 100 : ℝ) ≤
        (2 / 5 : ℝ) * Real.log (nu : ℝ) := by
    nlinarith
  have hlogN0Upper :
      Real.log (n0 : ℝ) ≤ (7 / 5 : ℝ) * Real.log (nu : ℝ) := by
    calc
      Real.log (n0 : ℝ) ≤
          Real.log ((4244 / 100 : ℝ) * (nu : ℝ)) :=
        Real.log_le_log hn0Pos hn0Upper
      _ = Real.log (4244 / 100 : ℝ) + Real.log (nu : ℝ) := by
        rw [Real.log_mul (by norm_num) hnuPosR.ne']
      _ ≤ (7 / 5 : ℝ) * Real.log (nu : ℝ) := by
        nlinarith
  have hproduct :
      (n0 : ℝ) * Real.log (n0 : ℝ) ≤
        (4244 / 100 : ℝ) * (7 / 5 : ℝ) *
          ((nu : ℝ) * Real.log (nu : ℝ)) := by
    calc
      (n0 : ℝ) * Real.log (n0 : ℝ) ≤
          ((4244 / 100 : ℝ) * (nu : ℝ)) *
            ((7 / 5 : ℝ) * Real.log (nu : ℝ)) :=
        mul_le_mul hn0Upper hlogN0Upper hlogN00
          (mul_nonneg (by norm_num) hnuPosR.le)
      _ = (4244 / 100 : ℝ) * (7 / 5 : ℝ) *
          ((nu : ℝ) * Real.log (nu : ℝ)) := by
        ring
  have hnuLog : 0 ≤ (nu : ℝ) * Real.log (nu : ℝ) :=
    mul_nonneg hnuPosR.le hlogNu0
  have hn0Log : 0 ≤ (n0 : ℝ) * Real.log (n0 : ℝ) :=
    mul_nonneg hn0Pos.le hlogN00
  have hsquare :
      (Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ))) ^ 2 ≤
        ((771 / 100 : ℝ) *
          Real.sqrt ((nu : ℝ) * Real.log (nu : ℝ))) ^ 2 := by
    rw [Real.sq_sqrt hn0Log, mul_pow, Real.sq_sqrt hnuLog]
    calc
      (n0 : ℝ) * Real.log (n0 : ℝ) ≤
          (4244 / 100 : ℝ) * (7 / 5 : ℝ) *
            ((nu : ℝ) * Real.log (nu : ℝ)) := hproduct
      _ ≤ (771 / 100 : ℝ) ^ 2 *
          ((nu : ℝ) * Real.log (nu : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnuLog
  have hsqrt :
      Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)) ≤
        (771 / 100 : ℝ) *
          Real.sqrt ((nu : ℝ) * Real.log (nu : ℝ)) :=
    (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp hsquare
  have hwidth :
      ndA5TubeWidth B C ≤
        ((771 / 100 : ℝ) * C) *
          Real.sqrt ((nu : ℝ) * Real.log (nu : ℝ)) := by
    unfold ndA5TubeWidth
    change C * Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)) ≤ _
    calc
      C * Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)) ≤
          C * ((771 / 100 : ℝ) *
            Real.sqrt ((nu : ℝ) * Real.log (nu : ℝ))) :=
        mul_le_mul_of_nonneg_left hsqrt hC
      _ = ((771 / 100 : ℝ) * C) *
          Real.sqrt ((nu : ℝ) * Real.log (nu : ℝ)) := by
        ring
  unfold ndSection7M1Window
  have hterminal := (mem_ndA5TerminalTotals_iff.mp hL).2.2
  simpa only [nu] using hterminal.le.trans hwidth

end
end ND
end Erdos1135
