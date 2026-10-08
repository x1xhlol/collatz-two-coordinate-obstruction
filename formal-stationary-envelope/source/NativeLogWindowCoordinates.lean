import NativeTaoProbabilityBridge

set_option autoImplicit false

namespace CollatzCanonical.NativeTao

open Erdos1135 CollatzCanonical.DirichletAbelian

theorem native_window_expectation_congr (w : ℕ → ℝ) {lo hi lo' hi' : ℕ}
    (hl : lo = lo') (hu : hi = hi')
    (hmass : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo hi))
    (hmass' : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo' hi')) :
    Tao.pmfExpectation (Tao.oddLogWindowPMF lo hi hmass) (fun q => w q.1) =
      Tao.pmfExpectation (Tao.oddLogWindowPMF lo' hi' hmass') (fun q => w q.1) := by
  subst lo'
  subst hi'
  rfl

theorem native_power_window_expectation (w : ℕ → ℝ) {y a : ℝ} (hy : 1 ≤ y)
    (hmass : 0 < Tao.logFinsetMass
      (Tao.oddLogWindow (Tao.taoNyLo y) (Tao.taoNyHi y a))) :
    Tao.pmfExpectation (Tao.oddLogWindowPMF (Tao.taoNyLo y) (Tao.taoNyHi y a) hmass)
      (fun q => w q.1) = closedOddWindowExpectation w (Real.log y) (a * Real.log y) := by
  have hy0 : 0 < y := by linarith
  have he : Real.exp (a * Real.log y) = y ^ a := by
    rw [Real.rpow_def_of_pos hy0, mul_comm]
  have hl : ⌈Real.exp (Real.log y)⌉₊ = Tao.taoNyLo y := by
    rw [Real.exp_log hy0]; rfl
  have hu : ⌊Real.exp (a * Real.log y)⌋₊ = Tao.taoNyHi y a := by rw [he]; rfl
  have hmass' : 0 < Tao.logFinsetMass
      (Tao.oddLogWindow ⌈Real.exp (Real.log y)⌉₊ ⌊Real.exp (a * Real.log y)⌋₊) := by
    simpa only [hl, hu] using hmass
  exact (native_window_expectation_congr w hl.symm hu.symm hmass hmass').trans
    (native_closed_expectation w (Real.log_nonneg hy) hmass')

theorem native_iterated_power_window_expectation (w : ℕ → ℝ) {x a d : ℝ}
    (hx : 1 ≤ x) (hd : 0 ≤ d)
    (hmass : 0 < Tao.logFinsetMass
      (Tao.oddLogWindow (Tao.taoNyLo (x ^ d)) (Tao.taoNyHi (x ^ d) a))) :
    Tao.pmfExpectation
      (Tao.oddLogWindowPMF (Tao.taoNyLo (x ^ d)) (Tao.taoNyHi (x ^ d) a) hmass)
      (fun q => w q.1) =
      closedOddWindowExpectation w (d * Real.log x) (a * d * Real.log x) := by
  have hy : 1 ≤ x ^ d := Real.one_le_rpow hx hd
  rw [native_power_window_expectation w hy, Real.log_rpow (by linarith : 0 < x)]
  rw [mul_assoc]

#print axioms native_iterated_power_window_expectation

end CollatzCanonical.NativeTao
