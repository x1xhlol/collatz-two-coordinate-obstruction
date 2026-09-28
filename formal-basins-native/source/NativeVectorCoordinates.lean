import BanachPassageTransport
import NativeLogWindowCoordinates
import OddVectorWindows

open Filter
open scoped Topology BigOperators

namespace CollatzCanonical.LabelLaw
open Erdos1135 CollatzCanonical.NativeTao CollatzCanonical.DirichletAbelian
open CollatzCanonical.BanachWindow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem native_closed_vector_expectation (F : ℕ → V) {s t : ℝ} (hs : 0 ≤ s)
    (hmass : 0 < Tao.logFinsetMass (Tao.oddLogWindow ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊)) :
    pmfMeanV (Tao.oddLogWindowPMF ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊ hmass)
      (fun q => F q.1) = closedOddVectorExpectation F s t := by
  classical
  unfold pmfMeanV finiteMeanV
  simp_rw [closed_probability_eq_native hs hmass]
  have he (q : {n : ℕ // n ∈ closedOddWindowValues s t}) :
      closedOddWindowProbability s t q • F q.1 =
        (closedOddWindowMass s t)⁻¹ • ((1 / (q.1 : ℝ)) • F q.1) := by
    unfold closedOddWindowProbability
    rw [smul_smul]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.smul_sum]
  unfold closedOddVectorExpectation closedOddVectorNumerator
  congr 1
  exact Finset.sum_coe_sort _ (fun q : ℕ => (1 / (q : ℝ)) • F q)

theorem native_vector_expectation_congr (F : ℕ → V) {lo hi lo' hi' : ℕ}
    (hl : lo = lo') (hu : hi = hi')
    (hmass : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo hi))
    (hmass' : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo' hi')) :
    pmfMeanV (Tao.oddLogWindowPMF lo hi hmass) (fun q => F q.1) =
      pmfMeanV (Tao.oddLogWindowPMF lo' hi' hmass') (fun q => F q.1) := by
  subst lo'; subst hi'; rfl

theorem native_power_window_vector_expectation (F : ℕ → V) {y a : ℝ} (hy : 1 ≤ y)
    (hmass : 0 < Tao.logFinsetMass
      (Tao.oddLogWindow (Tao.taoNyLo y) (Tao.taoNyHi y a))) :
    pmfMeanV (Tao.oddLogWindowPMF (Tao.taoNyLo y) (Tao.taoNyHi y a) hmass)
      (fun q => F q.1) = closedOddVectorExpectation F (Real.log y) (a * Real.log y) := by
  have hy0 : 0 < y := by linarith
  have he : Real.exp (a * Real.log y) = y ^ a := by
    rw [Real.rpow_def_of_pos hy0, mul_comm]
  have hl : ⌈Real.exp (Real.log y)⌉₊ = Tao.taoNyLo y := by rw [Real.exp_log hy0]; rfl
  have hu : ⌊Real.exp (a * Real.log y)⌋₊ = Tao.taoNyHi y a := by rw [he]; rfl
  have hmass' : 0 < Tao.logFinsetMass
      (Tao.oddLogWindow ⌈Real.exp (Real.log y)⌉₊ ⌊Real.exp (a * Real.log y)⌋₊) := by
    simpa only [hl, hu] using hmass
  exact (native_vector_expectation_congr F hl.symm hu.symm hmass hmass').trans
    (native_closed_vector_expectation F (Real.log_nonneg hy) hmass')

theorem native_iterated_power_window_vector_expectation (F : ℕ → V) {x a d : ℝ}
    (hx : 1 ≤ x) (hd : 0 ≤ d)
    (hmass : 0 < Tao.logFinsetMass
      (Tao.oddLogWindow (Tao.taoNyLo (x ^ d)) (Tao.taoNyHi (x ^ d) a))) :
    pmfMeanV (Tao.oddLogWindowPMF (Tao.taoNyLo (x ^ d)) (Tao.taoNyHi (x ^ d) a) hmass)
      (fun q => F q.1) =
      closedOddVectorExpectation F (d * Real.log x) (a * d * Real.log x) := by
  have hy : 1 ≤ x ^ d := Real.one_le_rpow hx hd
  rw [native_power_window_vector_expectation F hy, Real.log_rpow (by linarith : 0 < x)]
  rw [mul_assoc]

theorem closed_vector_rate_of_logscale_rate (F : ℕ → V) {a C c : ℝ}
    (ha : 0 < a)
    (h : ∀ᶠ x : ℝ in atTop,
      ‖closedOddVectorExpectation F (a ^ 2 * Real.log x) (a ^ 3 * Real.log x) -
        closedOddVectorExpectation F (a * Real.log x) (a ^ 2 * Real.log x)‖ ≤
        C * (Real.log x) ^ (-c)) :
    ∀ᶠ t : ℝ in atTop,
      ‖closedOddVectorExpectation F (a * t) (a * (a * t)) -
        closedOddVectorExpectation F t (a * t)‖ ≤ (C * a ^ c) * t ^ (-c) := by
  have hmap : Tendsto (fun t : ℝ => Real.exp (t / a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.atTop_div_const ha tendsto_id)
  filter_upwards [hmap.eventually h, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  simp only [Real.log_exp] at ht
  have he₁ : a * (t / a) = t := by field_simp
  have he₂ : a ^ 2 * (t / a) = a * t := by field_simp
  have he₃ : a ^ 3 * (t / a) = a * (a * t) := by field_simp
  have he : (t / a) ^ (-c) = a ^ c * t ^ (-c) := by
    rw [Real.div_rpow ht0 ha.le, Real.rpow_neg ha.le, div_inv_eq_mul, mul_comm]
  simpa only [he₁, he₂, he₃, he, ← mul_assoc] using ht

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.native_closed_vector_expectation
#print axioms CollatzCanonical.LabelLaw.native_iterated_power_window_vector_expectation
#print axioms CollatzCanonical.LabelLaw.closed_vector_rate_of_logscale_rate
