/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.LogTimeCollatzBridge

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem syracuse_iterate_le_twoPow_mul (n M : ℕ) (hM : Odd M) :
    (Tao.syracuse^[n]) M ≤ 2 ^ n * M := by
  have hstep (x : ℕ) (hx : Odd x) : Tao.syracuse x ≤ 2 * x := by
    have hp : 2 ≤ 2 ^ Tao.syracuseExponent x := by
      simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
        (Tao.syracuseExponent_pos_of_odd hx)
    have hmul := Nat.mul_le_mul_right (Tao.syracuse x) hp
    rw [Tao.two_pow_syracuseExponent_mul_syracuse] at hmul
    have hpos := Odd.pos hx
    omega
  induction n generalizing M with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, pow_succ]
      calc
        _ ≤ 2 ^ n * Tao.syracuse M := ih _ (Tao.syracuse_odd M)
        _ ≤ 2 ^ n * (2 * M) := Nat.mul_le_mul_left _ (hstep M hM)
        _ = _ := by ring

theorem history_floor_of_terminal_bound
    (R n M : ℕ) (hM : Odd M)
    (hterminal : R * 2 ^ n ≤ (Tao.syracuse^[n]) M) :
    ∀ j ≤ n, R ≤ (Tao.syracuse^[j]) M := by
  intro j hj
  have htail := syracuse_iterate_le_twoPow_mul (n - j) ((Tao.syracuse^[j]) M)
    (Tao.syracuse_iterate_odd j M hM)
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hj] at htail
  have hpow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (Nat.sub_le n j)
  have h := hterminal.trans (htail.trans
    (Nat.mul_le_mul_right ((Tao.syracuse^[j]) M) hpow))
  rw [Nat.mul_comm R] at h
  exact Nat.le_of_mul_le_mul_left h (by positivity)

theorem twoPow_valuationWeight_mul_terminal_le_of_history_floor
    (R : ℕ) (hR : 0 < R) (n M : ℕ) (hM : Odd M)
    (hfloor : ∀ j < n, R ≤ (Tao.syracuse^[j]) M) :
    (2 : ℝ) ^ Tao.taoTupleWeight (Tao.syracuseValuationPNatList n M hM) *
        ((Tao.syracuse^[n]) M : ℝ) ≤
      (3 + 1 / (R : ℝ)) ^ n * (M : ℝ) := by
  induction n generalizing M with
  | zero => simp [Tao.syracuseValuationPNatList, Tao.taoTupleWeight]
  | succ n ih =>
      let a := Tao.syracuseExponent M
      let W := Tao.taoTupleWeight
        (Tao.syracuseValuationPNatList n (Tao.syracuse M) (Tao.syracuse_odd M))
      let r : ℝ := 3 + 1 / (R : ℝ)
      have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
      have hr : 0 ≤ r := by dsimp [r]; positivity
      have htail := ih (Tao.syracuse M) (Tao.syracuse_odd M)
        (fun j hj => by
          simpa only [Function.iterate_succ_apply] using hfloor (j + 1) (by omega))
      have hRM : (R : ℝ) ≤ M := by exact_mod_cast hfloor 0 (by omega)
      have hdiv : 1 ≤ (M : ℝ) / R := (le_div_iff₀ hRreal).2 (by simpa using hRM)
      have hstep : 3 * (M : ℝ) + 1 ≤ r * M := by
        dsimp [r]
        rw [div_eq_mul_inv] at hdiv ⊢
        nlinarith only [hdiv]
      have hid : (2 : ℝ) ^ a * (Tao.syracuse M : ℝ) = 3 * (M : ℝ) + 1 := by
        exact_mod_cast Tao.two_pow_syracuseExponent_mul_syracuse M
      simp only [Tao.syracuseValuationPNatList, Tao.taoTupleWeight,
        Function.iterate_succ_apply]
      change (2 : ℝ) ^ (a + W) * ((Tao.syracuse^[n]) (Tao.syracuse M) : ℝ) ≤
        r ^ (n + 1) * M
      calc
        _ = (2 : ℝ) ^ a * ((2 : ℝ) ^ W *
            ((Tao.syracuse^[n]) (Tao.syracuse M) : ℝ)) := by rw [pow_add]; ring
        _ ≤ (2 : ℝ) ^ a * (r ^ n * (Tao.syracuse M : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
        _ = r ^ n * (3 * (M : ℝ) + 1) := by rw [← hid]; ring
        _ ≤ r ^ n * (r * M) := mul_le_mul_of_nonneg_left hstep (pow_nonneg hr n)
        _ = _ := by rw [pow_succ]; ring

theorem rawTime_mul_logTwo_le_of_history_floor
    (R : ℕ) (hR : 0 < R) (n M : ℕ) (hM : Odd M)
    (hfloor : ∀ j < n, R ≤ (Tao.syracuse^[j]) M) :
    ((n + Tao.taoTupleWeight (Tao.syracuseValuationPNatList n M hM) : ℕ) : ℝ) *
        Real.log 2 ≤
      (n : ℝ) * (Real.log 2 + Real.log (3 + 1 / (R : ℝ))) +
        Real.log (M : ℝ) - Real.log ((Tao.syracuse^[n]) M : ℝ) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hr : 0 < (3 + 1 / (R : ℝ)) := by positivity
  have hMreal : (0 : ℝ) < M := by exact_mod_cast Odd.pos hM
  have hend : (0 : ℝ) < (Tao.syracuse^[n]) M := by
    exact_mod_cast Odd.pos (Tao.syracuse_iterate_odd n M hM)
  have hlog := Real.log_le_log (mul_pos (pow_pos (by norm_num) _) hend)
    (twoPow_valuationWeight_mul_terminal_le_of_history_floor R hR n M hM hfloor)
  rw [Real.log_mul (pow_ne_zero _ (by norm_num)) hend.ne',
    Real.log_mul (pow_ne_zero _ hr.ne') hMreal.ne', Real.log_pow, Real.log_pow] at hlog
  push_cast
  nlinarith only [hlog]

end

end Erdos1135Predecessor.ND.PositiveDensity
