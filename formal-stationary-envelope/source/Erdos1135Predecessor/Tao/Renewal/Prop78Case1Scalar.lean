/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.Geom
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators Topology

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoSection7Geom4ExpMoment (t : ℝ) : ℝ :=
  ∑' r : ℕ+,
    (geom4PNat r).toReal * Real.exp (t * (r : ℕ))

theorem taoSection7Geom4ExpMoment_eq
    {t : ℝ} (ht : 3 * Real.exp t < 4) :
    taoSection7Geom4ExpMoment t =
      Real.exp t / (4 - 3 * Real.exp t) := by
  have hratio0 : 0 ≤ (3 / 4 : ℝ) * Real.exp t := by positivity
  have hratio1 : (3 / 4 : ℝ) * Real.exp t < 1 := by nlinarith
  unfold taoSection7Geom4ExpMoment
  calc
    (∑' r : ℕ+,
      (geom4PNat r).toReal * Real.exp (t * (r : ℕ))) =
        ∑' n : ℕ,
          (geom4PNat (Equiv.pnatEquivNat.symm n)).toReal *
            Real.exp (t * ((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ)) := by
          exact (Equiv.pnatEquivNat.symm.tsum_eq _).symm
    _ = ∑' n : ℕ,
        (Real.exp t / 4) * (((3 / 4 : ℝ) * Real.exp t) ^ n) := by
          apply tsum_congr
          intro n
          rw [Equiv.pnatEquivNat_symm_apply]
          have hmass :
              (geom4PNat n.succPNat).toReal =
                (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n := by
            simpa using geom4PNat_apply_nat_succ_toReal n
          have hcoe : ((n.succPNat : ℕ+) : ℕ) = n + 1 := by rfl
          rw [hmass, hcoe]
          rw [show t * (n + 1 : ℕ) = t + (n : ℝ) * t by
                push_cast
                ring,
            Real.exp_add, Real.exp_nat_mul]
          ring
    _ = (Real.exp t / 4) *
        ∑' n : ℕ, (((3 / 4 : ℝ) * Real.exp t) ^ n) := by
          rw [tsum_mul_left]
    _ = (Real.exp t / 4) *
        (1 - (3 / 4 : ℝ) * Real.exp t)⁻¹ := by
          rw [tsum_geometric_of_lt_one hratio0 hratio1]
    _ = Real.exp t / (4 - 3 * Real.exp t) := by
          have hden : 4 - 3 * Real.exp t ≠ 0 := by nlinarith
          field_simp

theorem summable_geom4PNat_mul_exp
    {t : ℝ} (ht : 3 * Real.exp t < 4) :
    Summable fun r : ℕ+ =>
      (geom4PNat r).toReal * Real.exp (t * (r : ℕ)) := by
  have hratio0 : 0 ≤ (3 / 4 : ℝ) * Real.exp t := by positivity
  have hratio1 : (3 / 4 : ℝ) * Real.exp t < 1 := by nlinarith
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  have hs : Summable fun n : ℕ =>
      (Real.exp t / 4) * (((3 / 4 : ℝ) * Real.exp t) ^ n) :=
    (summable_geometric_of_norm_lt_one
      (show ‖(3 / 4 : ℝ) * Real.exp t‖ < 1 by
        rw [Real.norm_of_nonneg hratio0]
        exact hratio1)).mul_left _
  apply hs.congr
  intro n
  rw [Function.comp_apply, Equiv.pnatEquivNat_symm_apply]
  have hmass :
      (geom4PNat n.succPNat).toReal =
        (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ n := by
    simpa using geom4PNat_apply_nat_succ_toReal n
  have hcoe : ((n.succPNat : ℕ+) : ℕ) = n + 1 := by rfl
  rw [hmass, hcoe]
  rw [show t * (n + 1 : ℕ) = t + (n : ℝ) * t by
        push_cast
        ring,
    Real.exp_add, Real.exp_nat_mul]
  ring

noncomputable def taoSection7Case1Tau (delta : ℝ) : ℝ :=
  Real.log (4 / (3 + Real.exp (-delta)))

theorem taoSection7Case1Tau_exp {delta : ℝ} (_hdelta : 0 < delta) :
    Real.exp (taoSection7Case1Tau delta) =
      4 / (3 + Real.exp (-delta)) := by
  unfold taoSection7Case1Tau
  apply Real.exp_log
  positivity

theorem taoSection7Case1Tau_mgf_admissible
    {delta : ℝ} (hdelta : 0 < delta) :
    3 * Real.exp (taoSection7Case1Tau delta) < 4 := by
  rw [taoSection7Case1Tau_exp hdelta]
  have hden : 0 < 3 + Real.exp (-delta) := by positivity
  calc
    3 * (4 / (3 + Real.exp (-delta))) =
        12 / (3 + Real.exp (-delta)) := by ring
    _ < 4 := (div_lt_iff₀ hden).2 (by
      nlinarith [Real.exp_pos (-delta)])

theorem taoSection7Geom4ExpMoment_tau
    {delta : ℝ} (hdelta : 0 < delta) :
    taoSection7Geom4ExpMoment (taoSection7Case1Tau delta) =
      Real.exp delta := by
  have htau := taoSection7Case1Tau_exp hdelta
  have hmgf := taoSection7Case1Tau_mgf_admissible hdelta
  rw [taoSection7Geom4ExpMoment_eq hmgf, htau]
  rw [Real.exp_neg]
  have he : Real.exp delta ≠ 0 := ne_of_gt (Real.exp_pos delta)
  field_simp
  ring

noncomputable def taoSection7Case1InvPow (A m : ℕ) (r : ℕ+) : ℝ :=
  (((max (m - (r : ℕ)) 1 : ℕ) : ℝ)⁻¹) ^ A

noncomputable def taoSection7Case1Rate (A m : ℕ) : ℝ :=
  4 * (A : ℝ) * (1 + Real.log (m : ℝ)) / (m : ℝ)

private theorem one_sub_inv_le_exp_two_mul
    {x : ℝ} (hx : 0 ≤ x) (hxhalf : 2 * x ≤ 1) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hden : 0 < 1 - x := by linarith
  calc
    (1 - x)⁻¹ ≤ 1 + 2 * x := (inv_le_iff_one_le_mul₀ hden).2 (by
      nlinarith [mul_nonneg hx (by linarith : 0 ≤ 1 - 2 * x)])
    _ = 2 * x + 1 := by ring
    _ ≤ Real.exp (2 * x) := Real.add_one_le_exp (2 * x)

theorem taoSection7Case1InvPow_le_expEnvelope
    (A m : ℕ) (r : ℕ+) (hm : 2 ≤ m) :
    taoSection7Case1InvPow A m r ≤
      ((m : ℝ)⁻¹ ^ A) *
        Real.exp (taoSection7Case1Rate A m * (r : ℕ)) := by
  have hm0 : 0 < (m : ℝ) := by positivity
  have hm1 : 1 ≤ (m : ℝ) := by
    exact_mod_cast (show 1 ≤ m by omega)
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  by_cases hsmall : 2 * (r : ℕ) ≤ m
  · have hrm : (r : ℕ) < m := by omega
    have hsub : 1 ≤ m - (r : ℕ) := by omega
    have hx0 : 0 ≤ (r : ℝ) / (m : ℝ) := by positivity
    have hxhalf : 2 * ((r : ℝ) / (m : ℝ)) ≤ 1 := by
      rw [show 2 * ((r : ℝ) / (m : ℝ)) =
        (2 * (r : ℝ)) / (m : ℝ) by ring]
      rw [div_le_one hm0]
      exact_mod_cast hsmall
    have hratio :
        (((m - (r : ℕ) : ℕ) : ℝ)⁻¹) ≤
          (m : ℝ)⁻¹ * Real.exp (2 * ((r : ℝ) / (m : ℝ))) := by
      rw [Nat.cast_sub hrm.le]
      have hfactor :
          ((m : ℝ) - (r : ℝ))⁻¹ =
            (m : ℝ)⁻¹ * (1 - (r : ℝ) / (m : ℝ))⁻¹ := by
        field_simp
      rw [hfactor]
      gcongr
      exact one_sub_inv_le_exp_two_mul hx0 hxhalf
    unfold taoSection7Case1InvPow
    rw [max_eq_left hsub]
    calc
      (((m - (r : ℕ) : ℕ) : ℝ)⁻¹) ^ A ≤
          ((m : ℝ)⁻¹ *
            Real.exp (2 * ((r : ℝ) / (m : ℝ)))) ^ A :=
        pow_le_pow_left₀ (by positivity) hratio A
      _ = ((m : ℝ)⁻¹ ^ A) *
          Real.exp ((2 * (A : ℝ) / (m : ℝ)) * (r : ℝ)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
      _ ≤ ((m : ℝ)⁻¹ ^ A) *
          Real.exp (taoSection7Case1Rate A m * (r : ℕ)) := by
        gcongr
        unfold taoSection7Case1Rate
        have hA : 0 ≤ (A : ℝ) := by positivity
        rw [div_le_div_iff_of_pos_right hm0]
        nlinarith [mul_nonneg hA hlog0]
  · have hlarge : m < 2 * (r : ℕ) := by omega
    have hfactor : 1 ≤ 4 * (r : ℝ) / (m : ℝ) := by
      rw [le_div_iff₀ hm0]
      norm_num
      exact_mod_cast (show m ≤ 4 * (r : ℕ) by omega)
    have hexponent :
        (A : ℝ) * Real.log (m : ℝ) ≤
          taoSection7Case1Rate A m * (r : ℕ) := by
      calc
        (A : ℝ) * Real.log (m : ℝ) =
            ((A : ℝ) * Real.log (m : ℝ)) * 1 := by ring
        _ ≤ ((A : ℝ) * Real.log (m : ℝ)) *
            (4 * (r : ℝ) / (m : ℝ)) := by gcongr
        _ ≤ ((A : ℝ) * (1 + Real.log (m : ℝ))) *
            (4 * (r : ℝ) / (m : ℝ)) := by
          gcongr
          linarith
        _ = taoSection7Case1Rate A m * (r : ℕ) := by
          unfold taoSection7Case1Rate
          ring
    have hinvpow : taoSection7Case1InvPow A m r ≤ 1 := by
      unfold taoSection7Case1InvPow
      apply (pow_le_one₀ (by positivity) ?_)
      exact inv_le_one_of_one_le₀ (by
        exact_mod_cast (le_max_right (m - (r : ℕ)) 1))
    calc
      taoSection7Case1InvPow A m r ≤ 1 := hinvpow
      _ = ((m : ℝ)⁻¹ ^ A) *
          Real.exp ((A : ℝ) * Real.log (m : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hm0, ← mul_pow]
        field_simp
        simp
      _ ≤ ((m : ℝ)⁻¹ ^ A) *
          Real.exp (taoSection7Case1Rate A m * (r : ℕ)) := by
        gcongr

noncomputable def taoSection7Case1InvPowMoment (A m : ℕ) : ℝ :=
  ∑' r : ℕ+, (geom4PNat r).toReal * taoSection7Case1InvPow A m r

theorem taoSection7Case1InvPowMoment_le_of_rate
    (A m : ℕ) {delta : ℝ} (hm : 2 ≤ m) (hdelta : 0 < delta)
    (hrate : taoSection7Case1Rate A m ≤ taoSection7Case1Tau delta) :
    taoSection7Case1InvPowMoment A m ≤
      ((m : ℝ)⁻¹ ^ A) * Real.exp delta := by
  let c : ℝ := (m : ℝ)⁻¹ ^ A
  let tau : ℝ := taoSection7Case1Tau delta
  have hsExp : Summable fun r : ℕ+ =>
      (geom4PNat r).toReal * Real.exp (tau * (r : ℕ)) := by
    apply summable_geom4PNat_mul_exp
    exact taoSection7Case1Tau_mgf_admissible hdelta
  have hpoint : ∀ r : ℕ+,
      (geom4PNat r).toReal * taoSection7Case1InvPow A m r ≤
        (geom4PNat r).toReal * (c * Real.exp (tau * (r : ℕ))) := by
    intro r
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc
      taoSection7Case1InvPow A m r ≤
          c * Real.exp (taoSection7Case1Rate A m * (r : ℕ)) := by
        exact taoSection7Case1InvPow_le_expEnvelope A m r hm
      _ ≤ c * Real.exp (tau * (r : ℕ)) := by
        gcongr
  have hsUpper : Summable fun r : ℕ+ =>
      (geom4PNat r).toReal * (c * Real.exp (tau * (r : ℕ))) := by
    exact (hsExp.mul_left c).congr (fun r => by ring)
  have hsLower : Summable fun r : ℕ+ =>
      (geom4PNat r).toReal * taoSection7Case1InvPow A m r :=
    Summable.of_nonneg_of_le (fun r => by
      apply mul_nonneg ENNReal.toReal_nonneg
      unfold taoSection7Case1InvPow
      positivity) hpoint hsUpper
  unfold taoSection7Case1InvPowMoment
  calc
    (∑' r : ℕ+, (geom4PNat r).toReal * taoSection7Case1InvPow A m r) ≤
        ∑' r : ℕ+,
          (geom4PNat r).toReal * (c * Real.exp (tau * (r : ℕ))) :=
      hsLower.tsum_le_tsum hpoint hsUpper
    _ = c * taoSection7Geom4ExpMoment tau := by
      unfold taoSection7Geom4ExpMoment
      rw [← tsum_mul_left]
      apply tsum_congr
      intro r
      ring
    _ = ((m : ℝ)⁻¹ ^ A) * Real.exp delta := by
      dsimp [c, tau]
      rw [taoSection7Geom4ExpMoment_tau hdelta]

theorem taoSection7Case1Geom4Contraction_half_of_rate
    (A m : ℕ) {epsilon : ℝ} (hm : 2 ≤ m) (hepsilon : 0 < epsilon)
    (hrate : taoSection7Case1Rate A m ≤
      taoSection7Case1Tau (epsilon ^ 3 / 2)) :
    Real.exp (-(epsilon ^ 3)) * taoSection7Case1InvPowMoment A m ≤
      Real.exp (-(epsilon ^ 3 / 2)) * ((m : ℝ)⁻¹ ^ A) := by
  have hdelta : 0 < epsilon ^ 3 / 2 := by positivity
  have hmom := taoSection7Case1InvPowMoment_le_of_rate
    A m hm hdelta hrate
  calc
    Real.exp (-(epsilon ^ 3)) * taoSection7Case1InvPowMoment A m ≤
        Real.exp (-(epsilon ^ 3)) *
          (((m : ℝ)⁻¹ ^ A) * Real.exp (epsilon ^ 3 / 2)) := by
      gcongr
    _ = ((m : ℝ)⁻¹ ^ A) *
        (Real.exp (-(epsilon ^ 3)) * Real.exp (epsilon ^ 3 / 2)) := by ring
    _ = ((m : ℝ)⁻¹ ^ A) *
        Real.exp (-(epsilon ^ 3) + epsilon ^ 3 / 2) := by
      rw [Real.exp_add]
    _ = Real.exp (-(epsilon ^ 3 / 2)) * ((m : ℝ)⁻¹ ^ A) := by
      rw [show -(epsilon ^ 3) + epsilon ^ 3 / 2 =
        -(epsilon ^ 3 / 2) by ring]
      ring

end Tao

end Erdos1135Predecessor
