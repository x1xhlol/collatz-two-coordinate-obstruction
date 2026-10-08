/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.ConductorIndex
import Erdos1135Predecessor.Tao.Section6.Corollary63
import Mathlib.Data.Nat.Factorization.Basic

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

def zmodThreePowMultiple (T q : ℕ) (omega : ZMod (3 ^ T)) : Prop :=
  ∃ eta : ZMod (3 ^ T),
    omega = (3 : ZMod (3 ^ T)) ^ q * eta

theorem zmodThreePowMultiple_iff_dvd_val
    {T q : ℕ} (hq : q ≤ T) (omega : ZMod (3 ^ T)) :
    zmodThreePowMultiple T q omega ↔ 3 ^ q ∣ omega.val := by
  constructor
  · rintro ⟨eta, homega⟩
    have hcast :
        (omega.val : ZMod (3 ^ T)) =
          ((3 ^ q * eta.val : ℕ) : ZMod (3 ^ T)) := by
      calc
        (omega.val : ZMod (3 ^ T)) = omega := ZMod.natCast_zmod_val omega
        _ = (3 : ZMod (3 ^ T)) ^ q * eta := homega
        _ = (3 : ZMod (3 ^ T)) ^ q *
            (eta.val : ZMod (3 ^ T)) := by
              rw [ZMod.natCast_zmod_val]
        _ = ((3 ^ q * eta.val : ℕ) : ZMod (3 ^ T)) := by
              simp only [Nat.cast_mul, Nat.cast_pow]
              norm_num
    have hmod : omega.val ≡ 3 ^ q * eta.val [MOD 3 ^ T] :=
      (ZMod.natCast_eq_natCast_iff
        omega.val (3 ^ q * eta.val) (3 ^ T)).mp hcast
    exact (hmod.dvd_iff (Nat.pow_dvd_pow 3 hq)).mpr
      (dvd_mul_right (3 ^ q) eta.val)
  · rintro ⟨eta, heta⟩
    refine ⟨(eta : ZMod (3 ^ T)), ?_⟩
    rw [← ZMod.natCast_zmod_val omega, heta]
    push_cast
    rfl

theorem zmodThreePowMultiple_unit_mul_iff
    {T q : ℕ} (u : (ZMod (3 ^ T))ˣ) (omega : ZMod (3 ^ T)) :
    zmodThreePowMultiple T q ((u : ZMod (3 ^ T)) * omega) ↔
      zmodThreePowMultiple T q omega := by
  constructor
  · rintro ⟨eta, heta⟩
    refine ⟨(u⁻¹ : ZMod (3 ^ T)) * eta, ?_⟩
    calc
      omega = (u⁻¹ : ZMod (3 ^ T)) *
          ((u : ZMod (3 ^ T)) * omega) := by simp
      _ = (u⁻¹ : ZMod (3 ^ T)) *
          ((3 : ZMod (3 ^ T)) ^ q * eta) := by rw [heta]
      _ = (3 : ZMod (3 ^ T)) ^ q *
          ((u⁻¹ : ZMod (3 ^ T)) * eta) := by ring
  · rintro ⟨eta, heta⟩
    refine ⟨(u : ZMod (3 ^ T)) * eta, ?_⟩
    rw [heta]
    ring

theorem taoZModThreeProjection_eq_natCast_val
    {r T : ℕ} (h : r ≤ T) (omega : ZMod (3 ^ T)) :
    taoZModThreeProjection h omega =
      (omega.val : ZMod (3 ^ r)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val omega]
  exact taoZModThreeProjection_natCast h omega.val

theorem zmodThreePowMultiple_projection_iff
    {q r T : ℕ} (hqr : q ≤ r) (hrT : r ≤ T)
    (omega : ZMod (3 ^ T)) :
    zmodThreePowMultiple T q omega ↔
      zmodThreePowMultiple r q (taoZModThreeProjection hrT omega) := by
  rw [zmodThreePowMultiple_iff_dvd_val (hqr.trans hrT)]
  rw [zmodThreePowMultiple_iff_dvd_val hqr]
  have hcast :
      (omega.val : ZMod (3 ^ r)) =
        ((taoZModThreeProjection hrT omega).val : ZMod (3 ^ r)) := by
    rw [← taoZModThreeProjection_eq_natCast_val hrT omega]
    rw [ZMod.natCast_zmod_val]
  have hmod :
      omega.val ≡ (taoZModThreeProjection hrT omega).val [MOD 3 ^ r] :=
    (ZMod.natCast_eq_natCast_iff
      omega.val (taoZModThreeProjection hrT omega).val (3 ^ r)).mp hcast
  exact hmod.dvd_iff (Nat.pow_dvd_pow 3 hqr)

theorem zmodThreePrimitive_natCast_of_not_dvd
    {r eta : ℕ} (hr : 1 ≤ r) (heta : ¬3 ∣ eta) :
    zmodThreePrimitive r (eta : ZMod (3 ^ r)) := by
  intro hmultiple
  rcases hmultiple with ⟨zeta, hzeta⟩
  have hcast :
      (eta : ZMod (3 ^ r)) =
        ((3 * zeta.val : ℕ) : ZMod (3 ^ r)) := by
    calc
      (eta : ZMod (3 ^ r)) = 3 * zeta := hzeta
      _ = 3 * (zeta.val : ZMod (3 ^ r)) := by
            rw [ZMod.natCast_zmod_val]
      _ = ((3 * zeta.val : ℕ) : ZMod (3 ^ r)) := by
            simp only [Nat.cast_mul]
            norm_num
  have hmod : eta ≡ 3 * zeta.val [MOD 3 ^ r] :=
    (ZMod.natCast_eq_natCast_iff eta (3 * zeta.val) (3 ^ r)).mp hcast
  apply heta
  exact (hmod.dvd_iff (by
    refine ⟨3 ^ (r - 1), ?_⟩
    rw [← pow_succ']
    congr
    omega)).mpr (dvd_mul_right 3 zeta.val)

theorem syracPMFPrimitivePolynomialDecayAt.dft_three_pow_mul_natCast_le_of_add_eq
    {A : ℕ} {C : ℝ} (hdecay : syracPMFPrimitivePolynomialDecayAt A C)
    {r j T eta : ℕ} (hadd : r + j = T) (hr : 1 ≤ r)
    (heta : ¬3 ∣ eta) :
    ‖ZMod.dft (pmfComplexMass (syracPMF T))
        ((3 : ZMod (3 ^ T)) ^ j * eta)‖ ≤
      C / (r : ℝ) ^ A := by
  subst T
  apply hdecay.dft_three_pow_mul_le hr
  simpa using zmodThreePrimitive_natCast_of_not_dvd hr heta

theorem exists_three_pow_mul_not_dvd_of_not_pow_multiple
    {T q : ℕ} {omega : ZMod (3 ^ T)}
    (homega : ¬zmodThreePowMultiple T q omega) :
    ∃ j eta : ℕ,
      j < q ∧ ¬3 ∣ eta ∧
        omega = (3 : ZMod (3 ^ T)) ^ j * eta := by
  have homega_ne : omega ≠ 0 := by
    intro hz
    apply homega
    exact ⟨0, by simp [hz]⟩
  have hval_ne : omega.val ≠ 0 :=
    (ZMod.val_ne_zero omega).mpr homega_ne
  obtain ⟨j, eta, heta, hval⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hval_ne 3 (by omega)
  have homega_factor :
      omega = (3 : ZMod (3 ^ T)) ^ j * eta := by
    calc
      omega = (omega.val : ZMod (3 ^ T)) :=
        (ZMod.natCast_zmod_val omega).symm
      _ = ((3 ^ j * eta : ℕ) : ZMod (3 ^ T)) := by rw [hval]
      _ = (3 : ZMod (3 ^ T)) ^ j * eta := by
            simp only [Nat.cast_mul, Nat.cast_pow]
            norm_num
  have hj : j < q := by
    by_contra hj_not
    have hqj : q ≤ j := Nat.le_of_not_gt hj_not
    apply homega
    refine ⟨(3 : ZMod (3 ^ T)) ^ (j - q) * eta, ?_⟩
    calc
      omega = (3 : ZMod (3 ^ T)) ^ j * eta := homega_factor
      _ = ((3 : ZMod (3 ^ T)) ^ q *
          (3 : ZMod (3 ^ T)) ^ (j - q)) * eta := by
            rw [← pow_add, Nat.add_sub_of_le hqj]
      _ = (3 : ZMod (3 ^ T)) ^ q *
          ((3 : ZMod (3 ^ T)) ^ (j - q) * eta) := by ring
  exact ⟨j, eta, hj, heta, homega_factor⟩

noncomputable def taoSection6TailScaledFrequency
    {T n : ℕ} (hTn : T ≤ n) (l : ℕ) (xi : ZMod (3 ^ n)) :
    ZMod (3 ^ T) :=
  ((taoCor63TwoPowUnit T l)⁻¹ : ZMod (3 ^ T)) *
    taoZModThreeProjection hTn xi

theorem taoSection6TailScaledFrequency_not_pow_multiple
    {q T n l : ℕ} (hqT : q ≤ T) (hTn : T ≤ n)
    {xi : ZMod (3 ^ n)} (hxi : ¬zmodThreePowMultiple n q xi) :
    ¬zmodThreePowMultiple T q
      (taoSection6TailScaledFrequency hTn l xi) := by
  intro hscaled
  apply hxi
  apply (zmodThreePowMultiple_projection_iff hqT hTn xi).mpr
  apply
    (zmodThreePowMultiple_unit_mul_iff
      ((taoCor63TwoPowUnit T l)⁻¹) (taoZModThreeProjection hTn xi)).mp
  simpa [taoSection6TailScaledFrequency] using hscaled

theorem syracPMFPrimitivePolynomialDecayAt.tail_scaled_frequency_le
    {A : ℕ} {C : ℝ} (hdecay : syracPMFPrimitivePolynomialDecayAt A C)
    {n m k T l : ℕ}
    (htail : k + 1 + T = n) (hhead : k + 1 ≤ m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n)
    {xi : ZMod (3 ^ n)}
    (hxi : ¬zmodThreePowMultiple n (n - m) xi) :
    ∃ r j : ℕ,
      j < n - m ∧
      r + j = T ∧
      k + j + 1 + r = n ∧
      1 ≤ r ∧
      m - k ≤ r ∧
      n ≤ 20 * r ∧
      ‖ZMod.dft (pmfComplexMass (syracPMF T))
          (taoSection6TailScaledFrequency (by omega : T ≤ n) l xi)‖ ≤
        C / (r : ℝ) ^ A := by
  have hqT : n - m ≤ T := by omega
  have hTn : T ≤ n := by omega
  have hscaled :
      ¬zmodThreePowMultiple T (n - m)
        (taoSection6TailScaledFrequency hTn l xi) :=
    taoSection6TailScaledFrequency_not_pow_multiple hqT hTn hxi
  obtain ⟨j, eta, hj, heta, hfactor⟩ :=
    exists_three_pow_mul_not_dvd_of_not_pow_multiple hscaled
  have hjT : j < T := hj.trans_le hqT
  let r := T - j
  have hjr : j + r = T := by
    dsimp [r]
    omega
  have hbounds := taoSection6_conductor_index_bounds
    htail hjr hhead hj hm hk
  rcases hbounds with ⟨hrj, hr, hmkr, _hnmk, hnr⟩
  have hfull :=
    taoSection6_head_add_frequency_add_conductor_eq htail hjr
  have hdecayTail :
      ‖ZMod.dft (pmfComplexMass (syracPMF T))
          ((3 : ZMod (3 ^ T)) ^ j * eta)‖ ≤
        C / (r : ℝ) ^ A := by
    exact hdecay.dft_three_pow_mul_natCast_le_of_add_eq hrj hr heta
  have htailDecay :
      ‖ZMod.dft (pmfComplexMass (syracPMF T))
          (taoSection6TailScaledFrequency hTn l xi)‖ ≤
        C / (r : ℝ) ^ A := by
    rw [hfactor]
    exact hdecayTail
  exact ⟨r, j, hj, hrj, hfull, hr, hmkr, hnr, htailDecay⟩

end

end Tao

end Erdos1135Predecessor
