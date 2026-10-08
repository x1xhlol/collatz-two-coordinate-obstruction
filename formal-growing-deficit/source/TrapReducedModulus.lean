import Erdos1135.Tao.Fourier.Lemma74PrimitiveStrip

/-!
Exact reduced-modulus numerators for the native Section 7 theta. The common
frequency congruence supplies the input to integer carry extraction; this file
does not impose trap geometry, telescope carries, or prove an asymptotic bound.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem valMinAbs_intCast_mul_factor (r q : ℕ) [NeZero q] [NeZero (r * q)]
    (hr : 0 < r) (b : ℤ) :
    (((r : ℤ) * b : ℤ) : ZMod (r * q)).valMinAbs =
      (r : ℤ) * (b : ZMod q).valMinAbs := by
  apply (ZMod.valMinAbs_spec _ _).mpr
  have hb : b ≡ (b : ZMod q).valMinAbs [ZMOD (q : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp (ZMod.coe_valMinAbs _).symm
  have hscale := hb.mul_left' (c := (r : ℤ))
  have hIoc := ZMod.valMinAbs_mem_Ioc (b : ZMod q)
  have hrInt : (0 : ℤ) < r := by exact_mod_cast hr
  constructor
  · apply (ZMod.intCast_eq_intCast_iff _ _ _).mpr
    simpa only [Nat.cast_mul] using hscale
  · constructor
    · have h := mul_lt_mul_of_pos_left hIoc.1 hrInt
      push_cast
      nlinarith
    · have h := mul_le_mul_of_nonneg_left hIoc.2 hrInt.le
      push_cast
      nlinarith

theorem taoSignedTheta_intCast_mul_factor (r q : ℕ) [NeZero q] [NeZero (r * q)]
    (hr : 0 < r) (b : ℤ) :
    taoSignedTheta (((r : ℤ) * b : ℤ) : ZMod (r * q)) =
      ((b : ZMod q).valMinAbs : ℝ) / (q : ℝ) := by
  rw [taoSignedTheta, valMinAbs_intCast_mul_factor r q hr b]
  push_cast
  have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  field_simp

theorem taoSignedTheta_mul_factor {N r q : ℕ} [NeZero N] [NeZero q]
    (hr : 0 < r) (hN : N = r * q) (z : ZMod N) :
    taoSignedTheta ((r : ZMod N) * z) =
      ((ZMod.castHom (show q ∣ N by rw [hN]; exact dvd_mul_left q r)
        (ZMod q) z).valMinAbs : ℝ) / (q : ℝ) := by
  subst N
  have hz : ((z.valMinAbs : ℤ) : ZMod (r * q)) = z := ZMod.coe_valMinAbs z
  have hcast : (z.valMinAbs : ZMod q) =
      ZMod.castHom (dvd_mul_left q r) (ZMod q) z := by
    simpa only [map_intCast] using
      congrArg (ZMod.castHom (dvd_mul_left q r) (ZMod q)) hz
  rw [← hcast, ← taoSignedTheta_intCast_mul_factor r q hr z.valMinAbs]
  congr 1
  push_cast
  rfl

noncomputable def trapReducedResidue (n : ℕ) (xi : ZMod (3 ^ n))
    (p : TaoSection7Point) : ZMod (3 ^ (n - 2 * ((p.j : ℕ) - 1))) :=
  ZMod.castHom (pow_dvd_pow 3 (Nat.sub_le n _)) _
    (taoSection7TwoZPow n (1 - p.l) * xi)

noncomputable def trapReducedNumerator (n : ℕ) (xi : ZMod (3 ^ n))
    (p : TaoSection7Point) : ℤ :=
  (trapReducedResidue n xi p).valMinAbs

/-- Removing the common power of three preserves the signed real phase. -/
theorem sourceTheta_eq_trapReducedNumerator (n : ℕ) (xi : ZMod (3 ^ n))
    (p : TaoSection7Point) (hp : 2 * ((p.j : ℕ) - 1) ≤ n) :
    taoSection7SourceTheta n xi p =
      (trapReducedNumerator n xi p : ℝ) / (3 : ℝ) ^ (n - 2 * ((p.j : ℕ) - 1)) := by
  have hN : 3 ^ n = 3 ^ (2 * ((p.j : ℕ) - 1)) *
      3 ^ (n - 2 * ((p.j : ℕ) - 1)) := by
    rw [← pow_add, Nat.add_sub_of_le hp]
  have h := taoSignedTheta_mul_factor
    (r := 3 ^ (2 * ((p.j : ℕ) - 1))) (q := 3 ^ (n - 2 * ((p.j : ℕ) - 1)))
    (by positivity) hN (taoSection7TwoZPow n (1 - p.l) * xi)
  simpa [taoSection7SourceTheta, taoSection7ThetaResidue, trapReducedNumerator,
    trapReducedResidue, mul_assoc] using h

theorem trapReducedResidue_isUnit {n : ℕ} {xi : ZMod (3 ^ n)}
    (hxi : zmodThreePrimitive n xi) (p : TaoSection7Point) :
    IsUnit (trapReducedResidue n xi p) := by
  exact (taoSection7TwoZPow_mul_primitive_isUnit hxi p.l).map
    (ZMod.castHom (pow_dvd_pow 3 (Nat.sub_le n _)) _)

/-- The native primitive-frequency predicate gives a numerator prime to three. -/
theorem three_not_dvd_trapReducedNumerator {n : ℕ} {xi : ZMod (3 ^ n)}
    (hxi : zmodThreePrimitive n xi) (p : TaoSection7Point)
    (hp : 2 * ((p.j : ℕ) - 1) < n) :
    ¬ (3 : ℤ) ∣ trapReducedNumerator n xi p := by
  let f := ZMod.castHom
    (dvd_pow_self 3 (show n - 2 * ((p.j : ℕ) - 1) ≠ 0 by omega)) (ZMod 3)
  have hu : IsUnit (f (trapReducedResidue n xi p)) :=
    (trapReducedResidue_isUnit hxi p).map f
  have hcast : (trapReducedNumerator n xi p : ZMod 3) =
      f (trapReducedResidue n xi p) := by
    simpa only [map_intCast, trapReducedNumerator] using
      congrArg f (ZMod.coe_valMinAbs (trapReducedResidue n xi p))
  intro hd
  exact hu.ne_zero (hcast.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd))

theorem trapReducedNumerator_ne_zero {n : ℕ} {xi : ZMod (3 ^ n)}
    (hxi : zmodThreePrimitive n xi) (p : TaoSection7Point)
    (hp : 2 * ((p.j : ℕ) - 1) < n) :
    trapReducedNumerator n xi p ≠ 0 := by
  intro hz
  exact three_not_dvd_trapReducedNumerator hxi p hp (hz ▸ dvd_zero 3)

theorem valMinAbs_castHom_modEq {N q : ℕ} (hq : q ∣ N) (z : ZMod N) :
    (ZMod.castHom hq (ZMod q) z).valMinAbs ≡ z.valMinAbs [ZMOD (q : ℤ)] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  rw [ZMod.coe_valMinAbs]
  have h := congrArg (ZMod.castHom hq (ZMod q)) (ZMod.coe_valMinAbs z)
  simpa only [map_intCast] using h.symm

theorem trapReducedNumerator_modEq (n : ℕ) (xi : ZMod (3 ^ n))
    (p : TaoSection7Point) :
    trapReducedNumerator n xi p ≡
      (taoSection7TwoZPow n (1 - p.l) * xi).valMinAbs
        [ZMOD ((3 ^ (n - 2 * ((p.j : ℕ) - 1)) : ℕ) : ℤ)] := by
  exact valMinAbs_castHom_modEq _ _

theorem two_pow_mul_sourcePhase (n D : ℕ) (p q : ℤ) (hD : p + D = q) :
    (2 : ZMod (3 ^ n)) ^ D * taoSection7TwoZPow n (1 - q) =
      taoSection7TwoZPow n (1 - p) := by
  rw [← taoSection7TwoUnit_coe n]
  unfold taoSection7TwoZPow
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 1
  rw [← zpow_natCast, ← zpow_add]
  congr 1
  omega

theorem trapReducedModulus_dvd (n : ℕ) (p q : TaoSection7Point)
    (hpq : (p.j : ℕ) ≤ q.j) :
    3 ^ (n - 2 * ((q.j : ℕ) - 1)) ∣ 3 ^ (n - 2 * ((p.j : ℕ) - 1)) := by
  apply pow_dvd_pow 3
  omega

/-- Ordered tops have the exact common-frequency congruence needed for a carry. -/
theorem trapReducedNumerator_common_frequency (n : ℕ) (xi : ZMod (3 ^ n))
    (p q : TaoSection7Point) (hpq : (p.j : ℕ) ≤ q.j) (hl : p.l ≤ q.l) :
    trapReducedNumerator n xi p ≡
      (2 : ℤ) ^ (q.l - p.l).toNat * trapReducedNumerator n xi q
        [ZMOD ((3 ^ (n - 2 * ((q.j : ℕ) - 1)) : ℕ) : ℤ)] := by
  have hD : p.l + ((q.l - p.l).toNat : ℤ) = q.l := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hl)]
    omega
  have hphase := two_pow_mul_sourcePhase n (q.l - p.l).toNat p.l q.l hD
  have hfull : (taoSection7TwoZPow n (1 - p.l) * xi).valMinAbs ≡
      (2 : ℤ) ^ (q.l - p.l).toNat *
        (taoSection7TwoZPow n (1 - q.l) * xi).valMinAbs
        [ZMOD ((3 ^ n : ℕ) : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    push_cast
    rw [← mul_assoc, hphase]
  have hd : ((3 ^ (n - 2 * ((q.j : ℕ) - 1)) : ℕ) : ℤ) ∣
      ((3 ^ (n - 2 * ((p.j : ℕ) - 1)) : ℕ) : ℤ) := by
    exact_mod_cast trapReducedModulus_dvd n p q hpq
  have hN : ((3 ^ (n - 2 * ((q.j : ℕ) - 1)) : ℕ) : ℤ) ∣
      ((3 ^ n : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow 3 (Nat.sub_le n (2 * ((q.j : ℕ) - 1)))
  exact ((trapReducedNumerator_modEq n xi p).of_dvd hd).trans
    ((hfull.of_dvd hN).trans ((trapReducedNumerator_modEq n xi q).symm.mul_left _))

end Erdos1135.Tao

#print axioms Erdos1135.Tao.sourceTheta_eq_trapReducedNumerator
#print axioms Erdos1135.Tao.three_not_dvd_trapReducedNumerator
#print axioms Erdos1135.Tao.trapReducedNumerator_ne_zero
#print axioms Erdos1135.Tao.trapReducedNumerator_common_frequency
