import TrapReducedModulus

/-! Exact changes of conductor and height for the native Section 7 phase. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_twoZPow_add (n : ℕ) (a b : ℤ) :
    taoSection7TwoZPow n (a + b) =
      taoSection7TwoZPow n a * taoSection7TwoZPow n b := by
  unfold taoSection7TwoZPow
  rw [zpow_add, Units.val_mul]

theorem trap_twoZPow_cast (n m : ℕ) (hmn : m ≤ n) (a : ℤ) :
    ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) (taoSection7TwoZPow n a) =
      taoSection7TwoZPow m a := by
  let f := ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m))
  let g := Units.map f.toMonoidHom
  have hg : g (taoSection7TwoUnit n) = taoSection7TwoUnit m := by
    apply Units.ext
    change f (taoSection7TwoUnit n) = (taoSection7TwoUnit m : ZMod (3 ^ m))
    rw [taoSection7TwoUnit_coe, taoSection7TwoUnit_coe]
    exact map_ofNat f 2
  change ((g ((taoSection7TwoUnit n) ^ a) : (ZMod (3 ^ m))ˣ) : ZMod (3 ^ m)) = _
  rw [map_zpow, hg]
  rfl

noncomputable def trapPrefixFrequency (n u : ℕ) (s : ℤ)
    (xi : ZMod (3 ^ n)) : ZMod (3 ^ (n - 2 * u)) :=
  ZMod.castHom (pow_dvd_pow 3 (Nat.sub_le n (2 * u))) _
    (taoSection7TwoZPow n (-s) * xi)

theorem trap_isUnit_primitive {n : ℕ} (hn : 1 ≤ n) {xi : ZMod (3 ^ n)}
    (hxi : IsUnit xi) : zmodThreePrimitive n xi := by
  let f := ZMod.castHom (dvd_pow_self 3 (show n ≠ 0 by omega)) (ZMod 3)
  have hu := hxi.map f
  rintro ⟨eta, heta⟩
  apply hu.ne_zero
  have hf3 : f 3 = (0 : ZMod 3) := by rw [map_ofNat]; decide
  rw [heta, map_mul, hf3, zero_mul]

theorem trapPrefixFrequency_primitive (n u : ℕ) (s : ℤ)
    (xi : ZMod (3 ^ n)) (hxi : zmodThreePrimitive n xi) (hu : 2 * u < n) :
    zmodThreePrimitive (n - 2 * u) (trapPrefixFrequency n u s xi) := by
  apply trap_isUnit_primitive (by omega)
  exact ((Units.isUnit ((taoSection7TwoUnit n) ^ (-s))).mul hxi.isUnit).map
    (ZMod.castHom (pow_dvd_pow 3 (Nat.sub_le n (2 * u))) _)

theorem trap_stdAddChar_mul_factor {N r q : ℕ} [NeZero N] [NeZero q]
    (hr : 0 < r) (hN : N = r * q) (z : ZMod N) :
    ZMod.stdAddChar (-((r : ZMod N) * z)) =
      ZMod.stdAddChar (-(ZMod.castHom
        (show q ∣ N by rw [hN]; exact dvd_mul_left q r) (ZMod q) z)) := by
  rw [stdAddChar_neg_residue_eq_exp_taoSignedTheta,
    stdAddChar_neg_residue_eq_exp_taoSignedTheta, taoSignedTheta_mul_factor hr hN]
  rfl

theorem trap_prefix_residue_cast (n u : ℕ) (s l : ℤ)
    (xi : ZMod (3 ^ n)) (j c : ℕ) :
    ZMod.castHom (pow_dvd_pow 3 (Nat.sub_le n (2 * u))) (ZMod (3 ^ (n - 2 * u)))
      ((c : ZMod (3 ^ n)) * 3 ^ (2 * j) * taoSection7TwoZPow n (-(s + l)) * xi) =
      (c : ZMod (3 ^ (n - 2 * u))) * 3 ^ (2 * j) *
        taoSection7TwoZPow (n - 2 * u) (-l) * trapPrefixFrequency n u s xi := by
  rw [show -(s + l) = -l + -s by ring, trap_twoZPow_add]
  simp only [map_mul, map_pow, map_natCast, map_ofNat,
    trapPrefixFrequency]
  rw [trap_twoZPow_cast n (n - 2 * u) (Nat.sub_le n (2 * u)) (-l)]
  ring

theorem trap_prefix_kernel_transport (n u : ℕ) (hu : 2 * u ≤ n)
    (s l : ℤ) (xi : ZMod (3 ^ n)) (j : ℕ+) (c : ℕ) :
    taoForwardDFTKernel
      ((c : ZMod (3 ^ n)) * taoSection7PairX n
        ⟨u + (j : ℕ), by have := PNat.pos j; omega⟩ (s + l)) xi =
    taoForwardDFTKernel
      ((c : ZMod (3 ^ (n - 2 * u))) * taoSection7PairX (n - 2 * u) j l)
      (trapPrefixFrequency n u s xi) := by
  have hpow : 3 ^ n = 3 ^ (2 * u) * 3 ^ (n - 2 * u) := by
    rw [← pow_add, Nat.add_sub_of_le hu]
  have hindex : 2 * (u + (j : ℕ) - 1) = 2 * u + 2 * ((j : ℕ) - 1) := by
    have := PNat.pos j
    omega
  have hfactor :
      ((c : ZMod (3 ^ n)) * taoSection7PairX n
        ⟨u + (j : ℕ), by have := PNat.pos j; omega⟩ (s + l)) * xi =
      ((3 ^ (2 * u) : ℕ) : ZMod (3 ^ n)) *
        ((c : ZMod (3 ^ n)) * 3 ^ (2 * ((j : ℕ) - 1)) *
          taoSection7TwoZPow n (-(s + l)) * xi) := by
    change ((c : ZMod (3 ^ n)) *
      (3 ^ (2 * (u + (j : ℕ) - 1)) * taoSection7TwoZPow n (-(s + l)))) * xi = _
    rw [hindex, pow_add]
    push_cast
    ring
  rw [taoForwardDFTKernel, hfactor, trap_stdAddChar_mul_factor (by positivity) hpow]
  rw [trap_prefix_residue_cast]
  simp only [taoForwardDFTKernel, taoSection7PairX, mul_assoc]

theorem trap_prefix_FThree_transport (n u : ℕ) (hu : 2 * u ≤ n)
    (s l : ℤ) (xi : ZMod (3 ^ n)) (j : ℕ+) :
    taoSection7FThree n xi
      (taoSection7PairX n ⟨u + (j : ℕ), by have := PNat.pos j; omega⟩ (s + l)) =
    taoSection7FThree (n - 2 * u) (trapPrefixFrequency n u s xi)
      (taoSection7PairX (n - 2 * u) j l) := by
  have h5 := trap_prefix_kernel_transport n u hu s l xi j 5
  have h7 := trap_prefix_kernel_transport n u hu s l xi j 7
  norm_num only [Nat.cast_ofNat] at h5 h7
  simpa only [taoSection7FThree_eq_pairAverage, taoSection7PairAverage] using
    congrArg₂ (fun x y : ℂ => (1 / 2) * x + (1 / 2) * y) h5 h7

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trapPrefixFrequency_primitive
#print axioms Erdos1135.Tao.trap_prefix_kernel_transport
#print axioms Erdos1135.Tao.trap_prefix_FThree_transport
