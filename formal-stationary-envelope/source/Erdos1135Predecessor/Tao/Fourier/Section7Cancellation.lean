/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7Character
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoSignedTheta {N : ℕ} [NeZero N] (z : ZMod N) : ℝ :=
  (z.valMinAbs : ℝ) / (N : ℝ)

theorem taoSignedTheta_intCast_valMinAbs {N : ℕ} [NeZero N] (z : ZMod N) :
    ((z.valMinAbs : ℤ) : ZMod N) = z := by
  exact ZMod.coe_valMinAbs z

def taoSection7Black {N : ℕ} [NeZero N] (epsilon : ℝ) (z : ZMod N) : Prop :=
  |taoSignedTheta z| ≤ epsilon

def taoSection7White {N : ℕ} [NeZero N] (epsilon : ℝ) (z : ZMod N) : Prop :=
  epsilon < |taoSignedTheta z|

theorem taoSection7White_iff_not_black {N : ℕ} [NeZero N]
    (epsilon : ℝ) (z : ZMod N) :
    taoSection7White epsilon z ↔ ¬ taoSection7Black epsilon z := by
  simp [taoSection7White, taoSection7Black, not_le]

theorem abs_taoSignedTheta_le_half {N : ℕ} [NeZero N] (z : ZMod N) :
    |taoSignedTheta z| ≤ 1 / 2 := by
  have hIoc := ZMod.valMinAbs_mem_Ioc z
  have hNpos_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hupper : ((z.valMinAbs : ℝ) * 2) ≤ (N : ℝ) := by
    exact_mod_cast hIoc.2
  have hlower : (-(N : ℝ)) < ((z.valMinAbs : ℝ) * 2) := by
    exact_mod_cast hIoc.1
  rw [taoSignedTheta, abs_div, abs_of_pos hNpos_real]
  rw [div_le_iff₀ hNpos_real]
  rw [abs_le]
  constructor <;> linarith

theorem stdAddChar_neg_intCast_realRatio {N : ℕ} [NeZero N] (m : ℤ) :
    ZMod.stdAddChar (-(m : ZMod N)) =
      Complex.exp (-(2 * Real.pi * ((m : ℝ) / (N : ℝ))) * Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := N) (-m)
  rw [show (-(m : ZMod N)) = ((-m : ℤ) : ZMod N) by norm_num]
  rw [h]
  congr 1
  norm_num
  field_simp [NeZero.ne N]

theorem stdAddChar_neg_residue_eq_exp_taoSignedTheta
    {N : ℕ} [NeZero N] (z : ZMod N) :
    ZMod.stdAddChar (-z) =
      Complex.exp (-(2 * Real.pi * taoSignedTheta z) * Complex.I) := by
  rw [← taoSignedTheta_intCast_valMinAbs z]
  rw [stdAddChar_neg_intCast_realRatio (N := N) z.valMinAbs]
  simp [taoSignedTheta]

theorem tao_cos_pi_le_exp_neg_cube_of_white
    {epsilon theta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hwhite : epsilon ≤ |theta|) (htheta : |theta| ≤ 1) :
    Real.cos (Real.pi * theta) ≤ Real.exp (-(epsilon ^ 3)) := by
  have hpi_nonneg : 0 ≤ Real.pi := Real.pi_pos.le
  have harg : |Real.pi * theta| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg hpi_nonneg]
    exact mul_le_of_le_one_right hpi_nonneg htheta
  have hcos := Real.cos_le_one_sub_mul_cos_sq harg
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hrewrite :
      1 - 2 / Real.pi ^ 2 * (Real.pi * theta) ^ 2 = 1 - 2 * theta ^ 2 := by
    field_simp [hpi_ne]
  have hsq_abs : |theta| ^ 2 = theta ^ 2 := by
    rw [sq_abs]
  have hsq : epsilon ^ 2 ≤ theta ^ 2 := by
    have := pow_le_pow_left₀ hepsilon0 hwhite 2
    rwa [hsq_abs] at this
  have hepsilon_le_two : epsilon ≤ 2 := by linarith
  have hcube_le : epsilon ^ 3 ≤ 2 * epsilon ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hepsilon_le_two (sq_nonneg epsilon)]
  have hpoly : 1 - 2 * theta ^ 2 ≤ 1 - epsilon ^ 3 := by
    nlinarith
  have hexp : 1 - epsilon ^ 3 ≤ Real.exp (-(epsilon ^ 3)) := by
    have := Real.add_one_le_exp (-(epsilon ^ 3))
    linarith
  calc
    Real.cos (Real.pi * theta)
        ≤ 1 - 2 / Real.pi ^ 2 * (Real.pi * theta) ^ 2 := hcos
    _ = 1 - 2 * theta ^ 2 := hrewrite
    _ ≤ 1 - epsilon ^ 3 := hpoly
    _ ≤ Real.exp (-(epsilon ^ 3)) := hexp

theorem norm_half_one_add_exp_neg_two_pi_i
    {theta : ℝ} (htheta : |theta| ≤ 1 / 2) :
    ‖(1 / 2 : ℂ) *
        (1 + Complex.exp (-(2 * Real.pi * theta) * Complex.I))‖ =
      Real.cos (Real.pi * theta) := by
  let x : ℝ := Real.pi * theta
  have hhalf : |x| ≤ Real.pi / 2 := by
    rw [show x = Real.pi * theta by rfl, abs_mul, abs_of_nonneg Real.pi_pos.le]
    nlinarith [mul_le_mul_of_nonneg_left htheta Real.pi_pos.le]
  have hcos_nonneg : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc (abs_le.mp hhalf)
  have hnorm :
      ‖(1 / 2 : ℂ) * (1 + Complex.exp (-(2 * x) * Complex.I))‖ =
        |Real.cos x| := by
    have hsum :
        Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I) =
          2 * (Real.cos x : ℂ) := by
      simpa [Complex.ofReal_cos] using (Complex.two_cos (x : ℂ)).symm
    have hdecomp :
        1 + Complex.exp (-(2 * x) * Complex.I) =
          Complex.exp (-(x : ℂ) * Complex.I) *
            (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I)) := by
      rw [eq_comm]
      calc
        Complex.exp (-(x : ℂ) * Complex.I) *
            (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I))
            =
          Complex.exp (-(x : ℂ) * Complex.I) * Complex.exp ((x : ℂ) * Complex.I) +
            Complex.exp (-(x : ℂ) * Complex.I) * Complex.exp (-(x : ℂ) * Complex.I) := by
              ring
        _ =
          Complex.exp (-(x : ℂ) * Complex.I + (x : ℂ) * Complex.I) +
            Complex.exp (-(x : ℂ) * Complex.I + (-(x : ℂ) * Complex.I)) := by
              rw [Complex.exp_add, Complex.exp_add]
        _ = 1 + Complex.exp (-(2 * x) * Complex.I) := by
              congr 1
              · ring_nf
                simp
              · congr 1
                norm_num
                ring
    calc
      ‖(1 / 2 : ℂ) * (1 + Complex.exp (-(2 * x) * Complex.I))‖
          =
        ‖(1 / 2 : ℂ) *
          (Complex.exp (-(x : ℂ) * Complex.I) *
            (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I)))‖ := by
            rw [hdecomp]
      _ =
        ‖Complex.exp (-(x : ℂ) * Complex.I) *
          ((1 / 2 : ℂ) *
            (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I)))‖ := by
            congr 1
            ring
      _ =
        ‖Complex.exp (-(x : ℂ) * Complex.I) *
          ((1 / 2 : ℂ) * (2 * (Real.cos x : ℂ)))‖ := by
            rw [hsum]
      _ = ‖Complex.exp (-(x : ℂ) * Complex.I) * (Real.cos x : ℂ)‖ := by
            congr 1
            ring
      _ = |Real.cos x| := by
            rw [norm_mul]
            rw [show -(x : ℂ) * Complex.I = ((-x : ℝ) : ℂ) * Complex.I by norm_num]
            rw [Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  simpa [x, abs_of_nonneg hcos_nonneg, mul_assoc] using hnorm

theorem norm_half_one_add_stdAddChar_neg_of_taoSection7White
    {N : ℕ} [NeZero N] (z : ZMod N) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hwhite : taoSection7White epsilon z) :
    ‖(1 / 2 : ℂ) * (1 + ZMod.stdAddChar (-z))‖ ≤
      Real.exp (-(epsilon ^ 3)) := by
  rw [stdAddChar_neg_residue_eq_exp_taoSignedTheta z]
  rw [norm_half_one_add_exp_neg_two_pi_i (abs_taoSignedTheta_le_half z)]
  exact tao_cos_pi_le_exp_neg_cube_of_white hepsilon0 hepsilon1 hwhite.le (by
    nlinarith [abs_taoSignedTheta_le_half z])

theorem norm_half_one_add_taoForwardDFTKernel_of_taoSection7White
    {N : ℕ} [NeZero N] (x xi : ZMod N) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hwhite : taoSection7White epsilon (((2 : ZMod N) * x) * xi)) :
    ‖(1 / 2 : ℂ) *
        (1 + taoForwardDFTKernel ((2 : ZMod N) * x) xi)‖ ≤
      Real.exp (-(epsilon ^ 3)) := by
  simpa [taoForwardDFTKernel] using
    norm_half_one_add_stdAddChar_neg_of_taoSection7White
      (((2 : ZMod N) * x) * xi) hepsilon0 hepsilon1 hwhite

noncomputable def taoSection7TwoUnit (n : ℕ) : (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime 2 (Nat.Coprime.pow_right n (by decide : Nat.Coprime 2 3))

noncomputable def taoSection7TwoZPow (n : ℕ) (e : ℤ) : ZMod (3 ^ n) :=
  ((taoSection7TwoUnit n) ^ e : (ZMod (3 ^ n))ˣ)

theorem taoSection7TwoUnit_coe (n : ℕ) :
    (taoSection7TwoUnit n : ZMod (3 ^ n)) = 2 := by
  simp [taoSection7TwoUnit]

theorem two_mul_taoSection7TwoZPow_neg
    (n : ℕ) (l : ℤ) :
    (2 : ZMod (3 ^ n)) * taoSection7TwoZPow n (-l) =
      taoSection7TwoZPow n (1 - l) := by
  unfold taoSection7TwoZPow
  rw [← taoSection7TwoUnit_coe n]
  rw [← Units.val_mul]
  congr 1
  rw [show (1 - l : ℤ) = 1 + -l by ring]
  rw [zpow_add, zpow_one, zpow_neg]

noncomputable def taoSection7PairX (n : ℕ) (j : ℕ+) (l : ℤ) : ZMod (3 ^ n) :=
  (3 : ZMod (3 ^ n)) ^ (2 * ((j : ℕ) - 1)) * taoSection7TwoZPow n (-l)

noncomputable def taoSection7ThetaResidue
    (n : ℕ) (xi : ZMod (3 ^ n)) (j : ℕ+) (l : ℤ) : ZMod (3 ^ n) :=
  ((3 : ZMod (3 ^ n)) ^ (2 * ((j : ℕ) - 1)) *
      taoSection7TwoZPow n (1 - l)) * xi

theorem taoSection7_pairX_thetaResidue
    (n : ℕ) (xi : ZMod (3 ^ n)) (j : ℕ+) (l : ℤ) :
    ((2 : ZMod (3 ^ n)) * taoSection7PairX n j l) * xi =
      taoSection7ThetaResidue n xi j l := by
  dsimp [taoSection7PairX, taoSection7ThetaResidue]
  calc
    ((2 : ZMod (3 ^ n)) *
          ((3 : ZMod (3 ^ n)) ^ (2 * ((j : ℕ) - 1)) *
            taoSection7TwoZPow n (-l))) * xi =
        (((3 : ZMod (3 ^ n)) ^ (2 * ((j : ℕ) - 1)) *
          ((2 : ZMod (3 ^ n)) * taoSection7TwoZPow n (-l))) * xi) := by
          ring
    _ = ((3 : ZMod (3 ^ n)) ^ (2 * ((j : ℕ) - 1)) *
          taoSection7TwoZPow n (1 - l)) * xi := by
          rw [two_mul_taoSection7TwoZPow_neg]

theorem norm_taoSection7PairAverage_point_le_exp_neg_cube_of_white
    (n : ℕ) (xi : ZMod (3 ^ n)) (j : ℕ+) (l : ℤ) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hwhite : taoSection7White epsilon (taoSection7ThetaResidue n xi j l)) :
    ‖taoSection7PairAverage n xi (taoSection7PairX n j l)‖ ≤
      Real.exp (-(epsilon ^ 3)) := by
  rw [norm_taoSection7PairAverage_eq]
  refine norm_half_one_add_taoForwardDFTKernel_of_taoSection7White
    (N := 3 ^ n) (taoSection7PairX n j l) xi hepsilon0 hepsilon1 ?_
  simpa [taoSection7_pairX_thetaResidue] using hwhite

noncomputable def taoSection7FThree
    (n : ℕ) (xi x : ZMod (3 ^ n)) : ℂ :=
  (((geom2PNatPairMass (1 : ℕ+) (2 : ℕ+) / pascalGeom2PairMass 3 : ℝ) : ℂ) *
      taoForwardDFTKernel ((5 : ZMod (3 ^ n)) * x) xi) +
    (((geom2PNatPairMass (2 : ℕ+) (1 : ℕ+) / pascalGeom2PairMass 3 : ℝ) : ℂ) *
      taoForwardDFTKernel ((7 : ZMod (3 ^ n)) * x) xi)

theorem taoSection7FThree_eq_pairAverage
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    taoSection7FThree n xi x = taoSection7PairAverage n xi x := by
  unfold taoSection7FThree taoSection7PairAverage
  rw [geom2PNatPairMass_one_two_div_pascal_three]
  rw [geom2PNatPairMass_two_one_div_pascal_three]
  norm_num

theorem norm_taoSection7FThree_eq_pairAverage
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    ‖taoSection7FThree n xi x‖ = ‖taoSection7PairAverage n xi x‖ := by
  rw [taoSection7FThree_eq_pairAverage]

theorem norm_taoSection7FThree_point_le_exp_neg_cube_of_white
    (n : ℕ) (xi : ZMod (3 ^ n)) (j : ℕ+) (l : ℤ) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hwhite : taoSection7White epsilon (taoSection7ThetaResidue n xi j l)) :
    ‖taoSection7FThree n xi (taoSection7PairX n j l)‖ ≤
      Real.exp (-(epsilon ^ 3)) := by
  rw [taoSection7FThree_eq_pairAverage]
  exact norm_taoSection7PairAverage_point_le_exp_neg_cube_of_white
    n xi j l hepsilon0 hepsilon1 hwhite

end Tao

end Erdos1135Predecessor
