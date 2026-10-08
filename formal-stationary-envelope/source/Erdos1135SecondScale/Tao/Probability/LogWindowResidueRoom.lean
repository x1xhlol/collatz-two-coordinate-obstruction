/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.LogWindowMassLower
import Erdos1135SecondScale.Tao.Probability.LogWindowResidue

/-!
# Finite Room for Logarithmic Odd-Residue Laws

This module turns a multiplicative-width odd window and a power-of-two room
bound into the fixed `C0 = 2` residue estimate used by Tao's Section 5.  It
contains no real endpoint schedule and no Proposition 1.9 output packet.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

private theorem two_div_two_pow_eq_two_mul_two_rpow_neg (M : ℕ) :
    (2 : ℝ) / ((2 ^ M : ℕ) : ℝ) =
      2 * ((2 : ℝ) ^ (-(M : ℝ))) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  norm_num [div_eq_mul_inv]

/-- Quadratic modulus room and factor-two window width give the fixed
`C0 = 2` residue estimate at every positive ambient exponent. -/
theorem taoTV_oddLogWindow_sourceResidue_canonical_le_two_rpow_neg
    {lo hi M : ℕ} (hlo : 1 ≤ lo) (hwidth : 2 * lo ≤ hi)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (hM : 1 ≤ M) (hroom : (2 ^ M) ^ 2 ≤ lo) :
    taoTV
        (taoProp19SourceResidueLaw (oddLogWindowOddNatPMF lo hi hmass) M)
        (taoCanonicalUniformOddResiduePMF M) ≤
      2 * ((2 : ℝ) ^ (-(M : ℝ))) := by
  let K := M - 1
  have hKM : K + 1 = M := by
    dsimp [K]
    omega
  have hlohi : lo ≤ hi := by omega
  have hfinite :=
    taoTV_oddLogWindow_sourceResidue_canonical_le hlo hlohi hmass K
  rw [hKM] at hfinite
  have hfinite' :
      taoTV
          (taoProp19SourceResidueLaw (oddLogWindowOddNatPMF lo hi hmass) M)
          (taoCanonicalUniformOddResiduePMF M) ≤
        ((2 ^ (M - 1) : ℕ) : ℝ) /
          ((lo : ℝ) * logFinsetMass (oddLogWindow lo hi)) := by
    simpa [K] using hfinite
  have hmassQuarter := one_fourth_le_logFinsetMass_oddLogWindow hlo hwidth
  let A : ℝ := ((2 ^ (M - 1) : ℕ) : ℝ)
  let Q : ℝ := ((2 ^ M : ℕ) : ℝ)
  let L : ℝ := lo
  let H : ℝ := logFinsetMass (oddLogWindow lo hi)
  have hQpos : 0 < Q := by positivity
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast (show 0 < lo by omega)
  have hHpos : 0 < H := hmass
  have hdenpos : 0 < L * H := mul_pos hLpos hHpos
  have hAeq : A = Q / 2 := by
    have hpow := pow_sub_one_mul (Nat.ne_of_gt hM) 2
    have hpowReal := congrArg (fun n : ℕ => (n : ℝ)) hpow
    dsimp [A, Q]
    norm_num at hpowReal ⊢
    linarith
  have hroomReal : Q ^ 2 ≤ L := by
    dsimp [Q, L]
    exact_mod_cast hroom
  have hLH : Q ^ 2 / 4 ≤ L * H := by
    calc
      Q ^ 2 / 4 ≤ L / 4 := div_le_div_of_nonneg_right hroomReal (by norm_num)
      _ = L * (1 / 4 : ℝ) := by ring
      _ ≤ L * H := mul_le_mul_of_nonneg_left hmassQuarter hLpos.le
  have hscalar : A / (L * H) ≤ 2 / Q := by
    apply (div_le_div_iff₀ hdenpos hQpos).2
    rw [hAeq]
    nlinarith
  calc
    taoTV
        (taoProp19SourceResidueLaw (oddLogWindowOddNatPMF lo hi hmass) M)
        (taoCanonicalUniformOddResiduePMF M) ≤ A / (L * H) := by
          simpa [A, L, H] using hfinite'
    _ ≤ 2 / Q := hscalar
    _ = 2 * ((2 : ℝ) ^ (-(M : ℝ))) := by
      simpa [Q] using two_div_two_pow_eq_two_mul_two_rpow_neg M

end Tao
end Erdos1135SecondScale
