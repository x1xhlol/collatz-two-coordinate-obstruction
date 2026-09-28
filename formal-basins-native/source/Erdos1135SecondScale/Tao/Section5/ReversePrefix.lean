/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.PassScheduleFacts
import Erdos1135SecondScale.Tao.Syracuse.AffineTrajectory

/-!
# Section 5 Reverse Strict-Prefix Pilot

This leaf proves the deterministic reverse-prefix implication under the
branch-free scalar budget that remains to be established. It uses the actual
valuation tuple and shifted iterate, with no source-interior, branch, PMF, or
`EPrime.Nonempty` hypothesis.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The branch-free scalar inequality that will later follow eventually from
the canonical definitions of `m0`, `n0`, and the lost window. -/
def taoSection5ReversePrefixScalarBudget (B : ℕ) : Prop :=
  Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) +
      (3 : ℝ) ^ taoSection5N0 B <
    taoSection5CanonicalLostLower B

/-- Closed full-prefix typicality loses exactly two copies of the deviation
when converted to a tail-weight lower bound. -/
theorem TaoSection5TypicalTuple.tail_weight_lower
    {B r : ℕ} {as : List ℕ+}
    (htyp : taoSection5TypicalTuple B r as)
    {j : ℕ} (hj : j ≤ r) :
    2 * ((r - j : ℕ) : ℝ) - 2 * taoSection5TypicalSlack B ≤
      (taoTupleWeight (as.drop j) : ℝ) := by
  have htakeR : as.take r = as := by
    rw [← htyp.1]
    exact List.take_length
  have htotal := htyp.2 r le_rfl
  rw [htakeR] at htotal
  have hprefix := htyp.2 j hj
  have hsumNat := taoTupleWeight_take_add_drop_trajectory as j
  have hsumReal :
      (taoTupleWeight (as.take j) : ℝ) +
          (taoTupleWeight (as.drop j) : ℝ) =
        (taoTupleWeight as : ℝ) := by
    exact_mod_cast hsumNat
  have hsubCast :
      (((r - j : ℕ) : ℕ) : ℝ) = (r : ℝ) - (j : ℝ) := by
    rw [Nat.cast_sub hj]
  rw [hsubCast]
  have htotalLower := (abs_le.mp htotal).1
  have hprefixUpper := (abs_le.mp hprefix).2
  nlinarith

private theorem three_pow_div_two_pow_le_exp_of_weight_lower
    {q w : ℕ} {h : ℝ}
    (hw : 2 * (q : ℝ) - 2 * h ≤ (w : ℝ)) :
    (3 : ℝ) ^ q / (2 : ℝ) ^ w ≤
      Real.exp (2 * Real.log 2 * h) := by
  have hcoeffPos : 0 < (3 : ℝ) ^ q / (2 : ℝ) ^ w := by positivity
  have hlog3 : Real.log (3 : ℝ) ≤ 2 * Real.log 2 := by
    calc
      Real.log (3 : ℝ) ≤ Real.log (4 : ℝ) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
        norm_num
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3Mul := mul_le_mul_of_nonneg_left hlog3 (Nat.cast_nonneg q)
  have hlogBound :
      (q : ℝ) * Real.log 3 - (w : ℝ) * Real.log 2 ≤
        2 * Real.log 2 * h := by
    nlinarith
  have hlogCoeff :
      Real.log ((3 : ℝ) ^ q / (2 : ℝ) ^ w) =
        (q : ℝ) * Real.log 3 - (w : ℝ) * Real.log 2 := by
    rw [Real.log_div (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num)), Real.log_pow, Real.log_pow]
  calc
    (3 : ℝ) ^ q / (2 : ℝ) ^ w =
        Real.exp (Real.log ((3 : ℝ) ^ q / (2 : ℝ) ^ w)) :=
      (Real.exp_log hcoeffPos).symm
    _ ≤ Real.exp (2 * Real.log 2 * h) := by
      apply Real.exp_le_exp.mpr
      rw [hlogCoeff]
      exact hlogBound

/--
Budgeted reverse implication needed by the corrected step-back event identity.
The upper affine offset bound is essential: offset nonnegativity points in the
wrong direction for this contradiction.
-/
theorem taoSection5_strictPrefix_of_typical_endpoint_lower
    {B N r : ℕ} (hN : Odd N)
    (hr : r ≤ taoSection5N0 B)
    (htyp : taoSection5TypicalTuple B r
      (syracuseValuationPNatList r N hN))
    (hlower :
      taoSection5CanonicalLostLower B ≤ ((syracuse^[r]) N : ℝ))
    (hbudget : taoSection5ReversePrefixScalarBudget B) :
    ∀ j < r, B < (syracuse^[j]) N := by
  intro j hj
  by_contra hnot
  have hjle : j ≤ r := hj.le
  have hstate : (syracuse^[j]) N ≤ B := Nat.le_of_not_gt hnot
  have htailWeight :=
    TaoSection5TypicalTuple.tail_weight_lower htyp hjle
  have hcoefficient :=
    three_pow_div_two_pow_le_exp_of_weight_lower htailWeight
  have henvelope :=
    syracuse_iterate_le_tail_affine_envelope_real hN hjle
  let coefficient : ℝ :=
    (3 : ℝ) ^ (r - j) /
      (2 : ℝ) ^ taoTupleWeight
        ((syracuseValuationPNatList r N hN).drop j)
  have hcoefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hstateReal : ((syracuse^[j]) N : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hstate
  have hreplaceState :
      coefficient * ((syracuse^[j]) N : ℝ) ≤ coefficient * (B : ℝ) :=
    mul_le_mul_of_nonneg_left hstateReal hcoefficientNonneg
  have hreplaceCoefficient :
      coefficient * (B : ℝ) ≤
        Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg B)
    simpa only [coefficient] using hcoefficient
  have hq : r - j ≤ taoSection5N0 B :=
    (Nat.sub_le r j).trans hr
  have hpow : (3 : ℝ) ^ (r - j) ≤ (3 : ℝ) ^ taoSection5N0 B := by
    gcongr
    norm_num
  have hendpointUpper :
      ((syracuse^[r]) N : ℝ) ≤
        Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) +
          (3 : ℝ) ^ taoSection5N0 B := by
    change ((syracuse^[r]) N : ℝ) ≤
      coefficient * ((syracuse^[j]) N : ℝ) + (3 : ℝ) ^ (r - j) at henvelope
    calc
      ((syracuse^[r]) N : ℝ) ≤
          coefficient * ((syracuse^[j]) N : ℝ) + (3 : ℝ) ^ (r - j) :=
        henvelope
      _ ≤ coefficient * (B : ℝ) + (3 : ℝ) ^ (r - j) :=
        add_le_add hreplaceState le_rfl
      _ ≤ Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) +
          (3 : ℝ) ^ taoSection5N0 B :=
        add_le_add hreplaceCoefficient hpow
  exact (not_lt_of_ge hlower)
    (hendpointUpper.trans_lt hbudget)

/-- The zero-length prefix condition is correctly vacuous. -/
example {B N : ℕ} :
    ∀ j < 0, B < (syracuse^[j]) N := by
  intro j hj
  omega

end

end Tao
end Erdos1135SecondScale
