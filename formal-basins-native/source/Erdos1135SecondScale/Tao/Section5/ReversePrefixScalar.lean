/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

/-
Modified 2026-09-28 for the independent alpha = 2001/2000 replay of
Mazur's Proposition 1.11 formalization, pinned at ca3dd0d63920.
The changes are documented in alpha-2001-2000.patch and the replay report.
Original copyright and license notices are retained; see LICENSE and NOTICE.
-/

import Erdos1135SecondScale.Tao.Section5.ReversePrefix
import Erdos1135SecondScale.Tao.Section5.DescentScale

/-!
# Section 5 Reverse-Prefix Scalar Budget

This leaf proves the branch-free eventual scalar inequality consumed by the
reverse strict-prefix argument. The proof keeps the floor loss sign-safe and
uses only the canonical `m0`, `n0`, and logarithmic slack scales.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped Topology

noncomputable section

private theorem one_fourth_le_log_four_thirds_scalar :
    (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
  norm_num at h ⊢
  exact h

private theorem log_two_pos_scalar :
    0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

private theorem log_two_lt_one_scalar :
    Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  exact h

/-- Any fixed sublinear power of `log B` is eventually bounded by a supplied
positive multiple of `log B`. -/
private theorem eventually_log_rpow_le_mul_log
    {p c : ℝ} (hp : 0 < 1 - p) (hc : 0 < c) :
    ∀ᶠ B : ℕ in atTop,
      Real.rpow (Real.log B) p ≤ c * Real.log B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (-(1 - p)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hp).comp hlog
  filter_upwards
    [hratio.eventually_le_const hc,
      hlog.eventually_gt_atTop (0 : ℝ)] with B hratioB hlogB
  have hlogNonneg : 0 ≤ Real.log B := hlogB.le
  calc
    Real.rpow (Real.log B) p =
        Real.rpow (Real.log B) (-(1 - p) + 1) := by
      congr 1
      ring
    _ =
        Real.rpow (Real.log B) (-(1 - p)) *
          Real.rpow (Real.log B) (1 : ℝ) :=
      Real.rpow_add hlogB (-(1 - p)) (1 : ℝ)
    _ = Real.rpow (Real.log B) (-(1 - p)) * Real.log B := by
      congr 1
      exact Real.rpow_one (Real.log B)
    _ ≤ c * Real.log B :=
      mul_le_mul_of_nonneg_right hratioB hlogNonneg

private theorem eventually_taoSection5ReversePrefixExponentMargin :
    ∀ᶠ B : ℕ in atTop,
      taoSection5CanonicalLostSlack B +
          2 * Real.log 2 * taoSection5TypicalSlack B + Real.log 2 <
        (taoSection5M0 B : ℝ) * Real.log (4 / 3 : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [hlog.eventually_ge_atTop (8000000 : ℝ),
      eventually_log_rpow_le_mul_log
        (p := (3 / 5 : ℝ)) (c := (1 / 16000000 : ℝ)) (by norm_num) (by norm_num),
      eventually_log_rpow_le_mul_log
        (p := (7 / 10 : ℝ)) (c := (1 / 8000000 : ℝ)) (by norm_num) (by norm_num)]
      with B hlogLarge htypical hlost
  have hlogPos : 0 < Real.log B := by nlinarith
  have hm0Floor :
      Real.log B / 200000 - 1 < (taoSection5M0 B : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.log B / 200000)
    rw [← taoSection5M0_eq_floor_log B] at h
    nlinarith
  have hm0Lower :
      Real.log B / 400000 ≤ (taoSection5M0 B : ℝ) := by
    nlinarith
  have hm0LogLower :
      Real.log B / 1600000 ≤
        (taoSection5M0 B : ℝ) * Real.log (4 / 3 : ℝ) := by
    calc
      Real.log B / 1600000 =
          (Real.log B / 400000) * (1 / 4 : ℝ) := by ring
      _ ≤ (taoSection5M0 B : ℝ) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hm0Lower (by norm_num)
      _ ≤ (taoSection5M0 B : ℝ) * Real.log (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left one_fourth_le_log_four_thirds_scalar
          (Nat.cast_nonneg _)
  have htypicalNonneg : 0 ≤ taoSection5TypicalSlack B := by
    exact Real.rpow_nonneg hlogPos.le _
  have hlogTypical :
      Real.log 2 * taoSection5TypicalSlack B ≤
        taoSection5TypicalSlack B := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right log_two_lt_one_scalar.le htypicalNonneg
  have htypicalBudget :
      2 * Real.log 2 * taoSection5TypicalSlack B ≤
        Real.log B / 8000000 := by
    have htypical' :
        taoSection5TypicalSlack B ≤ Real.log B / 16000000 := by
      change Real.rpow (Real.log B) (3 / 5 : ℝ) ≤ Real.log B / 16000000
      convert htypical using 1 <;> ring
    nlinarith
  have hlostBudget :
      taoSection5CanonicalLostSlack B ≤ Real.log B / 8000000 := by
    change Real.rpow (Real.log B) (7 / 10 : ℝ) ≤ Real.log B / 8000000
    convert hlost using 1 <;> ring
  have hlogTwoBudget : Real.log 2 ≤ Real.log B / 8000000 := by
    nlinarith [log_two_lt_one_scalar]
  have htotal :
      taoSection5CanonicalLostSlack B +
          2 * Real.log 2 * taoSection5TypicalSlack B + Real.log 2 <
        Real.log B / 1600000 := by
    nlinarith
  exact htotal.trans_le hm0LogLower

private theorem taoSection5ReversePrefixScalarBudget_of
    {B : ℕ} (facts : TaoSection5DescentScaleFacts B)
    (hmargin :
      taoSection5CanonicalLostSlack B +
          2 * Real.log 2 * taoSection5TypicalSlack B + Real.log 2 <
        (taoSection5M0 B : ℝ) * Real.log (4 / 3 : ℝ)) :
    taoSection5ReversePrefixScalarBudget B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast facts.one_le_B
  have hmainExponent :
      Real.log 2 + 2 * Real.log 2 * taoSection5TypicalSlack B <
        -taoSection5CanonicalLostSlack B +
          (taoSection5M0 B : ℝ) * Real.log (4 / 3 : ℝ) := by
    linarith
  have hfactor :
      2 * Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) <
        Real.exp (-taoSection5CanonicalLostSlack B) *
          (4 / 3 : ℝ) ^ taoSection5M0 B := by
    calc
      2 * Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) =
          Real.exp (Real.log 2) *
            Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp
          (Real.log 2 + 2 * Real.log 2 * taoSection5TypicalSlack B) := by
        rw [Real.exp_add]
      _ < Real.exp
          (-taoSection5CanonicalLostSlack B +
            (taoSection5M0 B : ℝ) * Real.log (4 / 3 : ℝ)) :=
        Real.exp_lt_exp.mpr hmainExponent
      _ = Real.exp (-taoSection5CanonicalLostSlack B) *
          Real.exp ((taoSection5M0 B : ℝ) * Real.log (4 / 3 : ℝ)) := by
        rw [Real.exp_add]
      _ = Real.exp (-taoSection5CanonicalLostSlack B) *
          (4 / 3 : ℝ) ^ taoSection5M0 B := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
  have hfactorB :
      2 * Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) <
        (Real.exp (-taoSection5CanonicalLostSlack B) *
          (4 / 3 : ℝ) ^ taoSection5M0 B) * (B : ℝ) :=
    mul_lt_mul_of_pos_right hfactor hBpos
  have hoffsetB : (3 : ℝ) ^ taoSection5N0 B ≤ (B : ℝ) := by
    calc
      (3 : ℝ) ^ taoSection5N0 B ≤ (B : ℝ) ^ (1 / 5 : ℝ) :=
        facts.offset
      _ ≤ (B : ℝ) ^ (99 / 100 : ℝ) +
          (B : ℝ) ^ (1 / 5 : ℝ) :=
        le_add_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg B) _)
      _ ≤ (B : ℝ) := facts.absorption
  have hexpOne :
      1 ≤ Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) := by
    apply Real.one_le_exp
    have hslack : 0 ≤ taoSection5TypicalSlack B := by
      exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast facts.one_le_B)) _
    positivity
  have hB_le_main :
      (B : ℝ) ≤
        Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hexpOne (Nat.cast_nonneg B)
  unfold taoSection5ReversePrefixScalarBudget
  rw [taoSection5CanonicalLostLower, taoSection5CanonicalLostScale]
  calc
    Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) +
        (3 : ℝ) ^ taoSection5N0 B ≤
      Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) +
        (B : ℝ) := add_le_add_right hoffsetB _
    _ ≤ Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) +
        Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) :=
      add_le_add_right hB_le_main _
    _ = 2 * Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) := by
      ring
    _ < Real.exp (-taoSection5CanonicalLostSlack B) *
        ((4 / 3 : ℝ) ^ taoSection5M0 B * (B : ℝ)) := by
      simpa only [mul_assoc] using hfactorB

/-- The canonical reverse-prefix scalar budget holds for all sufficiently
large thresholds. -/
theorem eventually_taoSection5ReversePrefixScalarBudget :
    ∀ᶠ B : ℕ in atTop, taoSection5ReversePrefixScalarBudget B := by
  filter_upwards
    [eventually_taoSection5DescentScaleFacts,
      eventually_taoSection5ReversePrefixExponentMargin]
      with B facts hmargin
  exact taoSection5ReversePrefixScalarBudget_of facts hmargin

end

end Tao
end Erdos1135SecondScale
