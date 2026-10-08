/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.ReversePrefixScalar
import Erdos1135SecondScale.Tao.Syracuse.AffineEnvelope
import Erdos1135SecondScale.Tao.Syracuse.AffineOdd
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Section 5 Affine Source Scale

This leaf proves the branch-neutral real bounds that place a scheduled affine
source at the original Section 5 source scale.  It keeps residue compatibility,
probability laws, tuple reversal, and common-normalizer arguments outside the
scalar calculation.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped Topology

noncomputable section

/-- Eventual branch-neutral data for reconstructing scheduled affine sources. -/
structure TaoSection5AffineSourceScaleFacts (B : ℕ) : Prop where
  schedule : TaoSection5PassScheduleFacts B
  reverseBudget : taoSection5ReversePrefixScalarBudget B
  sourceMargin :
    taoSection5CanonicalLostSlack B +
          Real.log 2 * taoSection5TypicalSlack B + Real.log 2 ≤
      Real.log (4 / 3 : ℝ) *
        Real.rpow (Real.log B) (4 / 5 : ℝ)

private theorem one_fourth_le_log_four_thirds_sourceScale :
    (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
  norm_num at h ⊢
  exact h

private theorem log_two_lt_one_sourceScale : Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  exact h

private theorem natCast_log_nonneg_sourceScale (B : ℕ) :
    0 ≤ Real.log (B : ℝ) := by
  by_cases hB : B = 0
  · simp [hB]
  · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hB))

private theorem eventually_log_rpow_le_twelfth_four_fifths
    {p : ℝ} (hp : 0 < 4 / 5 - p) :
    ∀ᶠ B : ℕ in atTop,
      Real.rpow (Real.log B) p ≤
        Real.rpow (Real.log B) (4 / 5 : ℝ) / 12 := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (-(4 / 5 - p)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hp).comp hlog
  filter_upwards
    [hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 12),
      hlog.eventually_gt_atTop (0 : ℝ)] with B hratioB hlogB
  have hlargeNonneg :
      0 ≤ Real.rpow (Real.log B) (4 / 5 : ℝ) :=
    Real.rpow_nonneg hlogB.le _
  calc
    Real.rpow (Real.log B) p =
        Real.rpow (Real.log B) (-(4 / 5 - p) + 4 / 5) := by
      congr 1
      ring
    _ = Real.rpow (Real.log B) (-(4 / 5 - p)) *
          Real.rpow (Real.log B) (4 / 5 : ℝ) :=
      Real.rpow_add hlogB (-(4 / 5 - p)) (4 / 5 : ℝ)
    _ ≤ (1 / 12 : ℝ) * Real.rpow (Real.log B) (4 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hratioB hlargeNonneg
    _ = Real.rpow (Real.log B) (4 / 5 : ℝ) / 12 := by ring

private theorem eventually_taoSection5AffineSourceMargin :
    ∀ᶠ B : ℕ in atTop,
      taoSection5CanonicalLostSlack B +
            Real.log 2 * taoSection5TypicalSlack B + Real.log 2 ≤
        Real.log (4 / 3 : ℝ) *
          Real.rpow (Real.log B) (4 / 5 : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (4 / 5 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp hlog
  filter_upwards
    [eventually_log_rpow_le_twelfth_four_fifths
      (p := (7 / 10 : ℝ)) (by norm_num),
      eventually_log_rpow_le_twelfth_four_fifths
        (p := (3 / 5 : ℝ)) (by norm_num),
      hlarge.eventually_ge_atTop (12 * Real.log 2)]
      with B hlost htypical hconst
  let s := Real.rpow (Real.log B) (4 / 5 : ℝ)
  have hsNonneg : 0 ≤ s := by
    exact Real.rpow_nonneg (natCast_log_nonneg_sourceScale B) _
  have htypicalNonneg : 0 ≤ taoSection5TypicalSlack B := by
    unfold taoSection5TypicalSlack
    exact Real.rpow_nonneg (natCast_log_nonneg_sourceScale B) _
  have hlogTypical :
      Real.log 2 * taoSection5TypicalSlack B ≤
        taoSection5TypicalSlack B := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right log_two_lt_one_sourceScale.le htypicalNonneg
  have hlost' : taoSection5CanonicalLostSlack B ≤ s / 12 := by
    simpa only [taoSection5CanonicalLostSlack, s] using hlost
  have htypical' : taoSection5TypicalSlack B ≤ s / 12 := by
    simpa only [taoSection5TypicalSlack, s] using htypical
  have hconst' : Real.log 2 ≤ s / 12 := by
    dsimp only [s]
    nlinarith
  have hquarter : s / 4 ≤ Real.log (4 / 3 : ℝ) * s := by
    have hmul := mul_le_mul_of_nonneg_right
      one_fourth_le_log_four_thirds_sourceScale hsNonneg
    nlinarith
  dsimp only [s] at hquarter ⊢
  nlinarith

/-- The source-scale packet holds for all sufficiently large thresholds. -/
theorem eventually_taoSection5AffineSourceScaleFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5AffineSourceScaleFacts B := by
  filter_upwards
    [eventually_taoSection5PassScheduleFacts,
      eventually_taoSection5ReversePrefixScalarBudget,
      eventually_taoSection5AffineSourceMargin]
      with B schedule reverseBudget sourceMargin
  exact ⟨schedule, reverseBudget, sourceMargin⟩

/-- Every endpoint in the scheduled lost window has enough room for the
neutral affine-residue reconstruction at any scheduled prefix length. -/
theorem TaoSection5AffineSourceScaleFacts.endpoint_room
    {B q M : ℕ} (facts : TaoSection5AffineSourceScaleFacts B)
    (hq : q ≤ taoSection5N0 B)
    (hM : M ∈ taoSection5CanonicalLostWindow B) :
    2 * 3 ^ q < M := by
  have hqpow : (3 : ℝ) ^ q ≤ (3 : ℝ) ^ taoSection5N0 B :=
    pow_le_pow_right₀ (by norm_num) hq
  have hn0Bpow :
      (3 : ℝ) ^ taoSection5N0 B ≤ (B : ℝ) ^ (1 / 5 : ℝ) :=
    taoSection5_three_pow_n0_le_threshold_rpow_one_fifth
      facts.schedule.one_le_B
  have hBpowB : (B : ℝ) ^ (1 / 5 : ℝ) ≤ (B : ℝ) := by
    have hpow : (B : ℝ) ^ (1 / 5 : ℝ) ≤ (B : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast facts.schedule.one_le_B) (by norm_num : (1 / 5 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using hpow
  have hslackNonneg : 0 ≤ taoSection5TypicalSlack B := by
    unfold taoSection5TypicalSlack
    exact Real.rpow_nonneg (natCast_log_nonneg_sourceScale B) _
  have hexpOne :
      1 ≤ Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) := by
    apply Real.one_le_exp
    positivity
  have hBexp :
      (B : ℝ) ≤
        Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hexpOne (Nat.cast_nonneg B)
  have htwoPow :
      2 * (3 : ℝ) ^ q ≤
        Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) +
          (3 : ℝ) ^ taoSection5N0 B := by
    nlinarith [hqpow, hn0Bpow.trans hBpowB, hBexp]
  have hlowerM : taoSection5CanonicalLostLower B ≤ (M : ℝ) := by
    have hM' := Finset.mem_Icc.mp hM
    exact Nat.ceil_le.mp hM'.1
  have hreal : 2 * (3 : ℝ) ^ q < (M : ℝ) :=
    htwoPow.trans_lt (facts.reverseBudget.trans_le hlowerM)
  exact_mod_cast hreal

private theorem log_four_thirds_eq_sourceScale :
    Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
    (by norm_num : (3 : ℝ) ≠ 0)]
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
  norm_num

private theorem four_thirds_pow_eq_exp_sourceScale (q : ℕ) :
    (4 / 3 : ℝ) ^ q =
      Real.exp ((q : ℝ) * Real.log (4 / 3 : ℝ)) := by
  calc
    (4 / 3 : ℝ) ^ q =
        (Real.exp (Real.log (4 / 3 : ℝ))) ^ q := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    _ = Real.exp ((q : ℝ) * Real.log (4 / 3 : ℝ)) := by
      rw [← Real.exp_nat_mul]

private theorem two_pow_div_three_pow_eq_exp_sourceScale (q w : ℕ) :
    (2 : ℝ) ^ w / (3 : ℝ) ^ q =
      Real.exp ((w : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3) := by
  have hcoeffPos : 0 < (2 : ℝ) ^ w / (3 : ℝ) ^ q := by positivity
  calc
    (2 : ℝ) ^ w / (3 : ℝ) ^ q =
        Real.exp (Real.log ((2 : ℝ) ^ w / (3 : ℝ) ^ q)) :=
      (Real.exp_log hcoeffPos).symm
    _ = Real.exp ((w : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3) := by
      congr 1
      rw [Real.log_div (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)), Real.log_pow, Real.log_pow]

private theorem exp_neg_log_two_mul_four_thirds_pow_le_two_pow_div_three_pow
    {q w : ℕ} {H : ℝ}
    (hw : 2 * (q : ℝ) - H ≤ (w : ℝ)) :
    Real.exp (-Real.log 2 * H) * (4 / 3 : ℝ) ^ q ≤
      (2 : ℝ) ^ w / (3 : ℝ) ^ q := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hw hlogTwoPos.le
  rw [four_thirds_pow_eq_exp_sourceScale, ← Real.exp_add,
    two_pow_div_three_pow_eq_exp_sourceScale]
  apply Real.exp_le_exp.mpr
  rw [log_four_thirds_eq_sourceScale]
  nlinarith

private theorem two_pow_div_three_pow_le_exp_log_two_mul_four_thirds_pow
    {q w : ℕ} {H : ℝ}
    (hw : (w : ℝ) ≤ 2 * (q : ℝ) + H) :
    (2 : ℝ) ^ w / (3 : ℝ) ^ q ≤
      Real.exp (Real.log 2 * H) * (4 / 3 : ℝ) ^ q := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hw hlogTwoPos.le
  rw [two_pow_div_three_pow_eq_exp_sourceScale,
    four_thirds_pow_eq_exp_sourceScale, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [log_four_thirds_eq_sourceScale]
  nlinarith

private theorem taoOffsetNum_le_two_pow_weight_mul_three_pow_length_sourceScale
    (as : List ℕ+) :
    taoOffsetNum as ≤ 2 ^ taoTupleWeight as * 3 ^ as.length := by
  have hrat :
      (taoOffsetNum as : ℚ) ≤
        ((2 ^ taoTupleWeight as * 3 ^ as.length : ℕ) : ℚ) := by
    calc
      (taoOffsetNum as : ℚ) =
          (2 : ℚ) ^ taoTupleWeight as * taoOffsetList as :=
        (pow_weight_mul_taoOffsetList_eq_num as).symm
      _ ≤ (2 : ℚ) ^ taoTupleWeight as * (3 : ℚ) ^ as.length :=
        mul_le_mul_of_nonneg_left (taoOffsetList_le_three_pow_length as)
          (by positivity)
      _ = ((2 ^ taoTupleWeight as * 3 ^ as.length : ℕ) : ℚ) := by
        norm_num
  exact_mod_cast hrat

/-- Full-prefix closed typicality, endpoint room, and the affine equation give
the exact one-slack real bounds for the reconstructed source. -/
theorem taoSection5_affineSource_real_bounds
    {B q N M : ℕ} {as : List ℕ+}
    (hlen : as.length = q)
    (htyp : taoSection5TypicalTuple B q as)
    (hroom : 2 * 3 ^ q < M)
    (hAff : taoAffList as (N : ℚ) = (M : ℚ)) :
    (1 / 2 : ℝ) *
          Real.exp (-Real.log 2 * taoSection5TypicalSlack B) *
          (4 / 3 : ℝ) ^ q * (M : ℝ) ≤
        (N : ℝ) ∧
      (N : ℝ) ≤
        Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
          (4 / 3 : ℝ) ^ q * (M : ℝ) := by
  let S := taoTupleWeight as
  let h := taoSection5TypicalSlack B
  have htake : as.take q = as := by
    rw [← hlen]
    exact List.take_length
  have hdev := htyp.2 q le_rfl
  rw [htake] at hdev
  have hwLower : 2 * (q : ℝ) - h ≤ (S : ℝ) := by
    dsimp only [S, h]
    linarith [abs_le.mp hdev]
  have hwUpper : (S : ℝ) ≤ 2 * (q : ℝ) + h := by
    dsimp only [S, h]
    linarith [abs_le.mp hdev]
  have hcoeffLower :
      Real.exp (-Real.log 2 * h) * (4 / 3 : ℝ) ^ q ≤
        (2 : ℝ) ^ S / (3 : ℝ) ^ q :=
    exp_neg_log_two_mul_four_thirds_pow_le_two_pow_div_three_pow hwLower
  have hcoeffUpper :
      (2 : ℝ) ^ S / (3 : ℝ) ^ q ≤
        Real.exp (Real.log 2 * h) * (4 / 3 : ℝ) ^ q :=
    two_pow_div_three_pow_le_exp_log_two_mul_four_thirds_pow hwUpper
  have hclearNat := (taoAffList_eq_nat_iff_cleared as N M).mp hAff
  have hclear :
      (3 : ℝ) ^ q * (N : ℝ) + (taoOffsetNum as : ℝ) =
        (2 : ℝ) ^ S * (M : ℝ) := by
    have hcast := congrArg (fun x : ℕ => (x : ℝ)) hclearNat
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      hlen, S] using hcast
  have hoffset :
      (taoOffsetNum as : ℝ) ≤
        (2 : ℝ) ^ S * (3 : ℝ) ^ q := by
    exact_mod_cast (by
      simpa only [S, hlen] using
        taoOffsetNum_le_two_pow_weight_mul_three_pow_length_sourceScale as)
  have hroomReal : 2 * (3 : ℝ) ^ q < (M : ℝ) := by
    exact_mod_cast hroom
  have htwoNonneg : 0 ≤ (2 : ℝ) ^ S := by positivity
  have hscaledRoom := mul_le_mul_of_nonneg_left hroomReal.le htwoNonneg
  have hhalfRaw :
      (2 : ℝ) ^ S * ((M : ℝ) / 2) ≤
        (3 : ℝ) ^ q * (N : ℝ) := by
    nlinarith
  have hthreePos : 0 < (3 : ℝ) ^ q := by positivity
  have hsourceLower :
      ((2 : ℝ) ^ S / (3 : ℝ) ^ q) * ((M : ℝ) / 2) ≤
        (N : ℝ) := by
    calc
      ((2 : ℝ) ^ S / (3 : ℝ) ^ q) * ((M : ℝ) / 2) =
          ((2 : ℝ) ^ S * ((M : ℝ) / 2)) / (3 : ℝ) ^ q := by ring
      _ ≤ ((3 : ℝ) ^ q * (N : ℝ)) / (3 : ℝ) ^ q :=
        (div_le_div_iff_of_pos_right hthreePos).2 hhalfRaw
      _ = (N : ℝ) := by field_simp
  have hoffsetNonneg : 0 ≤ (taoOffsetNum as : ℝ) := by positivity
  have hupperRaw :
      (3 : ℝ) ^ q * (N : ℝ) ≤
        (2 : ℝ) ^ S * (M : ℝ) := by
    nlinarith
  have hsourceUpper :
      (N : ℝ) ≤
        ((2 : ℝ) ^ S / (3 : ℝ) ^ q) * (M : ℝ) := by
    calc
      (N : ℝ) = ((3 : ℝ) ^ q * (N : ℝ)) / (3 : ℝ) ^ q := by
        field_simp
      _ ≤ ((2 : ℝ) ^ S * (M : ℝ)) / (3 : ℝ) ^ q :=
        (div_le_div_iff_of_pos_right hthreePos).2 hupperRaw
      _ = ((2 : ℝ) ^ S / (3 : ℝ) ^ q) * (M : ℝ) := by ring
  constructor
  · calc
      (1 / 2 : ℝ) * Real.exp (-Real.log 2 * taoSection5TypicalSlack B) *
            (4 / 3 : ℝ) ^ q * (M : ℝ) =
          (Real.exp (-Real.log 2 * h) * (4 / 3 : ℝ) ^ q) *
            ((M : ℝ) / 2) := by simp only [h]; ring
      _ ≤ ((2 : ℝ) ^ S / (3 : ℝ) ^ q) * ((M : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hcoeffLower (by positivity)
      _ ≤ (N : ℝ) := hsourceLower
  · calc
      (N : ℝ) ≤
          ((2 : ℝ) ^ S / (3 : ℝ) ^ q) * (M : ℝ) := hsourceUpper
      _ ≤ (Real.exp (Real.log 2 * h) * (4 / 3 : ℝ) ^ q) * (M : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeffUpper (Nat.cast_nonneg M)
      _ = Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
          (4 / 3 : ℝ) ^ q * (M : ℝ) := by simp only [h]

/-- A scheduled chronological affine witness lies between the two real source
endpoints, uniformly in the two Section 5 source branches. -/
theorem taoSection5_scheduledAffineSource_real_bounds
    {B n q N M : ℕ} {branch : TaoSection5SourceBranch} {as : List ℕ+}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hn : n ∈ taoSection5PassTimes B branch)
    (hq : q = n - taoSection5M0 B)
    (htyp : taoSection5TypicalTuple B q as)
    (hM : M ∈ taoSection5CanonicalLostWindow B)
    (hAff : taoAffList as (N : ℚ) = (M : ℚ)) :
    taoSection5SourceY B branch ≤ (N : ℝ) ∧
      (N : ℝ) ≤ Real.rpow (taoSection5SourceY B branch) taoAlpha := by
  let m := taoSection5M0 B
  let h := taoSection5TypicalSlack B
  let g := taoSection5CanonicalLostSlack B
  let s := Real.rpow (Real.log B) (4 / 5 : ℝ)
  let d := Real.log (4 / 3 : ℝ)
  let beta := taoSection5BranchExponent branch
  have hdPos : 0 < d := by
    dsimp only [d]
    exact Real.log_pos (by norm_num)
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast facts.schedule.one_le_B
  have hlogTwoNonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hmle : m ≤ n := by
    simpa only [m] using facts.schedule.m0_le hn
  have hqadd : q + m = n := by
    dsimp only [m]
    rw [hq]
    omega
  have hqle : q ≤ taoSection5N0 B := by
    rw [hq]
    exact facts.schedule.sub_le_n0 hn
  have hroom : 2 * 3 ^ q < M := facts.endpoint_room hqle hM
  have haffBounds :=
    taoSection5_affineSource_real_bounds htyp.1 htyp hroom hAff
  have hnMem := mem_taoSection5PassTimes_iff.mp hn
  have hnLower : taoSection5PassLower B branch ≤ (n : ℝ) :=
    Nat.ceil_le.mp hnMem.1
  have hnUpper : (n : ℝ) ≤ taoSection5PassUpper B branch :=
    (Nat.le_floor_iff (facts.schedule.upper_nonneg branch)).mp hnMem.2
  rw [taoSection5PassLower_eq facts.schedule.one_le_B branch] at hnLower
  rw [taoSection5PassUpper_eq facts.schedule.one_le_B branch] at hnUpper
  have hnLowerScaled :
      (beta - 1) * Real.log B + d * s ≤ (n : ℝ) * d := by
    calc
      (beta - 1) * Real.log B + d * s =
          (((beta - 1) / d) * Real.log B + s) * d := by
        field_simp [hdPos.ne']
      _ ≤ (n : ℝ) * d :=
        mul_le_mul_of_nonneg_right (by simpa only [beta, d, s] using hnLower)
          hdPos.le
  have hnUpperScaled :
      (n : ℝ) * d ≤ (taoAlpha * beta - 1) * Real.log B - d * s := by
    calc
      (n : ℝ) * d ≤
          (((taoAlpha * beta - 1) / d) * Real.log B - s) * d :=
        mul_le_mul_of_nonneg_right (by simpa only [beta, d, s] using hnUpper)
          hdPos.le
      _ = (taoAlpha * beta - 1) * Real.log B - d * s := by
        field_simp [hdPos.ne']
  have hmargin : g + Real.log 2 * h + Real.log 2 ≤ d * s := by
    simpa only [g, h, d, s] using facts.sourceMargin
  have hmarginUpper : g + Real.log 2 * h ≤ d * s := by
    linarith
  have hlowerExponent :
      beta * Real.log B ≤
        -Real.log 2 - Real.log 2 * h - g + (n : ℝ) * d + Real.log B := by
    nlinarith
  have hupperExponent :
      g + Real.log 2 * h + (n : ℝ) * d + Real.log B ≤
        taoAlpha * beta * Real.log B := by
    nlinarith
  have hMmem := Finset.mem_Icc.mp hM
  have hMlower : taoSection5CanonicalLostLower B ≤ (M : ℝ) :=
    Nat.ceil_le.mp hMmem.1
  have hlostUpperNonneg : 0 ≤ taoSection5CanonicalLostUpper B := by
    unfold taoSection5CanonicalLostUpper taoSection5CanonicalLostScale
    positivity
  have hMupper : (M : ℝ) ≤ taoSection5CanonicalLostUpper B :=
    (Nat.le_floor_iff hlostUpperNonneg).mp hMmem.2
  have hhalfExp : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hBexp : (B : ℝ) = Real.exp (Real.log B) :=
    (Real.exp_log hBpos).symm
  have hqaddReal : (q : ℝ) + (m : ℝ) = (n : ℝ) := by
    exact_mod_cast hqadd
  have hlowerScale :
      (1 / 2 : ℝ) * Real.exp (-Real.log 2 * h) *
            (4 / 3 : ℝ) ^ q * taoSection5CanonicalLostLower B =
        Real.exp
          (-Real.log 2 - Real.log 2 * h - g + (n : ℝ) * d + Real.log B) := by
    calc
      _ = Real.exp (-Real.log 2) * Real.exp (-Real.log 2 * h) *
            Real.exp ((q : ℝ) * d) *
              (Real.exp (-g) * (Real.exp ((m : ℝ) * d) * (B : ℝ))) := by
        rw [taoSection5CanonicalLostLower, taoSection5CanonicalLostScale,
          hhalfExp, four_thirds_pow_eq_exp_sourceScale,
          four_thirds_pow_eq_exp_sourceScale]
      _ = Real.exp
            (-Real.log 2 - Real.log 2 * h - g +
              ((q : ℝ) + (m : ℝ)) * d) * (B : ℝ) := by
        calc
          _ = (Real.exp (-Real.log 2) * Real.exp (-Real.log 2 * h) *
                Real.exp ((q : ℝ) * d) * Real.exp (-g) *
                Real.exp ((m : ℝ) * d)) * (B : ℝ) := by ring
          _ = Real.exp
                (-Real.log 2 + (-Real.log 2 * h) + (q : ℝ) * d +
                  (-g) + (m : ℝ) * d) * (B : ℝ) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
          _ = _ := by
            congr 2
            ring
      _ = Real.exp
            (-Real.log 2 - Real.log 2 * h - g +
              ((q : ℝ) + (m : ℝ)) * d) * Real.exp (Real.log B) :=
        congrArg
          (fun x : ℝ => Real.exp
            (-Real.log 2 - Real.log 2 * h - g +
              ((q : ℝ) + (m : ℝ)) * d) * x) hBexp
      _ = Real.exp
          ((-Real.log 2 - Real.log 2 * h - g +
              ((q : ℝ) + (m : ℝ)) * d) + Real.log B) := by
        exact (Real.exp_add _ _).symm
      _ = Real.exp
          (-Real.log 2 - Real.log 2 * h - g + (n : ℝ) * d + Real.log B) := by
        congr 1
        rw [hqaddReal]
  have hupperScale :
      Real.exp (Real.log 2 * h) * (4 / 3 : ℝ) ^ q *
          taoSection5CanonicalLostUpper B =
        Real.exp
          (g + Real.log 2 * h + (n : ℝ) * d + Real.log B) := by
    calc
      _ = Real.exp (Real.log 2 * h) * Real.exp ((q : ℝ) * d) *
            (Real.exp g * (Real.exp ((m : ℝ) * d) * (B : ℝ))) := by
        rw [taoSection5CanonicalLostUpper, taoSection5CanonicalLostScale,
          four_thirds_pow_eq_exp_sourceScale,
          four_thirds_pow_eq_exp_sourceScale]
      _ = Real.exp
            (g + Real.log 2 * h + ((q : ℝ) + (m : ℝ)) * d) *
              (B : ℝ) := by
        calc
          _ = (Real.exp (Real.log 2 * h) * Real.exp ((q : ℝ) * d) *
                Real.exp g * Real.exp ((m : ℝ) * d)) * (B : ℝ) := by ring
          _ = Real.exp
                (Real.log 2 * h + (q : ℝ) * d + g + (m : ℝ) * d) *
                  (B : ℝ) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add]
          _ = _ := by
            congr 2
            ring
      _ = Real.exp
            (g + Real.log 2 * h + ((q : ℝ) + (m : ℝ)) * d) *
              Real.exp (Real.log B) :=
        congrArg
          (fun x : ℝ => Real.exp
            (g + Real.log 2 * h + ((q : ℝ) + (m : ℝ)) * d) * x) hBexp
      _ = Real.exp
          ((g + Real.log 2 * h + ((q : ℝ) + (m : ℝ)) * d) +
            Real.log B) := by
        exact (Real.exp_add _ _).symm
      _ = Real.exp
          (g + Real.log 2 * h + (n : ℝ) * d + Real.log B) := by
        congr 1
        rw [hqaddReal]
  have hyPos : 0 < taoSection5SourceY B branch := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hlogY :
      Real.log (taoSection5SourceY B branch) = beta * Real.log B := by
    rw [taoSection5SourceY_eq_branch_rpow]
    simpa only [beta] using Real.log_rpow hBpos (taoSection5BranchExponent branch)
  have hyExp :
      taoSection5SourceY B branch = Real.exp (beta * Real.log B) := by
    calc
      taoSection5SourceY B branch =
          Real.exp (Real.log (taoSection5SourceY B branch)) :=
        (Real.exp_log hyPos).symm
      _ = Real.exp (beta * Real.log B) := by rw [hlogY]
  have hyAlphaExp :
      Real.rpow (taoSection5SourceY B branch) taoAlpha =
        Real.exp (taoAlpha * beta * Real.log B) := by
    calc
      Real.rpow (taoSection5SourceY B branch) taoAlpha =
          Real.exp (Real.log (taoSection5SourceY B branch) * taoAlpha) :=
        Real.rpow_def_of_pos hyPos _
      _ = Real.exp (taoAlpha * beta * Real.log B) := by
        rw [hlogY]
        congr 1
        ring
  constructor
  · have hfactorNonneg :
        0 ≤ (1 / 2 : ℝ) * Real.exp (-Real.log 2 * h) *
          (4 / 3 : ℝ) ^ q := by positivity
    have hlowerToN :
        (1 / 2 : ℝ) * Real.exp (-Real.log 2 * h) *
              (4 / 3 : ℝ) ^ q * taoSection5CanonicalLostLower B ≤
            (N : ℝ) := by
      calc
        _ ≤ (1 / 2 : ℝ) * Real.exp (-Real.log 2 * h) *
              (4 / 3 : ℝ) ^ q * (M : ℝ) :=
          mul_le_mul_of_nonneg_left hMlower hfactorNonneg
        _ ≤ (N : ℝ) := by simpa only [h] using haffBounds.1
    rw [hyExp]
    rw [hlowerScale] at hlowerToN
    exact (Real.exp_le_exp.mpr hlowerExponent).trans hlowerToN
  · have hfactorNonneg :
        0 ≤ Real.exp (Real.log 2 * h) * (4 / 3 : ℝ) ^ q := by positivity
    have hNtoUpper :
        (N : ℝ) ≤
          Real.exp (Real.log 2 * h) * (4 / 3 : ℝ) ^ q *
            taoSection5CanonicalLostUpper B := by
      calc
        (N : ℝ) ≤ Real.exp (Real.log 2 * h) *
              (4 / 3 : ℝ) ^ q * (M : ℝ) := by
          simpa only [h] using haffBounds.2
        _ ≤ Real.exp (Real.log 2 * h) * (4 / 3 : ℝ) ^ q *
              taoSection5CanonicalLostUpper B :=
          mul_le_mul_of_nonneg_left hMupper hfactorNonneg
    rw [hyAlphaExp]
    rw [hupperScale] at hNtoUpper
    exact hNtoUpper.trans (Real.exp_le_exp.mpr hupperExponent)

end

end Tao
end Erdos1135SecondScale
