/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.AffineAtomReverse
import Erdos1135SecondScale.Tao.Syracuse.AffineCoefficient

/-!
# Section 5 Forward Lost-Window Localization

This leaf localizes the point obtained by stepping back `m0` iterates from a
first hit. The argument is branch-free: terminal and preterminal first-hit
inequalities combine with the last `m0` valuation weights. Passage-time
localization in a branch schedule remains a separate later unit.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped Topology

noncomputable section

/-- Eventual scalar data needed for forward localization into the canonical
lost window. -/
structure TaoSection5PassLostWindowFacts (B : ℕ) : Prop where
  one_le_m0 : 1 ≤ taoSection5M0 B
  typical_lost_margin :
    2 * Real.log 2 * taoSection5TypicalSlack B +
        Real.log (8 / 3 : ℝ) ≤
      taoSection5CanonicalLostSlack B
  preterminal_offset_room :
    2 * (3 : ℝ) ^ (taoSection5M0 B - 1) ≤ (B : ℝ)

theorem TaoSection5PassLostWindowFacts.upper_margin
    {B : ℕ} (facts : TaoSection5PassLostWindowFacts B) :
    2 * Real.log 2 * taoSection5TypicalSlack B ≤
      taoSection5CanonicalLostSlack B := by
  have hlog : 0 ≤ Real.log (8 / 3 : ℝ) :=
    Real.log_nonneg (by norm_num)
  linarith [facts.typical_lost_margin]

private theorem log_two_lt_one_lostWindow :
    Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  exact h

private theorem eventually_taoSection5TypicalSlack_quarter_lostSlack :
    ∀ᶠ B : ℕ in atTop,
      taoSection5TypicalSlack B ≤
        taoSection5CanonicalLostSlack B / 4 := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (-(1 / 10 : ℝ)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp hlog
  filter_upwards
    [hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
      hlog.eventually_gt_atTop (0 : ℝ)] with B hratioB hlogB
  have hlostNonneg :
      0 ≤ Real.rpow (Real.log B) (7 / 10 : ℝ) :=
    Real.rpow_nonneg hlogB.le _
  have hfactor :
    Real.rpow (Real.log B) (3 / 5 : ℝ) =
        Real.rpow (Real.log B) (-(1 / 10 : ℝ)) *
          Real.rpow (Real.log B) (7 / 10 : ℝ) := by
    have hadd := Real.rpow_add hlogB (-(1 / 10 : ℝ)) (7 / 10 : ℝ)
    convert hadd using 1
    norm_num
  rw [taoSection5TypicalSlack, taoSection5CanonicalLostSlack, hfactor]
  nlinarith [mul_le_mul_of_nonneg_right hratioB hlostNonneg]

private theorem eventually_taoSection5PassLostWindowMargin :
    ∀ᶠ B : ℕ in atTop,
      2 * Real.log 2 * taoSection5TypicalSlack B +
          Real.log (8 / 3 : ℝ) ≤
        taoSection5CanonicalLostSlack B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlost :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (7 / 10 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).comp hlog
  filter_upwards
    [eventually_taoSection5TypicalSlack_quarter_lostSlack,
      hlost.eventually_ge_atTop
        (2 * Real.log (8 / 3 : ℝ))] with B htypical hlostLarge
  have htypicalNonneg : 0 ≤ taoSection5TypicalSlack B := by
    unfold taoSection5TypicalSlack
    by_cases hB : B = 0
    · simp [hB]
    · exact Real.rpow_nonneg
        (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hB))) _
  have hlogTypical :
      Real.log 2 * taoSection5TypicalSlack B ≤
        taoSection5TypicalSlack B := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right log_two_lt_one_lostWindow.le htypicalNonneg
  have hlostLarge' :
      2 * Real.log (8 / 3 : ℝ) ≤ taoSection5CanonicalLostSlack B := by
    simpa only [taoSection5CanonicalLostSlack] using hlostLarge
  nlinarith

theorem eventually_taoSection5PassLostWindowFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5PassLostWindowFacts B := by
  filter_upwards
    [eventually_taoSection5PassScheduleFacts,
      eventually_taoSection5DescentScaleFacts,
      eventually_taoSection5PassLostWindowMargin]
      with B schedule descent hmargin
  rcases schedule.nonempty .alpha with ⟨n, hn⟩
  have hm0n0 : taoSection5M0 B ≤ taoSection5N0 B :=
    (schedule.m0_le hn).trans (schedule.range .alpha n hn).2
  have hpow :
      (3 : ℝ) ^ (taoSection5M0 B - 1) ≤
        (3 : ℝ) ^ taoSection5N0 B :=
    pow_le_pow_right₀ (by norm_num) ((Nat.sub_le _ _).trans hm0n0)
  have hsmallPower :
      (B : ℝ) ^ (1 / 5 : ℝ) ≤ (B : ℝ) ^ (99 / 100 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast descent.one_le_B) (by norm_num)
  have hoffset :
      2 * (3 : ℝ) ^ (taoSection5M0 B - 1) ≤ (B : ℝ) := by
    calc
      2 * (3 : ℝ) ^ (taoSection5M0 B - 1) ≤
          2 * (3 : ℝ) ^ taoSection5N0 B := by gcongr
      _ ≤ 2 * (B : ℝ) ^ (1 / 5 : ℝ) := by
        gcongr
        exact descent.offset
      _ = (B : ℝ) ^ (1 / 5 : ℝ) + (B : ℝ) ^ (1 / 5 : ℝ) := by ring
      _ ≤ (B : ℝ) ^ (99 / 100 : ℝ) + (B : ℝ) ^ (1 / 5 : ℝ) :=
        add_le_add_left hsmallPower _
      _ ≤ (B : ℝ) := descent.absorption
  exact
    { one_le_m0 := schedule.one_le_m0
      typical_lost_margin := hmargin
      preterminal_offset_room := hoffset }

/-- Closed prefix typicality also gives the symmetric two-slack upper bound
for every suffix weight. -/
theorem TaoSection5TypicalTuple.tail_weight_upper
    {B r : ℕ} {as : List ℕ+}
    (htyp : taoSection5TypicalTuple B r as)
    {j : ℕ} (hj : j ≤ r) :
    (taoTupleWeight (as.drop j) : ℝ) ≤
      2 * ((r - j : ℕ) : ℝ) + 2 * taoSection5TypicalSlack B := by
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
  have htotalUpper := (abs_le.mp htotal).2
  have hprefixLower := (abs_le.mp hprefix).1
  nlinarith

/-- A first hit at `m0`, together with two-sided suffix-weight control, places
its source between the real canonical lost-window endpoints. -/
theorem taoSection5_firstHit_real_mem_lostWindow_of_tailWeights
    {B M : ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (hM : Odd M)
    (hfullUpper :
      (taoTupleWeight
          (syracuseValuationPNatList (taoSection5M0 B) M hM) : ℝ) ≤
        2 * (taoSection5M0 B : ℝ) +
          2 * taoSection5TypicalSlack B)
    (hpreLower :
      2 * ((taoSection5M0 B - 1 : ℕ) : ℝ) -
          2 * taoSection5TypicalSlack B ≤
        (taoTupleWeight
          (syracuseValuationPNatList (taoSection5M0 B - 1) M hM) : ℝ))
    (hfirst : syracuseFirstHitAtMost B M (taoSection5M0 B)) :
    taoSection5CanonicalLostLower B ≤ (M : ℝ) ∧
      (M : ℝ) ≤ taoSection5CanonicalLostUpper B := by
  let m := taoSection5M0 B
  let h := taoSection5TypicalSlack B
  let g := taoSection5CanonicalLostSlack B
  have hm : 1 ≤ m := facts.one_le_m0
  have hmargin :
      2 * Real.log 2 * h + Real.log (8 / 3 : ℝ) ≤ g := by
    simpa only [m, h, g] using facts.typical_lost_margin
  have hupperMargin : 2 * Real.log 2 * h ≤ g := by
    simpa only [m, h, g] using facts.upper_margin
  have hoffset : 2 * (3 : ℝ) ^ (m - 1) ≤ (B : ℝ) := by
    simpa only [m] using facts.preterminal_offset_room
  have hcoeffLower :=
    exp_neg_log_two_mul_mul_three_four_pow_le_three_pow_div_two_pow
      (q := m)
      (w := taoTupleWeight (syracuseValuationPNatList m M hM))
      (H := 2 * h) (by simpa only [m, h] using hfullUpper)
  have hmainQ := affineMainTerm_le_syracuse_iterate m M hM
  have hmainR :
      (3 : ℝ) ^ m /
            (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList m M hM) *
          (M : ℝ) ≤
        ((syracuse^[m]) M : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hmainQ
    norm_num at hcast ⊢
    exact hcast
  have hterminal : ((syracuse^[m]) M : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hfirst.1
  have hcoeffMain :
      (Real.exp (-Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ m) * (M : ℝ) ≤
        (B : ℝ) := by
    calc
      (Real.exp (-Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ m) * (M : ℝ) ≤
          ((3 : ℝ) ^ m /
            (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList m M hM)) *
              (M : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeffLower (Nat.cast_nonneg M)
      _ ≤ ((syracuse^[m]) M : ℝ) := hmainR
      _ ≤ (B : ℝ) := hterminal
  let inverseFull : ℝ :=
    Real.exp (Real.log 2 * (2 * h)) * (4 / 3 : ℝ) ^ m
  have hinverseFull :
      inverseFull *
          (Real.exp (-Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ m) = 1 := by
    dsimp [inverseFull]
    calc
      (Real.exp (Real.log 2 * (2 * h)) * (4 / 3 : ℝ) ^ m) *
          (Real.exp (-Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ m) =
        (Real.exp (Real.log 2 * (2 * h)) *
          Real.exp (-Real.log 2 * (2 * h))) *
            ((4 / 3 : ℝ) ^ m * (3 / 4 : ℝ) ^ m) := by ring
      _ = 1 := by
        rw [← Real.exp_add, ← mul_pow]
        norm_num
  have hMupperRaw :
      (M : ℝ) ≤ inverseFull * (B : ℝ) := by
    calc
      (M : ℝ) = inverseFull *
          ((Real.exp (-Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ m) *
            (M : ℝ)) := by
        rw [← mul_assoc, hinverseFull, one_mul]
      _ ≤ inverseFull * (B : ℝ) :=
        mul_le_mul_of_nonneg_left hcoeffMain (by positivity)
  have hExpUpper :
      Real.exp (Real.log 2 * (2 * h)) ≤ Real.exp g := by
    apply Real.exp_le_exp.mpr
    nlinarith [hupperMargin]
  have hMupper :
      (M : ℝ) ≤ Real.exp g * (4 / 3 : ℝ) ^ m * (B : ℝ) := by
    calc
      (M : ℝ) ≤ inverseFull * (B : ℝ) := hMupperRaw
      _ ≤ (Real.exp g * (4 / 3 : ℝ) ^ m) * (B : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg B)
        dsimp [inverseFull]
        exact mul_le_mul_of_nonneg_right hExpUpper (by positivity)
      _ = Real.exp g * (4 / 3 : ℝ) ^ m * (B : ℝ) := by ring
  let q := m - 1
  have hcoeffUpper :=
    three_pow_div_two_pow_le_exp_log_two_mul_mul_three_four_pow
      (q := q)
      (w := taoTupleWeight (syracuseValuationPNatList q M hM))
      (H := 2 * h) (by simpa only [m, q, h] using hpreLower)
  have henvelopeQ := syracuse_iterate_le_affine_envelope q M hM
  have henvelopeR :
      ((syracuse^[q]) M : ℝ) ≤
        ((3 : ℝ) ^ q /
            (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList q M hM)) *
            (M : ℝ) +
          (3 : ℝ) ^ q := by
    have hcast := (Rat.cast_le (K := ℝ)).2 henvelopeQ
    norm_num at hcast ⊢
    exact hcast
  have henvelope :
      ((syracuse^[q]) M : ℝ) ≤
        (Real.exp (Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ q) * (M : ℝ) +
          (3 : ℝ) ^ q := by
    calc
      ((syracuse^[q]) M : ℝ) ≤
          ((3 : ℝ) ^ q /
            (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList q M hM)) *
              (M : ℝ) + (3 : ℝ) ^ q := henvelopeR
      _ ≤ (Real.exp (Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ q) *
            (M : ℝ) + (3 : ℝ) ^ q := by
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_right hcoeffUpper (Nat.cast_nonneg M)
  have hpre : (B : ℝ) < ((syracuse^[q]) M : ℝ) := by
    exact_mod_cast hfirst.2 q (by dsimp [q]; omega)
  have hoffsetHalf : (3 : ℝ) ^ q ≤ (B : ℝ) / 2 := by
    dsimp [q] at ⊢
    nlinarith
  have hmainHalf :
      (B : ℝ) / 2 <
        (Real.exp (Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ q) * (M : ℝ) := by
    nlinarith
  let inversePre : ℝ :=
    Real.exp (-Real.log 2 * (2 * h)) * (4 / 3 : ℝ) ^ q
  have hinversePre :
      inversePre *
          (Real.exp (Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ q) = 1 := by
    dsimp [inversePre]
    calc
      (Real.exp (-Real.log 2 * (2 * h)) * (4 / 3 : ℝ) ^ q) *
          (Real.exp (Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ q) =
        (Real.exp (-Real.log 2 * (2 * h)) *
          Real.exp (Real.log 2 * (2 * h))) *
            ((4 / 3 : ℝ) ^ q * (3 / 4 : ℝ) ^ q) := by ring
      _ = 1 := by
        rw [← Real.exp_add, ← mul_pow]
        norm_num
  have hpreLowerRaw : inversePre * ((B : ℝ) / 2) < (M : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hmainHalf (by positivity : 0 < inversePre)
    calc
      inversePre * ((B : ℝ) / 2) <
          inversePre *
            ((Real.exp (Real.log 2 * (2 * h)) * (3 / 4 : ℝ) ^ q) *
              (M : ℝ)) := hmul
      _ = (M : ℝ) := by rw [← mul_assoc, hinversePre, one_mul]
  have hmDecomp : m = q + 1 := by
    dsimp [q]
    omega
  have hExpMargin :
      Real.exp (-g + Real.log (8 / 3 : ℝ)) ≤
        Real.exp (-Real.log 2 * (2 * h)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hmargin]
  have hfactor :
      2 * (Real.exp (-g) * (4 / 3 : ℝ) ^ m) ≤ inversePre := by
    calc
      2 * (Real.exp (-g) * (4 / 3 : ℝ) ^ m) =
          Real.exp (-g) * (8 / 3 : ℝ) * (4 / 3 : ℝ) ^ q := by
        rw [hmDecomp, pow_succ]
        ring
      _ = Real.exp (-g + Real.log (8 / 3 : ℝ)) * (4 / 3 : ℝ) ^ q := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8 / 3)]
      _ ≤ Real.exp (-Real.log 2 * (2 * h)) * (4 / 3 : ℝ) ^ q :=
        mul_le_mul_of_nonneg_right hExpMargin (by positivity)
      _ = inversePre := rfl
  have hcanonicalLower :
      Real.exp (-g) * (4 / 3 : ℝ) ^ m * (B : ℝ) ≤
        inversePre * ((B : ℝ) / 2) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor (show 0 ≤ (B : ℝ) / 2 by positivity)
    nlinarith
  have hMlower :
      Real.exp (-g) * (4 / 3 : ℝ) ^ m * (B : ℝ) ≤ (M : ℝ) :=
    hcanonicalLower.trans hpreLowerRaw.le
  constructor
  · simpa only [taoSection5CanonicalLostLower,
      taoSection5CanonicalLostScale, m, h, g, mul_assoc] using hMlower
  · simpa only [taoSection5CanonicalLostUpper,
      taoSection5CanonicalLostScale, m, h, g, mul_assoc] using hMupper

/-- A closed-typical original passage event localizes its `m0`-step-back point
inside the canonical target `EPrime`. -/
theorem taoSection5PassEvent_shifted_mem_EPrime
    {B n N : ℕ} {E : Set ℕ}
    (facts : TaoSection5PassLostWindowFacts B)
    (hN : Odd N)
    (hm : taoSection5M0 B ≤ n)
    (htyp : taoSection5TypicalTuple B n
      (syracuseValuationPNatList n N hN))
    (hpass : taoSection5PassEventAtTime B N n E) :
    (syracuse^[n - taoSection5M0 B]) N ∈ taoSection5EPrime B E := by
  let m := taoSection5M0 B
  let r := n - m
  let M := (syracuse^[r]) N
  have hrn : r ≤ n := by dsimp [r]; omega
  have hM : Odd M := by
    exact syracuse_iterate_odd_trajectory r N hN
  have hdropFull :
      (syracuseValuationPNatList n N hN).drop r =
        syracuseValuationPNatList m M hM := by
    have hdrop := syracuseValuationPNatList_drop_of_le hN hrn
    simpa only [r, m, M, Nat.sub_sub_self hm] using hdrop
  have hfullUpperGlobal :=
    TaoSection5TypicalTuple.tail_weight_upper htyp hrn
  have hfullUpper :
      (taoTupleWeight (syracuseValuationPNatList m M hM) : ℝ) ≤
        2 * (m : ℝ) + 2 * taoSection5TypicalSlack B := by
    rw [← hdropFull]
    simpa only [r, m, Nat.sub_sub_self hm] using hfullUpperGlobal
  have hnPos : 1 ≤ n := facts.one_le_m0.trans hm
  have hmOne : 1 ≤ m := by simpa only [m] using facts.one_le_m0
  have hnPrev : n - 1 ≤ n := Nat.sub_le n 1
  have hrPrev : r ≤ n - 1 := by
    dsimp [r, m]
    omega
  have htypPrevRaw := TaoSection5TypicalTuple.take htyp hnPrev
  have htypPrev :
      taoSection5TypicalTuple B (n - 1)
        (syracuseValuationPNatList (n - 1) N hN) := by
    simpa only [syracuseValuationPNatList_take_of_le hN hnPrev] using htypPrevRaw
  have hpreLowerGlobal :=
    TaoSection5TypicalTuple.tail_weight_lower htypPrev hrPrev
  have hdropPre :
      (syracuseValuationPNatList (n - 1) N hN).drop r =
        syracuseValuationPNatList (m - 1) M hM := by
    have hdrop := syracuseValuationPNatList_drop_of_le hN hrPrev
    have hlength : (n - 1) - r = m - 1 := by
      dsimp [r, m]
      omega
    simpa only [r, m, M, hlength] using hdrop
  have hpreLower :
      2 * ((m - 1 : ℕ) : ℝ) - 2 * taoSection5TypicalSlack B ≤
        (taoTupleWeight (syracuseValuationPNatList (m - 1) M hM) : ℝ) := by
    rw [← hdropPre]
    have hlength : (n - 1) - r = m - 1 := by
      dsimp [r, m]
      omega
    simpa only [hlength] using hpreLowerGlobal
  rcases (taoSection5PassEventAtTime_iff_stepBack E hm).1 hpass with
    ⟨_hprefix, htailFirst, hterminal⟩
  have htailFirstM : syracuseFirstHitAtMost B M m := by
    simpa only [r, m, M] using htailFirst
  have hbounds :=
    taoSection5_firstHit_real_mem_lostWindow_of_tailWeights
      facts hM hfullUpper hpreLower htailFirstM
  have hupperNonneg : 0 ≤ taoSection5CanonicalLostUpper B := by
    unfold taoSection5CanonicalLostUpper taoSection5CanonicalLostScale
    positivity
  apply mem_taoSection5EPrime_iff.mpr
  refine
    ⟨Nat.ceil_le.mpr hbounds.1,
      (Nat.le_floor_iff hupperNonneg).mpr hbounds.2,
      hM, htailFirstM, ?_⟩
  simpa only [r, m, M] using hterminal

theorem eventually_taoSection5PassEvent_shifted_mem_EPrime :
    ∀ᶠ B : ℕ in atTop,
      ∀ {n N : ℕ} {E : Set ℕ} (hN : Odd N),
        taoSection5M0 B ≤ n →
        taoSection5TypicalTuple B n
          (syracuseValuationPNatList n N hN) →
        taoSection5PassEventAtTime B N n E →
        (syracuse^[n - taoSection5M0 B]) N ∈ taoSection5EPrime B E := by
  filter_upwards [eventually_taoSection5PassLostWindowFacts] with B facts
  intro n N E hN hm htyp hpass
  exact taoSection5PassEvent_shifted_mem_EPrime facts hN hm htyp hpass

end

end Tao
end Erdos1135SecondScale
