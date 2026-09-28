import Erdos1135.ND.Band.A5ReferenceExteriorFiniteTail
import Erdos1135.ND.Band.A5ReferenceIntegerRoom
import Erdos1135.Tao.Section5.FixedTimeMixing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A5 exterior coefficient logarithmic rate

This scalar leaf discharges the retained terminal cap, absorbs the two
explicit Geom(2) events and the high-envelope remainder, and then averages
the residue-uniform coefficient bound to exterior CommonZ without a residue
cardinality loss.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology BigOperators

noncomputable section

/-- The visible retained-carrier terminal budget is eventually below its
ambient logarithmic cap. -/
theorem eventually_ndA5EndpointTerminalCapBudget :
    ∀ᶠ B : ℕ in atTop, NDA5EndpointTerminalCapBudget B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto
        (fun B : ℕ =>
          Real.rpow (Real.log (B : ℝ)) (-(3 / 10 : ℝ)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 10)).comp hlog
  filter_upwards
      [hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 20),
        hlog.eventually_ge_atTop (20 * Real.log (8 / 3 : ℝ)),
        eventually_ge_atTop (1 : ℕ)]
      with B hratioB hlogLarge hB
  let L : ℝ := Real.log B
  have hlogEightThirds : 0 < Real.log (8 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hLpos : 0 < L := by
    dsimp only [L]
    nlinarith
  have hL0 : 0 ≤ L := hLpos.le
  have hlost : Tao.taoSection5CanonicalLostSlack B ≤ L / 20 := by
    unfold Tao.taoSection5CanonicalLostSlack
    calc
      Real.rpow L (7 / 10 : ℝ) =
          Real.rpow L (-(3 / 10 : ℝ) + 1) := by norm_num
      _ = Real.rpow L (-(3 / 10 : ℝ)) * Real.rpow L (1 : ℝ) :=
        Real.rpow_add hLpos _ _
      _ = Real.rpow L (-(3 / 10 : ℝ)) * L := by
        rw [show Real.rpow L (1 : ℝ) = L from Real.rpow_one L]
      _ ≤ (1 / 20 : ℝ) * L :=
        mul_le_mul_of_nonneg_right (by simpa only [L] using hratioB) hL0
      _ = L / 20 := by ring
  have hconstant : Real.log (8 / 3 : ℝ) ≤ L / 20 := by
    dsimp only [L] at hlogLarge ⊢
    linarith
  have hm0 :
      (Tao.taoSection5M0 B : ℝ) ≤ L / 100000 := by
    simpa only [L] using
      Tao.taoSection5M0_cast_le_log_div_hundred_thousand hB
  have hlogTwo0 : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hlogTwoLe : Real.log (2 : ℝ) ≤ 1 :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hmLog :
      (Tao.taoSection5M0 B : ℝ) * Real.log 2 ≤
        (L / 100000) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hm0 hlogTwo0
  have hlogScale :
      (L / 100000) * Real.log 2 ≤ L / 100000 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlogTwoLe
        (div_nonneg hL0 (by norm_num))
  have hm0Term :
      2 * (Tao.taoSection5M0 B : ℝ) * Real.log 2 ≤ L / 50000 := by
    nlinarith [hmLog, hlogScale]
  have hbudget :
      ndA5EndpointTerminalLogBudget B ≤ (55001 / 50000 : ℝ) * L := by
    unfold ndA5EndpointTerminalLogBudget
    nlinarith
  have hthreeFifths : (3 / 5 : ℝ) < Real.log 2 := by
    exact (by norm_num : (3 / 5 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hfirst :
      (55001 / 50000 : ℝ) * L < (6 / 5 : ℝ) * L :=
    mul_lt_mul_of_pos_right (by norm_num) hLpos
  have hsecond :
      (6 / 5 : ℝ) * L < 2 * Real.log 2 * L :=
    mul_lt_mul_of_pos_right (by nlinarith [hthreeFifths]) hLpos
  change ndA5EndpointTerminalLogBudget B ≤
    2 * Real.log 2 * Real.log B
  simpa only [L] using (hbudget.trans_lt (hfirst.trans hsecond)).le

set_option maxHeartbeats 800000 in
private theorem eventually_ndA5ReferenceExteriorScalePacket
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      2 ≤ Tao.taoSection5M0 B ∧
      3 < ndA5ReferenceExteriorUpperThreshold B C ∧
      (129 / 32 : ℝ) * Real.log (Real.log B) ≤
        min
          ((ndA5ReferenceExteriorUpperThreshold B C) ^ 2 /
            (32 * (Tao.taoSection5M0 B : ℝ)))
          (ndA5ReferenceExteriorUpperThreshold B C / 8) ∧
      (129 / 32 : ℝ) * Real.log (Real.log B) ≤
        min
          ((ndA5ReferenceExteriorLowerThreshold B C) ^ 2 /
            (32 * ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ)))
          (ndA5ReferenceExteriorLowerThreshold B C / 8) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnegTenth :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log (B : ℝ)) (-(1 / 10 : ℝ)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hlog
  have hlogSmallReal :=
    Real.isLittleO_log_id_atTop.bound
      (by norm_num : (0 : ℝ) < 1 / 1100000)
  have hlogSmall := hlog.eventually hlogSmallReal
  filter_upwards
      [hlog.eventually_ge_atTop (Real.exp 1),
        hnegTenth.eventually_le_const (by norm_num : (0 : ℝ) < 7 / 50),
        hlogSmall,
        eventually_ndA5ReferenceLevel_integer_room]
      with B hLlarge hnegSmall hlogRatio hroom
  let L : ℝ := Real.log B
  let Lambda : ℝ := Real.log L
  let N : ℝ := Tao.taoSection5N0 B
  let m : ℝ := Tao.taoSection5M0 B
  let ell : ℝ := Real.log 2
  let u : ℝ := ndA5ReferenceExteriorUpperThreshold B C
  let v : ℝ := ndA5ReferenceExteriorLowerThreshold B C
  have hLpos : 0 < L := by
    dsimp only [L]
    exact (Real.exp_pos 1).trans_le hLlarge
  have hLOne : 1 ≤ L := by
    calc
      (1 : ℝ) = Real.exp 0 := by norm_num
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ L := by simpa only [L] using hLlarge
  have hLambdaOne : 1 ≤ Lambda := by
    dsimp only [Lambda]
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by
      rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1)
      (by simpa only [L] using hLlarge)
  have hLambda0 : 0 ≤ Lambda := zero_le_one.trans hLambdaOne
  have hlogLinear : 1100000 * Lambda ≤ L := by
    have hratio' : |Real.log L| ≤ (1 / 1100000 : ℝ) * |L| := by
      simpa only [L, Real.norm_eq_abs, id_eq] using hlogRatio
    rw [abs_of_nonneg hLambda0, abs_of_nonneg hLpos.le] at hratio'
    nlinarith
  have hellPos : 0 < ell := by
    dsimp only [ell]
    exact Real.log_pos (by norm_num)
  have hellUpper : ell < 7 / 10 := by
    dsimp only [ell]
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hNlowerRaw : L / (10 * ell) - 1 < N := by
    simpa only [L, N, ell] using
      Tao.log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hNlower : (7 / 50 : ℝ) * L ≤ N := by
    have hL350 : (350 : ℝ) ≤ L := by
      have hLambdaLe : (1100000 : ℝ) ≤ 1100000 * Lambda := by
        nlinarith
      linarith
    have hdiv : L / 7 < L / (10 * ell) := by
      apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 7)
        (mul_pos (by norm_num) hellPos)).2
      nlinarith
    nlinarith
  have hNpos : 0 < N := by
    have : 0 < (7 / 50 : ℝ) * L := mul_pos (by norm_num) hLpos
    exact this.trans_le hNlower
  have hlogN0 : 0 ≤ Real.log N :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (7 / 50 : ℝ) * L := by
        have hL350 : (350 : ℝ) ≤ L := by
          have hLambdaLe : (1100000 : ℝ) ≤ 1100000 * Lambda := by
            nlinarith
          linarith
        nlinarith
      exact this.trans hNlower)
  have hLpow :
      Real.rpow L (9 / 10 : ℝ) ≤ (7 / 50 : ℝ) * L := by
    calc
      Real.rpow L (9 / 10 : ℝ) =
          Real.rpow L (-(1 / 10 : ℝ) + 1) := by norm_num
      _ = Real.rpow L (-(1 / 10 : ℝ)) * Real.rpow L (1 : ℝ) :=
        Real.rpow_add hLpos _ _
      _ = Real.rpow L (-(1 / 10 : ℝ)) * L := by
        rw [show Real.rpow L (1 : ℝ) = L from Real.rpow_one L]
      _ ≤ (7 / 50 : ℝ) * L :=
        mul_le_mul_of_nonneg_right
          (by simpa only [L] using hnegSmall) hLpos.le
  have hlogNlower : (9 / 10 : ℝ) * Lambda ≤ Real.log N := by
    have hpowPos : 0 < Real.rpow L (9 / 10 : ℝ) :=
      Real.rpow_pos_of_pos hLpos _
    have hlogMono := Real.log_le_log hpowPos (hLpow.trans hNlower)
    calc
      (9 / 10 : ℝ) * Lambda =
          Real.log (Real.rpow L (9 / 10 : ℝ)) := by
        simpa only [Lambda] using
          (Real.log_rpow hLpos (9 / 10 : ℝ)).symm
      _ ≤ Real.log N := hlogMono
  have hmUpper : m ≤ L / 100000 := by
    have hB : 1 ≤ B := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hzero
      subst B
      have : ¬(0 : ℝ) < 0 := lt_irrefl 0
      apply this
      simpa only [L, Nat.cast_zero, Real.log_zero] using hLpos
    simpa only [m, L] using
      Tao.taoSection5M0_cast_le_log_div_hundred_thousand hB
  have hmPos : 0 < m := by
    dsimp only [m]
    exact_mod_cast (by omega : 0 < Tao.taoSection5M0 B)
  have hbase : 0 ≤ N * Real.log N := mul_nonneg hNpos.le hlogN0
  have hrootSq :
      (Real.sqrt (N * Real.log N)) ^ 2 = N * Real.log N :=
    Real.sq_sqrt hbase
  have hu0 : 0 ≤ u := by
    dsimp only [u, ndA5ReferenceExteriorUpperThreshold,
      ndA5TubeWidth]
    positivity
  have huSq :
      (36 / 21875 : ℝ) * L * Lambda ≤ u ^ 2 := by
    have hCLower : (2 / 25 : ℝ) ≤ (4 / 25 : ℝ) * C := by
      nlinarith
    have hcoef : (4 / 35 : ℝ) ≤ ((4 / 25 : ℝ) * C) / ell := by
      apply (le_div_iff₀ hellPos).2
      nlinarith
    have hroot0 : 0 ≤ Real.sqrt (N * Real.log N) := Real.sqrt_nonneg _
    have huRoot :
        (4 / 35 : ℝ) * Real.sqrt (N * Real.log N) ≤ u := by
      dsimp only [u, ndA5ReferenceExteriorUpperThreshold,
        ndA5TubeWidth]
      calc
        (4 / 35 : ℝ) * Real.sqrt (N * Real.log N) ≤
            (((4 / 25 : ℝ) * C) / ell) *
              Real.sqrt (N * Real.log N) :=
          mul_le_mul_of_nonneg_right hcoef hroot0
        _ = ((4 / 25 : ℝ) *
              (C * Real.sqrt (N * Real.log N))) / ell := by ring
    have huRootSq := (sq_le_sq₀ (by positivity) hu0).2 huRoot
    rw [mul_pow, hrootSq] at huRootSq
    have hNLambda :
        (63 / 500 : ℝ) * L * Lambda ≤ N * Real.log N := by
      have hmul := mul_le_mul hNlower hlogNlower
        (mul_nonneg (by norm_num) hLambda0) hNpos.le
      nlinarith
    nlinarith
  have huQuad :
      (36 / 7 : ℝ) * Lambda ≤ u ^ 2 / (32 * m) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hmPos)).2
    have hmScaled : 32 * m ≤ (32 / 100000 : ℝ) * L := by
      nlinarith
    nlinarith
  have huLarge : 42 * Lambda ≤ u := by
    have hsq : (42 * Lambda) ^ 2 ≤ u ^ 2 := by
      nlinarith [huSq, hlogLinear]
    exact (sq_le_sq₀ (by positivity) hu0).1 hsq
  have hvDef : v = u - 3 := by
    rfl
  have hv0 : 0 < v := by
    rw [hvDef]
    nlinarith
  have hvRatio : (9 / 10 : ℝ) * u ≤ v := by
    rw [hvDef]
    nlinarith
  have hvLambda : 39 * Lambda ≤ v := by
    calc
      39 * Lambda ≤ 42 * Lambda - 3 := by nlinarith [hLambdaOne]
      _ ≤ u - 3 := sub_le_sub_right huLarge 3
      _ = v := hvDef.symm
  have hmSubPos : (0 : ℝ) < ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < Tao.taoSection5M0 B - 1)
  have hmSubLe :
      ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ) ≤ m := by
    dsimp only [m]
    exact_mod_cast Nat.sub_le (Tao.taoSection5M0 B) 1
  have hvSq : (81 / 100 : ℝ) * u ^ 2 ≤ v ^ 2 := by
    nlinarith [sq_le_sq₀ (by positivity) hv0.le |>.2 hvRatio]
  have hvQuad :
      (729 / 175 : ℝ) * Lambda ≤
        v ^ 2 / (32 * ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hmSubPos)).2
    have hscaled :
        (729 / 175 : ℝ) * Lambda *
            (32 * ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ)) ≤
          (81 / 100 : ℝ) * u ^ 2 := by
      have huQuadMul :
          (36 / 7 : ℝ) * Lambda * (32 * m) ≤ u ^ 2 :=
        (le_div_iff₀ (mul_pos (by norm_num) hmPos)).mp huQuad
      have hden :
          32 * ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ) ≤ 32 * m :=
        mul_le_mul_of_nonneg_left hmSubLe (by norm_num)
      calc
        (729 / 175 : ℝ) * Lambda *
            (32 * ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ)) =
          (81 / 100 : ℝ) *
            ((36 / 7 : ℝ) * Lambda *
              (32 * ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ))) := by ring
        _ ≤ (81 / 100 : ℝ) *
            ((36 / 7 : ℝ) * Lambda * (32 * m)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hden
            (mul_nonneg (by norm_num) hLambda0)
        _ ≤ (81 / 100 : ℝ) * u ^ 2 :=
          mul_le_mul_of_nonneg_left huQuadMul (by norm_num)
    exact hscaled.trans hvSq
  refine ⟨by omega, by nlinarith [huLarge, hLambdaOne], ?_, ?_⟩
  · apply le_min
    · exact (by nlinarith :
        (129 / 32 : ℝ) * Lambda ≤ (36 / 7 : ℝ) * Lambda).trans huQuad
    · exact (by nlinarith :
        (129 / 32 : ℝ) * Lambda ≤ (21 / 4 : ℝ) * Lambda).trans
          (by nlinarith : (21 / 4 : ℝ) * Lambda ≤ u / 8)
  · apply le_min
    · exact (by nlinarith :
        (129 / 32 : ℝ) * Lambda ≤ (729 / 175 : ℝ) * Lambda).trans hvQuad
    · exact (by nlinarith :
        (129 / 32 : ℝ) * Lambda ≤ (39 / 8 : ℝ) * Lambda).trans
          (by nlinarith : (39 / 8 : ℝ) * Lambda ≤ v / 8)

private theorem
    eventually_log_add_one_mul_ndA5ReferenceExteriorTwoEventTail_le_half_log_rpow_neg_three
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      (Real.log B + 1) * ndA5ReferenceExteriorTwoEventTail B C ≤
        (1 / 2 : ℝ) * Real.rpow (Real.log B) (-3 : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnegThirtySecond :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log (B : ℝ)) (-(1 / 32 : ℝ)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp hlog
  filter_upwards
      [eventually_ndA5ReferenceExteriorScalePacket C hC,
        hlog.eventually_ge_atTop (1 : ℝ),
        hnegThirtySecond.eventually_le_const
          (by norm_num : (0 : ℝ) < 1 / 16)]
      with B hscale hLOne hsmall
  rcases hscale with ⟨_hm, _htube, hu, hv⟩
  let L : ℝ := Real.log B
  let Lambda : ℝ := Real.log L
  let U : ℝ :=
    min
      ((ndA5ReferenceExteriorUpperThreshold B C) ^ 2 /
        (32 * (Tao.taoSection5M0 B : ℝ)))
      (ndA5ReferenceExteriorUpperThreshold B C / 8)
  let V : ℝ :=
    min
      ((ndA5ReferenceExteriorLowerThreshold B C) ^ 2 /
        (32 * ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ)))
      (ndA5ReferenceExteriorLowerThreshold B C / 8)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact zero_lt_one.trans_le hLOne
  have hLambdaU : (129 / 32 : ℝ) * Lambda ≤ U := by
    simpa only [L, Lambda, U] using hu
  have hLambdaV : (129 / 32 : ℝ) * Lambda ≤ V := by
    simpa only [L, Lambda, V] using hv
  have hexp :
      Real.exp (-(129 / 32 : ℝ) * Lambda) =
        Real.rpow L (-129 / 32 : ℝ) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hLpos]
    congr 1
    dsimp only [Lambda]
    ring
  have hUexp :
      Real.exp (-U) ≤ Real.rpow L (-129 / 32 : ℝ) := by
    rw [← hexp]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hVexp :
      Real.exp (-V) ≤ Real.rpow L (-129 / 32 : ℝ) := by
    rw [← hexp]
    apply Real.exp_le_exp.mpr
    nlinarith
  have htail :
      ndA5ReferenceExteriorTwoEventTail B C ≤
        4 * Real.rpow L (-129 / 32 : ℝ) := by
    unfold ndA5ReferenceExteriorTwoEventTail
    simpa only [U, V] using (by nlinarith [hUexp, hVexp] :
      2 * Real.exp (-U) + 2 * Real.exp (-V) ≤
        4 * Real.rpow L (-129 / 32 : ℝ))
  have hadd : L + 1 ≤ 2 * L := by
    dsimp only [L]
    linarith
  have hfactor :
      L * Real.rpow L (-129 / 32 : ℝ) =
        Real.rpow L (-3 : ℝ) * Real.rpow L (-(1 / 32 : ℝ)) := by
    calc
      L * Real.rpow L (-129 / 32 : ℝ) =
          Real.rpow L (1 : ℝ) * Real.rpow L (-129 / 32 : ℝ) := by
            congr 1
            simpa only [Real.rpow_eq_pow] using (Real.rpow_one L).symm
      _ = Real.rpow L ((1 : ℝ) + (-129 / 32 : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L ((-3 : ℝ) + (-(1 / 32 : ℝ))) := by
        norm_num
      _ = Real.rpow L (-3 : ℝ) * Real.rpow L (-(1 / 32 : ℝ)) :=
        Real.rpow_add hLpos _ _
  calc
    (Real.log B + 1) * ndA5ReferenceExteriorTwoEventTail B C =
        (L + 1) * ndA5ReferenceExteriorTwoEventTail B C := by rfl
    _ ≤ (L + 1) * (4 * Real.rpow L (-129 / 32 : ℝ)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ (2 * L) * (4 * Real.rpow L (-129 / 32 : ℝ)) :=
      mul_le_mul_of_nonneg_right hadd (by
        apply mul_nonneg (by norm_num)
        simpa only [Real.rpow_eq_pow] using
          Real.rpow_nonneg hLpos.le (-129 / 32 : ℝ))
    _ = 8 * (Real.rpow L (-3 : ℝ) *
        Real.rpow L (-(1 / 32 : ℝ))) := by rw [← hfactor]; ring
    _ ≤ 8 * (Real.rpow L (-3 : ℝ) * (1 / 16 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _
      · simpa only [Real.rpow_eq_pow] using
          Real.rpow_nonneg hLpos.le (-3 : ℝ)
      simpa only [L] using hsmall
    _ = (1 / 2 : ℝ) * Real.rpow (Real.log B) (-3 : ℝ) := by
      dsimp only [L]
      ring

private theorem eventually_three_mul_rpow_le_half_log_rpow_neg_three :
    ∀ᶠ B : ℕ in atTop,
      3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) ≤
        (1 / 2 : ℝ) * Real.rpow (Real.log B) (-3 : ℝ) := by
  let a : ℝ := 4997 / 600000
  have ha : 0 < a := by
    dsimp only [a]
    norm_num
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay :
      Tendsto
        (fun L : ℝ =>
          6 * Real.rpow L (3 : ℝ) * Real.exp (-a * L))
        atTop (nhds 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (3 : ℝ) a ha).const_mul 6
  have hsmall :
      ∀ᶠ B : ℕ in atTop,
        6 * Real.rpow (Real.log B) (3 : ℝ) *
            Real.exp (-a * Real.log B) ≤ 1 :=
    (hdecay.comp hlog).eventually_le_const (by norm_num)
  filter_upwards [hlog.eventually_ge_atTop (1 : ℝ), hsmall]
    with B hLOne hsmallB
  let L : ℝ := Real.log B
  have hLpos : 0 < L := by
    dsimp only [L]
    exact zero_lt_one.trans_le hLOne
  have hBpos : (0 : ℝ) < B := by
    have hBnat : 0 < B := by
      apply Nat.pos_of_ne_zero
      intro hBzero
      subst B
      norm_num at hLOne
    exact_mod_cast hBnat
  have hpowPos : 0 < Real.rpow L (3 : ℝ) := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_pos_of_pos hLpos (3 : ℝ)
  have hscaled :
      (3 * Real.exp (-a * L)) * Real.rpow L (3 : ℝ) ≤
        (1 / 2 : ℝ) := by
    calc
      (3 * Real.exp (-a * L)) * Real.rpow L (3 : ℝ) =
          (1 / 2 : ℝ) *
            (6 * Real.rpow L (3 : ℝ) * Real.exp (-a * L)) := by ring
      _ ≤ (1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left
          (by simpa only [L] using hsmallB) (by norm_num)
      _ = (1 / 2 : ℝ) := by ring
  have hdiv :
      3 * Real.exp (-a * L) ≤
        (1 / 2 : ℝ) / Real.rpow L (3 : ℝ) :=
    (le_div_iff₀ hpowPos).2 hscaled
  have hneg :
      Real.rpow L (-3 : ℝ) =
        1 / Real.rpow L (3 : ℝ) := by
    calc
      Real.rpow L (-3 : ℝ) =
          (Real.rpow L (3 : ℝ))⁻¹ := by
            simpa only [Real.rpow_eq_pow] using
              Real.rpow_neg hLpos.le (3 : ℝ)
      _ = 1 / Real.rpow L (3 : ℝ) :=
        (one_div (Real.rpow L (3 : ℝ))).symm
  calc
    3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) =
        3 * Real.exp (-a * L) := by
      rw [Real.rpow_def_of_pos hBpos]
      dsimp only [a, L]
      congr 1
      ring_nf
    _ ≤ (1 / 2 : ℝ) / Real.rpow L (3 : ℝ) := hdiv
    _ = (1 / 2 : ℝ) * Real.rpow L (-3 : ℝ) := by
      rw [hneg]
      ring
    _ = (1 / 2 : ℝ) * Real.rpow (Real.log B) (-3 : ℝ) := by rfl

/-- At the scheduled common reference level, every exterior endpoint
coefficient has the frozen inverse-log-cube rate, uniformly in the endpoint
set and residue. -/
theorem eventually_ndA5ReferenceExteriorCoefficient_le_log_rpow_neg_three
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (E : Set ℕ) (X : ZMod (3 ^ ndA5ReferenceLevel B)),
        Tao.taoSection5PayloadFreeCoefficient
            (ndA5ReferenceLevel B)
            (ndA5ReferenceExteriorEndpoints B C E) X ≤
          Real.rpow (Real.log B) (-3 : ℝ) := by
  filter_upwards
      [Tao.eventually_taoSection5PassLostWindowFacts,
        eventually_ndA5EndpointTerminalCapBudget,
        Tao.eventually_taoSection5PassScheduleFacts,
        eventually_ndA5ReferenceLevel_integer_room,
        eventually_ndA5ReferenceExteriorScalePacket C hC,
        eventually_log_add_one_mul_ndA5ReferenceExteriorTwoEventTail_le_half_log_rpow_neg_three
          C hC,
        eventually_three_mul_rpow_le_half_log_rpow_neg_three]
      with B facts hcap schedule hroom hscale htail hhigh
  intro E X
  rcases hscale with ⟨hm, htube, _hu, _hv⟩
  have hindex :
      Tao.taoSection5M0 B + ndA5ReferenceLevel B ≤
        Tao.taoSection5N0 B := by
    obtain ⟨n, hn⟩ := schedule.nonempty Tao.TaoSection5SourceBranch.alpha
    have hrange := schedule.range Tao.TaoSection5SourceBranch.alpha n hn
    have htwo :
        2 * Tao.taoSection5M0 B ≤ Tao.taoSection5N0 B :=
      hrange.1.trans hrange.2
    omega
  calc
    Tao.taoSection5PayloadFreeCoefficient
          (ndA5ReferenceLevel B)
          (ndA5ReferenceExteriorEndpoints B C E) X ≤
        (Real.log B + 1) *
            ndA5ReferenceExteriorTwoEventTail B C +
          3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) :=
      ndA5ReferenceExteriorCoefficient_le_twoEventTail_add_three_mul_rpow
        facts hcap hm htube hindex
    _ ≤ (1 / 2 : ℝ) * Real.rpow (Real.log B) (-3 : ℝ) +
        (1 / 2 : ℝ) * Real.rpow (Real.log B) (-3 : ℝ) :=
      add_le_add htail hhigh
    _ = Real.rpow (Real.log B) (-3 : ℝ) := by ring

/-- A residue-uniform coefficient bound averages to CommonZ without a
cardinality loss, because the Syracuse mass vector has total mass one. -/
theorem taoSection5PayloadFreeCommonZ_le_of_coefficient_le
    {m : ℕ} {S : Finset ℕ} {R : ℝ}
    (hcoeff : ∀ X : ZMod (3 ^ m),
      Tao.taoSection5PayloadFreeCoefficient m S X ≤ R) :
    Tao.taoSection5PayloadFreeCommonZ m S ≤ R := by
  classical
  rw [Tao.taoSection5PayloadFreeCommonZ_eq_fineSyracWeightedTerm]
  unfold Tao.taoSection5FineSyracWeightedTerm
  calc
    (∑ X : ZMod (3 ^ m),
        Tao.taoSection5PayloadFreeCoefficient m S X *
          Tao.syracPMFMassVector m X) ≤
        ∑ X : ZMod (3 ^ m), R * Tao.syracPMFMassVector m X := by
      apply Finset.sum_le_sum
      intro X _hX
      exact mul_le_mul_of_nonneg_right (hcoeff X) ENNReal.toReal_nonneg
    _ = R * ∑ X : ZMod (3 ^ m), Tao.syracPMFMassVector m X := by
      rw [Finset.mul_sum]
    _ = R := by
      rw [show (∑ X : ZMod (3 ^ m), Tao.syracPMFMassVector m X) = 1 by
        exact Tao.pmf_sum_toReal (Tao.syracPMF m)]
      ring

/-- The strict exterior endpoint carrier has inverse-log-cube CommonZ mass
at the one common A5 reference level. -/
theorem eventually_ndA5ReferenceExteriorCommonZ_mem_Icc_log_rpow_neg_three
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      ∀ E : Set ℕ,
        Tao.taoSection5PayloadFreeCommonZ
            (ndA5ReferenceLevel B)
            (ndA5ReferenceExteriorEndpoints B C E) ∈
          Set.Icc (0 : ℝ) (Real.rpow (Real.log B) (-3 : ℝ)) := by
  filter_upwards
      [eventually_ndA5ReferenceExteriorCoefficient_le_log_rpow_neg_three
        C hC]
      with B hcoeff
  intro E
  constructor
  · exact ndA5ReferenceCommonZ_nonneg
      (ndA5ReferenceLevel B) (ndA5ReferenceExteriorEndpoints B C E)
  · apply taoSection5PayloadFreeCommonZ_le_of_coefficient_le
    exact hcoeff E

end
end ND
end Erdos1135
