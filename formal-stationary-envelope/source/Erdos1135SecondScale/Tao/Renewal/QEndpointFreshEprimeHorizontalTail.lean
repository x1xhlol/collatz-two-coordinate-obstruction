/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.HoldListHorizontalTail
import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshEprimeMasterWidth
import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshEprimeFourTail

/-!
# Canonical Eprime Horizontal Tail Absorption

This leaf converts both horizontal tails in Tao's `(7.61)` into the scales
used by the native four-marginal assembly.  The first-passage term is absorbed
uniformly by the master source width, while the fresh term uses the existing
iid Hold-list MGF through an exact natural-ceiling adapter.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Exponential decay at the source one-fifth scale is uniformly absorbed by
the polynomial `X / sMin` bucket under the master width. -/
theorem lemma79_threeFifthsTail_le_scale
    {fpGap : ℕ} {K c sMin X : ℝ}
    (hK : 0 < K) (hc : 0 < c)
    (hsMin : 1 ≤ sMin) (hX : 1 ≤ X)
    (hmaster : sMin ^ 2 ≤ 100 * (fpGap : ℝ)) :
    K * Real.exp (-c * (fpGap : ℝ) ^ (1 / 5 : ℝ)) ≤
      (270 * K / c ^ 3) * X / sMin := by
  have hsMin_pos : 0 < sMin := lt_of_lt_of_le zero_lt_one hsMin
  have hsMin_nonneg : 0 ≤ sMin := hsMin_pos.le
  have hgap_pos : 0 < (fpGap : ℝ) := by
    by_contra hnot
    have hgap_zero : (fpGap : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hnot) (Nat.cast_nonneg fpGap)
    rw [hgap_zero, mul_zero] at hmaster
    nlinarith [sq_pos_of_pos hsMin_pos]
  have hgapNat : 1 ≤ fpGap := by
    have : 0 < fpGap := by exact_mod_cast hgap_pos
    omega
  have hgap_one : (1 : ℝ) ≤ fpGap := by
    exact_mod_cast hgapNat
  let y : ℝ := (fpGap : ℝ) ^ (1 / 5 : ℝ)
  have hy_one : 1 ≤ y := by
    dsimp [y]
    exact Real.one_le_rpow hgap_one (by norm_num)
  have hy_nonneg : 0 ≤ y := le_trans zero_le_one hy_one
  have hy5 : y ^ 5 = (fpGap : ℝ) := by
    dsimp [y]
    calc
      ((fpGap : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) =
          ((fpGap : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℝ) :=
        (Real.rpow_natCast ((fpGap : ℝ) ^ (1 / 5 : ℝ)) 5).symm
      _ = (fpGap : ℝ) ^ ((1 / 5 : ℝ) * 5) :=
        (Real.rpow_mul (Nat.cast_nonneg fpGap) (1 / 5 : ℝ) 5).symm
      _ = (fpGap : ℝ) ^ (1 : ℝ) := by norm_num
      _ = (fpGap : ℝ) := by simp
  have hy5_nonneg : 0 ≤ y ^ 5 := pow_nonneg hy_nonneg 5
  have hy5_le6 : y ^ 5 ≤ y ^ 6 := by
    calc
      y ^ 5 ≤ y ^ 5 * y := by
        simpa using mul_le_mul_of_nonneg_left hy_one hy5_nonneg
      _ = y ^ 6 := by ring
  have hsMin_sq_le :
      sMin ^ 2 ≤ (10 * y ^ 3) ^ 2 := by
    calc
      sMin ^ 2 ≤ 100 * (fpGap : ℝ) := hmaster
      _ = 100 * y ^ 5 := by rw [hy5]
      _ ≤ 100 * y ^ 6 :=
        mul_le_mul_of_nonneg_left hy5_le6 (by norm_num)
      _ = (10 * y ^ 3) ^ 2 := by ring
  have hsMin_le : sMin ≤ 10 * y ^ 3 :=
    (sq_le_sq₀ hsMin_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg hy_nonneg 3))).1
      hsMin_sq_le
  have hu_nonneg : 0 ≤ c * y := mul_nonneg hc.le hy_nonneg
  have hbase_nonneg :
      0 ≤ (c * y / 3) * Real.exp (-(c * y / 3)) :=
    mul_nonneg (div_nonneg hu_nonneg (by norm_num)) (Real.exp_pos _).le
  have hmul :=
    Real.mul_exp_neg_le_exp_neg_one (c * y / 3)
  have hcube :
      ((c * y / 3) * Real.exp (-(c * y / 3))) ^ 3 ≤
        Real.exp (-1) ^ 3 :=
    pow_le_pow_left₀ hbase_nonneg hmul 3
  have hexpCube :
      Real.exp (-(c * y / 3)) ^ 3 =
        Real.exp (-(c * y)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have huCube :
      (c * y) ^ 3 * Real.exp (-(c * y)) ≤ 27 := by
    calc
      (c * y) ^ 3 * Real.exp (-(c * y)) =
          (c * y) ^ 3 * (Real.exp (-(c * y / 3)) ^ 3) := by
        rw [hexpCube]
      _ =
          27 *
            (((c * y / 3) * Real.exp (-(c * y / 3))) ^ 3) := by
        rw [mul_pow]
        ring
      _ ≤ 27 * (Real.exp (-1) ^ 3) :=
        mul_le_mul_of_nonneg_left hcube (by norm_num)
      _ = 27 * Real.exp (-3) := by
        rw [← Real.exp_nat_mul]
        congr 2
        ring
      _ ≤ 27 := by
        have hexp_le : Real.exp (-3) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by norm_num)
        nlinarith
  have hdenom : 0 < c ^ 3 * sMin :=
    mul_pos (pow_pos hc 3) hsMin_pos
  have hrhs :
      (270 * K / c ^ 3) * X / sMin =
        (270 * K * X) / (c ^ 3 * sMin) := by
    field_simp [hc.ne', hsMin_pos.ne']
  rw [hrhs]
  apply (le_div_iff₀ hdenom).2
  change
    (K * Real.exp (-c * (fpGap : ℝ) ^ (1 / 5 : ℝ))) *
        (c ^ 3 * sMin) ≤
      270 * K * X
  have hcross :
      (K * Real.exp (-(c * y))) * (c ^ 3 * sMin) ≤
        270 * K * X := by
    calc
      (K * Real.exp (-(c * y))) * (c ^ 3 * sMin) =
          (K * Real.exp (-(c * y)) * c ^ 3) * sMin := by ring
      _ ≤ (K * Real.exp (-(c * y)) * c ^ 3) * (10 * y ^ 3) :=
        mul_le_mul_of_nonneg_left hsMin_le
          (mul_nonneg
            (mul_nonneg hK.le (Real.exp_pos _).le)
            (pow_nonneg hc.le 3))
      _ = 10 * K * ((c * y) ^ 3 * Real.exp (-(c * y))) := by
        ring
      _ ≤ 10 * K * 27 :=
        mul_le_mul_of_nonneg_left huCube (mul_nonneg (by norm_num) hK.le)
      _ ≤ 270 * K * X := by
        nlinarith
  simpa [y] using hcross

/-- The literal real-threshold fresh horizontal event is exactly controlled
by the existing natural-cutoff Hold-list tail.  No sign assumption on `t`
is needed. -/
theorem lemma79CanonicalFreshHorizontalTailEvent_outerMeasure_le
    (P : ℕ) (t : ℝ) :
    (taoSection7HoldListPMF P).toOuterMeasure
        (lemma79CanonicalFreshHorizontalTailEvent P t) ≤
      ENNReal.ofReal
        (Real.exp ((P : ℝ) / 2 - t / 16)) := by
  let mTail : ℕ := 10 * ⌈t⌉₊
  have hEvent :
      lemma79CanonicalFreshHorizontalTailEvent P t =
        {fresh |
          mTail ≤
            10 * lemma77HoldPrefixHorizontalDelta P fresh} := by
    ext fresh
    change
      t ≤ (lemma77HoldPrefixHorizontalDelta P fresh : ℝ) ↔
        mTail ≤ 10 * lemma77HoldPrefixHorizontalDelta P fresh
    dsimp [mTail]
    rw [Nat.mul_le_mul_left_iff (by norm_num : 0 < 10)]
    exact
      (Nat.ceil_le
        (a := t)
        (n := lemma77HoldPrefixHorizontalDelta P fresh)).symm
  rw [hEvent]
  calc
    (taoSection7HoldListPMF P).toOuterMeasure
        {fresh |
          mTail ≤ 10 * lemma77HoldPrefixHorizontalDelta P fresh} ≤
        ENNReal.ofReal
          (Real.exp
            ((P : ℝ) / 2 - (mTail : ℝ) / 160)) :=
      taoSection7HoldListPMF_horizontalTail_outerMeasure_le P mTail
    _ ≤ ENNReal.ofReal
          (Real.exp ((P : ℝ) / 2 - t / 16)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have htceil : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
      dsimp [mTail]
      push_cast
      nlinarith

/-- In the nontrivial large branch, the fresh horizontal tail has the
uniform rate `7/64` at Tao's scale `Aweight²(P+1)`. -/
theorem lemma79CanonicalFreshHorizontalTailEvent_outerMeasure_le_sevenSixtyFour
    (P Aweight fpGap : ℕ) (sMin : ℝ)
    (hAweight : 8 ≤ Aweight)
    (hlarge :
      30 * ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)) ≤ sMin)
    (hthreeFifths :
      sMin / 16 ≤ (fpGap : ℝ) ^ (3 / 5 : ℝ)) :
    (taoSection7HoldListPMF P).toOuterMeasure
        (lemma79CanonicalFreshHorizontalTailEvent
          P ((fpGap : ℝ) ^ (3 / 5 : ℝ))) ≤
      ENNReal.ofReal
        (Real.exp
          (-(7 / 64 : ℝ) *
            ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)))) := by
  let X : ℝ := (Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)
  let t : ℝ := (fpGap : ℝ) ^ (3 / 5 : ℝ)
  have hAreal : (8 : ℝ) ≤ Aweight := by
    exact_mod_cast hAweight
  have hAsq : (64 : ℝ) ≤ (Aweight : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((Aweight : ℝ) - 8)]
  have hXlower : 64 * ((P : ℝ) + 1) ≤ X := by
    dsimp [X]
    exact mul_le_mul_of_nonneg_right hAsq (by positivity)
  have hpHalf : (P : ℝ) / 2 ≤ X / 128 := by
    nlinarith
  have htLower : 15 * X / 128 ≤ t / 16 := by
    dsimp [X, t] at hlarge hthreeFifths ⊢
    nlinarith
  have hexponent :
      (P : ℝ) / 2 - t / 16 ≤ -(7 / 64 : ℝ) * X := by
    nlinarith
  calc
    (taoSection7HoldListPMF P).toOuterMeasure
        (lemma79CanonicalFreshHorizontalTailEvent P t) ≤
        ENNReal.ofReal
          (Real.exp ((P : ℝ) / 2 - t / 16)) :=
      lemma79CanonicalFreshHorizontalTailEvent_outerMeasure_le P t
    _ ≤ ENNReal.ofReal
          (Real.exp (-(7 / 64 : ℝ) * X)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)
    _ = ENNReal.ofReal
          (Real.exp
            (-(7 / 64 : ℝ) *
              ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)))) := by
      rfl

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
