/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QActualRecursion
import Erdos1135Predecessor.Tao.Renewal.QPrefixFactor

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection7HoldListQContinuationExpectation
    (P : ℕ) (epsilon : ℝ)
    (W : TaoSection7RenewalPoint -> Prop)
    (Q : TaoSection7RenewalPoint -> ℝ)
    (start : TaoSection7RenewalPoint) : ℝ :=
  ∑' pre : List TaoSection7RenewalPoint,
    (taoSection7HoldListPMF P pre).toReal *
      (taoSection7QPrefixFactor epsilon W start pre *
        Q (taoSection7RenewalPathPoint start pre P))

theorem taoSection7HoldListQContinuationExpectation_summable
    {P : ℕ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint -> Prop)
    {Q : TaoSection7RenewalPoint -> ℝ}
    (hQ : TaoSection7QBounded01 Q)
    (start : TaoSection7RenewalPoint) :
    Summable fun pre : List TaoSection7RenewalPoint =>
      (taoSection7HoldListPMF P pre).toReal *
        (taoSection7QPrefixFactor epsilon W start pre *
          Q (taoSection7RenewalPathPoint start pre P)) := by
  refine Summable.of_norm_bounded
    (taoSection7HoldListPMF_summable_toReal P) ?_
  intro pre
  have hmass : 0 ≤ (taoSection7HoldListPMF P pre).toReal :=
    ENNReal.toReal_nonneg
  have hpref0 := taoSection7QPrefixFactor_nonneg epsilon W start pre
  have hpref1 := taoSection7QPrefixFactor_le_one hepsilon W start pre
  have hq := hQ (taoSection7RenewalPathPoint start pre P)
  have hproduct0 :
      0 ≤ taoSection7QPrefixFactor epsilon W start pre *
        Q (taoSection7RenewalPathPoint start pre P) :=
    mul_nonneg hpref0 hq.1
  have hproduct1 :
      taoSection7QPrefixFactor epsilon W start pre *
          Q (taoSection7RenewalPathPoint start pre P) ≤
        1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hpref1 hq.2 hq.1 (by norm_num)
      _ = 1 := by norm_num
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hmass,
    abs_of_nonneg hproduct0]
  simpa using mul_le_mul_of_nonneg_left hproduct1 hmass

theorem taoSection7HoldPMF_mul_holdListPMF_mul_QContinuation_summable
    {P : ℕ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint -> Prop)
    {Q : TaoSection7RenewalPoint -> ℝ}
    (hQ : TaoSection7QBounded01 Q)
    (start : TaoSection7RenewalPoint) :
    Summable fun x : TaoSection7RenewalPoint ×
        List TaoSection7RenewalPoint =>
      (taoSection7HoldPMF x.1).toReal *
        (taoSection7HoldListPMF P x.2).toReal *
        (taoSection7QPrefixFactor epsilon W (start + x.1) x.2 *
          Q (taoSection7RenewalPathPoint (start + x.1) x.2 P)) := by
  have hmass := taoSection7HoldPMF_mul_holdListPMF_summable_toReal P
  refine Summable.of_norm_bounded hmass ?_
  intro x
  have hm0 :
      0 ≤ (taoSection7HoldPMF x.1).toReal *
        (taoSection7HoldListPMF P x.2).toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hpref0 :=
    taoSection7QPrefixFactor_nonneg epsilon W (start + x.1) x.2
  have hpref1 :=
    taoSection7QPrefixFactor_le_one hepsilon W (start + x.1) x.2
  have hq := hQ (taoSection7RenewalPathPoint (start + x.1) x.2 P)
  have hproduct0 :
      0 ≤ taoSection7QPrefixFactor epsilon W (start + x.1) x.2 *
        Q (taoSection7RenewalPathPoint (start + x.1) x.2 P) :=
    mul_nonneg hpref0 hq.1
  have hproduct1 :
      taoSection7QPrefixFactor epsilon W (start + x.1) x.2 *
          Q (taoSection7RenewalPathPoint (start + x.1) x.2 P) ≤
        1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hpref1 hq.2 hq.1 (by norm_num)
      _ = 1 := by norm_num
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm0,
    abs_of_nonneg hproduct0]
  simpa using mul_le_mul_of_nonneg_left hproduct1 hm0

theorem taoSection7HoldListQContinuationExpectation_succ
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (P : ℕ) (W : TaoSection7RenewalPoint -> Prop)
    {Q : TaoSection7RenewalPoint -> ℝ}
    (hQ : TaoSection7QBounded01 Q)
    (start : TaoSection7RenewalPoint) :
    taoSection7HoldListQContinuationExpectation
        (P + 1) epsilon W Q start =
      taoSection7QWhiteFactor epsilon W start *
        taoSection7HoldExpectationFull
          (fun h => taoSection7HoldListQContinuationExpectation
            P epsilon W Q (start + h)) := by
  unfold taoSection7HoldListQContinuationExpectation
  unfold taoSection7HoldExpectationFull
  have hnil :
      (taoSection7HoldListPMF (P + 1)
          ([] : List TaoSection7RenewalPoint)).toReal *
          (taoSection7QPrefixFactor epsilon W start [] *
            Q (taoSection7RenewalPathPoint start [] (P + 1))) = 0 := by
    rw [taoSection7HoldListPMF_succ_apply_nil]
    simp
  calc
    (∑' pre : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF (P + 1) pre).toReal *
          (taoSection7QPrefixFactor epsilon W start pre *
            Q (taoSection7RenewalPathPoint start pre (P + 1)))) =
        ∑' x : TaoSection7RenewalPoint ×
            List TaoSection7RenewalPoint,
          (taoSection7HoldListPMF (P + 1) (x.1 :: x.2)).toReal *
            (taoSection7QPrefixFactor epsilon W start (x.1 :: x.2) *
              Q (taoSection7RenewalPathPoint
                start (x.1 :: x.2) (P + 1))) := by
      exact taoSection7_tsum_list_eq_tsum_cons_of_nil_zero hnil
    _ = ∑' x : TaoSection7RenewalPoint ×
            List TaoSection7RenewalPoint,
          taoSection7QWhiteFactor epsilon W start *
            ((taoSection7HoldPMF x.1).toReal *
              (taoSection7HoldListPMF P x.2).toReal *
              (taoSection7QPrefixFactor epsilon W (start + x.1) x.2 *
                Q (taoSection7RenewalPathPoint
                  (start + x.1) x.2 P))) := by
      apply tsum_congr
      intro x
      rw [taoSection7HoldListPMF_succ_apply_cons,
        ENNReal.toReal_mul, taoSection7QPrefixFactor_cons,
        taoSection7RenewalPathPoint_cons_succ]
      ring
    _ = taoSection7QWhiteFactor epsilon W start *
          (∑' x : TaoSection7RenewalPoint ×
              List TaoSection7RenewalPoint,
            (taoSection7HoldPMF x.1).toReal *
              (taoSection7HoldListPMF P x.2).toReal *
              (taoSection7QPrefixFactor epsilon W (start + x.1) x.2 *
                Q (taoSection7RenewalPathPoint
                  (start + x.1) x.2 P))) := by
      rw [tsum_mul_left]
    _ = taoSection7QWhiteFactor epsilon W start *
          (∑' h : TaoSection7RenewalPoint,
            (taoSection7HoldPMF h).toReal *
              (∑' pre : List TaoSection7RenewalPoint,
                (taoSection7HoldListPMF P pre).toReal *
                  (taoSection7QPrefixFactor epsilon W (start + h) pre *
                    Q (taoSection7RenewalPathPoint
                      (start + h) pre P)))) := by
      congr 1
      have hsum :=
        taoSection7HoldPMF_mul_holdListPMF_mul_QContinuation_summable
          (P := P) hepsilon W hQ start
      have hfiber : ∀ h : TaoSection7RenewalPoint,
          Summable fun pre : List TaoSection7RenewalPoint =>
            (taoSection7HoldPMF h).toReal *
              (taoSection7HoldListPMF P pre).toReal *
              (taoSection7QPrefixFactor epsilon W (start + h) pre *
                Q (taoSection7RenewalPathPoint
                  (start + h) pre P)) := by
        intro h
        have hterm :=
          taoSection7HoldListQContinuationExpectation_summable
            (P := P) hepsilon W hQ (start + h)
        simpa [mul_assoc] using
          hterm.mul_left (taoSection7HoldPMF h).toReal
      rw [Summable.tsum_prod' hsum hfiber]
      apply tsum_congr
      intro h
      simpa [mul_assoc] using
        (tsum_mul_left
          (a := (taoSection7HoldPMF h).toReal)
          (f := fun pre : List TaoSection7RenewalPoint =>
            (taoSection7HoldListPMF P pre).toReal *
              (taoSection7QPrefixFactor epsilon W (start + h) pre *
                Q (taoSection7RenewalPathPoint (start + h) pre P))))
    _ = taoSection7QWhiteFactor epsilon W start *
          (∑' h : TaoSection7RenewalPoint,
            (taoSection7HoldPMF h).toReal *
              (∑' pre : List TaoSection7RenewalPoint,
                (taoSection7HoldListPMF P pre).toReal *
                  (taoSection7QPrefixFactor epsilon W (start + h) pre *
                    Q (taoSection7RenewalPathPoint
                      (start + h) pre P)))) := rfl

theorem taoSection7HoldListQContinuationExpectation_zero
    (epsilon : ℝ) (W : TaoSection7RenewalPoint -> Prop)
    (Q : TaoSection7RenewalPoint -> ℝ)
    (start : TaoSection7RenewalPoint) :
    taoSection7HoldListQContinuationExpectation
        0 epsilon W Q start = Q start := by
  unfold taoSection7HoldListQContinuationExpectation
  rw [tsum_eq_single ([] : List TaoSection7RenewalPoint)]
  · simp [taoSection7HoldListPMF_zero_apply_nil]
  · intro pre hpre
    cases pre with
    | nil => exact (hpre rfl).elim
    | cons h hs =>
        rw [taoSection7HoldListPMF_zero_apply_cons]
        simp

theorem taoSection7ActualQ_eq_holdListQContinuationExpectation
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint -> Prop}
    {Q : TaoSection7RenewalPoint -> ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (P : ℕ) (start : TaoSection7RenewalPoint) :
    Q start =
      taoSection7HoldListQContinuationExpectation
        P epsilon W Q start := by
  have hQ01 : TaoSection7QBounded01 Q := fun p =>
    ⟨taoSection7ActualQ_nonneg_of_finiteLimit hQ p,
      taoSection7ActualQ_le_one_of_finiteLimit hepsilon hQ p⟩
  induction P generalizing start with
  | zero =>
      exact
        (taoSection7HoldListQContinuationExpectation_zero
          epsilon W Q start).symm
  | succ P ih =>
      calc
        Q start = taoSection7QWhiteFactor epsilon W start *
            taoSection7HoldExpectationFull (fun h => Q (start + h)) := by
          simpa [taoSection7FullHoldQRecursionRHS] using
            (taoSection7ActualQ_fullHoldQRecursion_of_finiteLimit
              hepsilon hQ start)
        _ = taoSection7QWhiteFactor epsilon W start *
            taoSection7HoldExpectationFull
              (fun h => taoSection7HoldListQContinuationExpectation
                P epsilon W Q (start + h)) := by
          congr 1
          apply congrArg taoSection7HoldExpectationFull
          funext h
          exact ih (start + h)
        _ = taoSection7HoldListQContinuationExpectation
              (P + 1) epsilon W Q start :=
          (taoSection7HoldListQContinuationExpectation_succ
            hepsilon P W hQ01 start).symm

theorem taoSection7HoldListQContinuationExpectation_eq_master_of_le
    {P J : ℕ} (hPJ : P ≤ J)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint -> Prop)
    {Q : TaoSection7RenewalPoint -> ℝ}
    (hQ : TaoSection7QBounded01 Q)
    (start : TaoSection7RenewalPoint) :
    taoSection7HoldListQContinuationExpectation P epsilon W Q start =
      ∑' full : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF J full).toReal *
          (taoSection7QPrefixFactor epsilon W start (full.take P) *
            Q (taoSection7RenewalPathPoint start full P)) := by
  let F : List TaoSection7RenewalPoint -> ℝ := fun pre =>
    taoSection7QPrefixFactor epsilon W start pre *
      Q (taoSection7RenewalPathPoint start pre P)
  have hF0 : ∀ pre, 0 ≤ F pre := by
    intro pre
    exact mul_nonneg
      (taoSection7QPrefixFactor_nonneg epsilon W start pre)
      (hQ (taoSection7RenewalPathPoint start pre P)).1
  have hF1 : ∀ pre, F pre ≤ 1 := by
    intro pre
    have hpref1 :=
      taoSection7QPrefixFactor_le_one hepsilon W start pre
    have hq := hQ (taoSection7RenewalPathPoint start pre P)
    calc
      F pre ≤ 1 * 1 := by
        exact mul_le_mul hpref1 hq.2 hq.1 (by norm_num)
      _ = 1 := by norm_num
  have htransport :=
    pmf_map_weighted_tsum_toReal_eq_of_bounded01
      (taoSection7HoldListPMF J)
      (fun full : List TaoSection7RenewalPoint => full.take P)
      F hF0 hF1
  calc
    taoSection7HoldListQContinuationExpectation P epsilon W Q start =
        ∑' pre : List TaoSection7RenewalPoint,
          (taoSection7HoldListPMF P pre).toReal * F pre := rfl
    _ = ∑' pre : List TaoSection7RenewalPoint,
          (((taoSection7HoldListPMF J).map
            (fun full : List TaoSection7RenewalPoint => full.take P)) pre).toReal *
              F pre := by
        rw [taoSection7HoldListPMF_map_take_eq_of_le hPJ]
    _ = ∑' full : List TaoSection7RenewalPoint,
          (taoSection7HoldListPMF J full).toReal * F (full.take P) :=
        htransport.2.2
    _ = ∑' full : List TaoSection7RenewalPoint,
          (taoSection7HoldListPMF J full).toReal *
            (taoSection7QPrefixFactor epsilon W start (full.take P) *
              Q (taoSection7RenewalPathPoint start full P)) := by
        apply tsum_congr
        intro full
        dsimp [F]
        rw [show taoSection7RenewalPathPoint start (full.take P) P =
            taoSection7RenewalPathPoint start full P by
          exact taoSection7RenewalPathPoint_take_eq_of_le
            start full P P le_rfl]

theorem taoSection7ActualQ_eq_holdListQContinuationExpectation_master_of_le
    {P J : ℕ} (hPJ : P ≤ J)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint -> Prop}
    {Q : TaoSection7RenewalPoint -> ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (start : TaoSection7RenewalPoint) :
    Q start =
      ∑' full : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF J full).toReal *
          (taoSection7QPrefixFactor epsilon W start (full.take P) *
            Q (taoSection7RenewalPathPoint start full P)) := by
  have hQ01 : TaoSection7QBounded01 Q := fun p =>
    ⟨taoSection7ActualQ_nonneg_of_finiteLimit hQ p,
      taoSection7ActualQ_le_one_of_finiteLimit hepsilon hQ p⟩
  calc
    Q start = taoSection7HoldListQContinuationExpectation
        P epsilon W Q start :=
      taoSection7ActualQ_eq_holdListQContinuationExpectation
        hepsilon hQ P start
    _ = _ :=
      taoSection7HoldListQContinuationExpectation_eq_master_of_le
        hPJ hepsilon W hQ01 start

end

end Tao

end Erdos1135Predecessor
