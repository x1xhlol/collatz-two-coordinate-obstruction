import Erdos1135.Tao.Renewal.Lemma79R3Prefix
import Erdos1135.Tao.Renewal.Lemma79R2Pointwise
import Erdos1135.Tao.Renewal.Lemma79R2MasterTransport

/-!
# Lemma 7.9 Killed R=3 Pointwise Restart Envelope

This proof leaf separates the first-entry/first-exit weight from the restarted
`R-1` statistic.  A white first exit is counted once but is not asserted to be
a stopping transition.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every repaired cutoff statistic is nonnegative. -/
theorem lemma79CutoffTailMoment_nonneg
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C R : ℕ) :
    0 ≤ lemma79CutoffTailMoment pointAt family n xi epsilon C R := by
  unfold lemma79CutoffTailMoment
  split <;> positivity

/-- The restarted native statistic is exactly the statistic of the fresh
length-`J` block after identifying the canonical relative endpoint with the
global path endpoint. -/
theorem lemma79HoldPathCutoffTailMomentENN_restart_eq_freshTail
    {n J R k : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {origin endpoint : TaoSection7RenewalPoint}
    {full fresh : List TaoSection7RenewalPoint}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hendpoint :
      endpoint = taoSection7RenewalPathPoint origin full k)
    (hfresh : fresh = (full.drop k).take J) :
    ENNReal.ofReal
        (lemma79CutoffTailMoment
          (lemma79HoldPathRestartPointAt origin full k)
          family n xi epsilon J R) =
      lemma79HoldPathCutoffTailMomentENN
        endpoint family n xi epsilon J R fresh := by
  change
    lemma79HoldPathCutoffTailMomentENN
        (taoSection7RenewalPathPoint origin full k)
        family n xi epsilon J R (full.drop k) =
      lemma79HoldPathCutoffTailMomentENN
        endpoint family n xi epsilon J R fresh
  calc
    lemma79HoldPathCutoffTailMomentENN
        (taoSection7RenewalPathPoint origin full k)
        family n xi epsilon J R (full.drop k) =
        lemma79HoldPathCutoffTailMomentENN
          (taoSection7RenewalPathPoint origin full k)
          family n xi epsilon J R ((full.drop k).take J) :=
      lemma79HoldPathCutoffTailMomentENN_take hpair
    _ = _ := by rw [← hendpoint, ← hfresh]

/-- The exact recurrence is bounded by a two-valued first-exit weight times
the restarted `R-1` statistic. -/
theorem lemma79HoldPathCutoffTailMoment_le_firstExitWeight_mul_restart
    {n C p K R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hR : 2 ≤ R)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hlen : C ≤ full.length)
    (hexit : Lemma79FirstExitCertificate
      (lemma79HoldPathPointAt start full) old p (p + K))
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79HoldPathPointAt start full) family C
      ((p, old) :: rest)) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C R ≤
      Real.exp (-(p.pred : ℝ) + epsilon) *
        (if taoSection7SourceWhiteWCutoff n xi epsilon C
            ((lemma79HoldPathRestartPointAt start full p K).j : ℕ)
            (lemma79HoldPathRestartPointAt start full p K).l
          then Real.exp (-1) else 1) *
        lemma79CutoffTailMoment
          (lemma79HoldPathRestartPointAt start full (p + K))
          family n xi epsilon C (R - 1) := by
  let count :=
    lemma79CutoffWhiteCount
      (lemma79HoldPathRestartPointAt start full p)
      n xi epsilon C K
  have hrec :=
    lemma79HoldPathCutoffTailMoment_recurrence_firstEntry
      hR hpair hcover hlen hexit htrace
  rw [hrec]
  have hfuture0 :
      0 ≤ lemma79CutoffTailMoment
        (lemma79HoldPathRestartPointAt start full (p + K))
        family n xi epsilon C (R - 1) :=
    lemma79CutoffTailMoment_nonneg _ _ _ _ _ _ _
  by_cases hwhite :
      taoSection7SourceWhiteWCutoff n xi epsilon C
        ((lemma79HoldPathRestartPointAt start full p K).j : ℕ)
        (lemma79HoldPathRestartPointAt start full p K).l
  · have hK : 0 < K := by
      have := hexit.entry_lt_exit
      omega
    have hcount : 1 ≤ count :=
      lemma79CutoffWhiteCount_one_le_of_white_at hK hwhite
    have hcoeff :
        Real.exp
            (-((p.pred + count : ℕ) : ℝ) + epsilon) ≤
          Real.exp (-(p.pred : ℝ) + epsilon) * Real.exp (-1) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Nat.cast_add]
      have hcountReal : (1 : ℝ) ≤ (count : ℝ) := by exact_mod_cast hcount
      linarith
    rw [if_pos hwhite]
    exact mul_le_mul_of_nonneg_right hcoeff hfuture0
  · have hcoeff :
        Real.exp
            (-((p.pred + count : ℕ) : ℝ) + epsilon) ≤
          Real.exp (-(p.pred : ℝ) + epsilon) := by
      apply Real.exp_le_exp.mpr
      rw [Nat.cast_add]
      have hcount0 : (0 : ℝ) ≤ (count : ℝ) := Nat.cast_nonneg _
      linarith
    rw [if_neg hwhite, mul_one]
    exact mul_le_mul_of_nonneg_right hcoeff hfuture0

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
