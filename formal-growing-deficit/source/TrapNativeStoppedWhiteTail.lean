import TrapHoldPathCount
import TrapLaplaceEventBounds
import Erdos1135.Tao.Renewal.Lemma79CutoffStatistic

/-! Short-horizon few-white events charged to the full-cutoff stopping moment. -/

set_option autoImplicit false

open CollatzResearch
open scoped BigOperators

namespace Erdos1135.Tao

open TaoSection7Case3SourceStoppingRun
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

theorem trap_cutoff_count_le_short_hold_count
    (n C J t : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (ht : t ≤ full.length)
    (hj : ((taoSection7RenewalPathPoint start full t).j : ℕ) ≤ J) :
    lemma79CutoffWhiteCount (lemma79HoldPathPointAt start full) n xi epsilon C t ≤
      taoSection7QWhiteVisitCount
        (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J))
        start full := by
  classical
  apply le_trans _ (trap_positive_count_le_qWhiteVisitCount _ start full t ht)
  unfold lemma79CutoffWhiteCount
  apply Finset.sum_le_sum
  intro q hq
  have hqj : ((taoSection7RenewalPathPoint start full q).j : ℕ) ≤ J :=
    ((trap_holdPath_j_monotone start full) (Finset.mem_Icc.mp hq).2).trans hj
  by_cases hw : taoSection7SourceWhiteWCutoff n xi epsilon C
      ((lemma79HoldPathPointAt start full q).j : ℕ) (lemma79HoldPathPointAt start full q).l
  · have hwhite : taoSection7SourceWhiteWCutoff n xi epsilon J
        ((taoSection7RenewalPathPoint start full q).j : ℕ)
        (taoSection7RenewalPathPoint start full q).l :=
      (taoSection7SourceWhiteWCutoff_iff_of_le hqj).mpr
        (taoSection7SourceWhiteWCutoff_raw hw)
    simp [hw, taoSection7QWhiteIndicator, taoSection7SourceWhiteRenewal, hwhite]
  · simp [hw]

noncomputable def trapEarlyStopFewWhiteEvent
    (n C J R T : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (family : Set TaoSection7Triangle) (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint) : Prop :=
  full.length = C ∧ ∃ t,
    tR? (lemma79CutoffTrace (lemma79HoldPathPointAt start full) family C) R = some t ∧
      ((taoSection7RenewalPathPoint start full t).j : ℕ) ≤ J ∧
      trapHoldListWhiteCount
        (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J))
        (start :: full) ≤ T

theorem trap_early_stop_few_white_le_exp_of_native_moment
    (n C J R T : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (family : Set TaoSection7Triangle) (start : TaoSection7RenewalPoint)
    (hmoment :
      (∑' full : List TaoSection7RenewalPoint,
        taoSection7HoldListPMF C full * ENNReal.ofReal
          (lemma79CutoffTailMoment (lemma79HoldPathPointAt start full)
            family n xi epsilon C R)) ≤ ENNReal.ofReal (Real.exp epsilon)) :
    trapPMFEvent (taoSection7HoldListPMF C)
        (trapEarlyStopFewWhiteEvent n C J R T xi epsilon family start) ≤
      Real.exp ((T : ℝ) + epsilon - epsilon * (R : ℝ)) := by
  apply trap_pmf_event_le_exp_of_moment (taoSection7HoldListPMF C) _
    (fun full => ENNReal.ofReal
      (lemma79CutoffTailMoment (lemma79HoldPathPointAt start full)
        family n xi epsilon C R)) (T : ℝ) (epsilon * (R : ℝ)) epsilon _ hmoment
  intro full hfull
  obtain ⟨hlen, t, ht, hj, hwhite⟩ := hfull
  have htlen : t ≤ full.length := by
    have := lemma79CutoffTrace_tR_lt ht
    omega
  have hcount : lemma79CutoffWhiteCount (lemma79HoldPathPointAt start full)
      n xi epsilon C t ≤ T :=
    (trap_cutoff_count_le_short_hold_count n C J t xi epsilon start full htlen hj).trans hwhite
  have hcountR : (lemma79CutoffWhiteCount (lemma79HoldPathPointAt start full)
      n xi epsilon C t : ℝ) ≤ (T : ℝ) := by exact_mod_cast hcount
  apply ENNReal.ofReal_le_ofReal
  rw [lemma79CutoffTailMoment_eq_exp_of_tR? ht]
  apply Real.exp_le_exp.mpr
  linarith

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_cutoff_count_le_short_hold_count
#print axioms Erdos1135.Tao.trap_early_stop_few_white_le_exp_of_native_moment
