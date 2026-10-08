import TrapHoldPathCount
import TrapCanonicalFewWhite
import Erdos1135.Tao.Renewal.Lemma79CanonicalTraceProjection

/-! Least horizontal crossing and exact white count on the literal Hold path. -/

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos1135.Tao
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

theorem trap_hold_crossing_exists
    (J : ℕ) (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hJ : J ≤ full.length) :
    ∃ q, J < ((taoSection7RenewalPathPoint start full q).j : ℕ) := by
  exact ⟨J, lemma79HoldPathPoint_j_gt_cutoff hJ le_rfl⟩

noncomputable def trapHoldCrossing
    (J : ℕ) (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hJ : J ≤ full.length) : ℕ :=
  Nat.find (trap_hold_crossing_exists J start full hJ)

theorem trap_hold_crossing_le
    (J : ℕ) (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hJ : J ≤ full.length) : trapHoldCrossing J start full hJ ≤ J := by
  exact Nat.find_min' _ (lemma79HoldPathPoint_j_gt_cutoff hJ le_rfl)

theorem trap_hold_crossing_gt
    (J : ℕ) (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hJ : J ≤ full.length) :
    J < ((taoSection7RenewalPathPoint start full (trapHoldCrossing J start full hJ)).j : ℕ) :=
  Nat.find_spec (trap_hold_crossing_exists J start full hJ)

theorem trap_hold_before_crossing_le
    (J : ℕ) (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hJ : J ≤ full.length) (q : ℕ) (hq : q < trapHoldCrossing J start full hJ) :
    ((taoSection7RenewalPathPoint start full q).j : ℕ) ≤ J := by
  exact Nat.le_of_not_gt (Nat.find_min (trap_hold_crossing_exists J start full hJ) hq)

theorem trap_hold_crossing_le_iff
    (J : ℕ) (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hJ : J ≤ full.length) (q : ℕ) :
    trapHoldCrossing J start full hJ ≤ q ↔
      J < ((taoSection7RenewalPathPoint start full q).j : ℕ) := by
  constructor
  · intro hq
    exact (trap_hold_crossing_gt J start full hJ).trans_le
      (trap_holdPath_j_monotone start full hq)
  · intro hq
    exact Nat.find_min' _ hq

theorem trap_source_white_renewal_cutoff_iff
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (p : TaoSection7RenewalPoint) :
    taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J) p ↔
      (p.j : ℕ) ≤ J ∧ taoSection7SourceWhitePoint n xi epsilon p.toPoint := by
  constructor
  · rintro ⟨hp, hJ, hwhite⟩
    exact ⟨hJ, hwhite⟩
  · rintro ⟨hJ, hwhite⟩
    exact ⟨p.j.2, hJ, hwhite⟩

theorem trap_hold_cutoff_count_eq_source_count
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hJ : J ≤ full.length) :
    taoSection7QWhiteVisitCount
        (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)) start full =
      trapSourceWhiteCount n xi epsilon (lemma79HoldPathPointAt start full)
        (trapHoldCrossing J start full hJ) := by
  classical
  let M := trapHoldCrossing J start full hJ
  let W := taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)
  have hM : M ≤ full.length := (trap_hold_crossing_le J start full hJ).trans hJ
  rw [trap_qWhiteVisitCount_eq_sum_range]
  change (∑ q ∈ Finset.range (full.length + 1),
      taoSection7QWhiteIndicator W (taoSection7RenewalPathPoint start full q)) = _
  calc
    _ = ∑ q ∈ Finset.range M,
        taoSection7QWhiteIndicator W (taoSection7RenewalPathPoint start full q) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : M ≤ full.length + 1))
      intro q _ hq
      have hMq : M ≤ q := by simpa using hq
      have hjq := (trap_hold_crossing_le_iff J start full hJ q).mp hMq
      have hnot : ¬ W (taoSection7RenewalPathPoint start full q) := by
        intro hw
        have hle := (trap_source_white_renewal_cutoff_iff n J xi epsilon _).mp hw
        omega
      simp [taoSection7QWhiteIndicator, hnot]
    _ = ∑ q ∈ Finset.range M,
        if taoSection7SourceWhitePoint n xi epsilon (lemma79HoldPathPointAt start full q)
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hle := trap_hold_before_crossing_le J start full hJ q (Finset.mem_range.mp hq)
      have hiff : W (taoSection7RenewalPathPoint start full q) ↔
          taoSection7SourceWhitePoint n xi epsilon (lemma79HoldPathPointAt start full q) := by
        simpa only [hle, true_and, lemma79HoldPathPointAt] using
          trap_source_white_renewal_cutoff_iff n J xi epsilon
            (taoSection7RenewalPathPoint start full q)
      simp only [taoSection7QWhiteIndicator, hiff]
    _ = trapSourceWhiteCount n xi epsilon (lemma79HoldPathPointAt start full) M := by
      simp [trapSourceWhiteCount, CollatzResearch.trapWhiteCount, Finset.sum_boole]

theorem trap_hold_crossing_gt_threshold
    (J T H : ℕ) (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hJ : J ≤ full.length)
    (hstep : ∀ q < trapHoldCrossing J start full hJ,
      ((taoSection7RenewalPathPoint start full (q + 1)).j : ℕ) ≤
        (taoSection7RenewalPathPoint start full q).j + H)
    (hroom : (start.j : ℕ) + H * T ≤ J) : T < trapHoldCrossing J start full hJ := by
  have hwalk := CollatzResearch.trap_nat_walk_le
    (fun q => ((taoSection7RenewalPathPoint start full q).j : ℕ))
    H (trapHoldCrossing J start full hJ) hstep
  have hcross := trap_hold_crossing_gt J start full hJ
  simp only [taoSection7RenewalPathPoint_zero] at hwalk
  by_contra hnot
  have hmul := Nat.mul_le_mul_left H (Nat.le_of_not_gt hnot)
  omega

theorem trap_shortened_hold_trace_nonempty
    (n coverJ J C T H : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (hJ : J ≤ full.length)
    (hlen : full.length = C) (hJcover : J ≤ coverJ)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon coverJ) family)
    (hcount : taoSection7QWhiteVisitCount
      (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)) start full ≤ T)
    (hstep : ∀ q < trapHoldCrossing J start full hJ,
      ((taoSection7RenewalPathPoint start full (q + 1)).j : ℕ) ≤
        (taoSection7RenewalPathPoint start full q).j + H)
    (hroom : (start.j : ℕ) + H * T ≤ J) :
    trapTraceBefore (trapHoldCrossing J start full hJ)
      (lemma79CutoffTrace (lemma79HoldPathPointAt start full) family C) ≠ [] := by
  let M := trapHoldCrossing J start full hJ
  have hMC : M ≤ C := by
    rw [← hlen]
    exact (trap_hold_crossing_le J start full hJ).trans hJ
  have hTM : T < M := trap_hold_crossing_gt_threshold J T H start full hJ hstep hroom
  rw [trap_hold_cutoff_count_eq_source_count n J xi epsilon start full hJ] at hcount
  exact trap_bounded_inclusive_nonempty_of_few_white n coverJ M xi epsilon
    (lemma79HoldPathPointAt start full) family _ hcover
    (fun q hq => (trap_hold_before_crossing_le J start full hJ q hq).trans hJcover)
    (hcount.trans_lt hTM)
    (trap_bounded_inclusive_trace_before hMC
      (lemma79CutoffTrace_spec (lemma79HoldPathPointAt start full) family C))

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_hold_cutoff_count_eq_source_count
#print axioms Erdos1135.Tao.trap_hold_crossing_gt_threshold
#print axioms Erdos1135.Tao.trap_shortened_hold_trace_nonempty
