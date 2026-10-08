import TrapGoodPathForcesStops

/-! A tube before the crossing and nonnegative vertical steps supply the endpoint. -/

set_option autoImplicit false
open Filter
open scoped Topology

namespace Erdos1135.Tao
open TaoSection7Case3SourceStoppingRun
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

structure TrapHoldGoodPath (J H : ℕ) (V D : ℝ)
    (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint) : Prop where
  start_le : (start.j : ℕ) ≤ H
  horizontal_step : ∀ q < full.length,
    ((taoSection7RenewalPathPoint start full (q + 1)).j : ℕ) ≤
      (taoSection7RenewalPathPoint start full q).j + H
  vertical_mono : ∀ q < full.length,
    (taoSection7RenewalPathPoint start full q).l ≤
      (taoSection7RenewalPathPoint start full (q + 1)).l
  vertical_step : ∀ q < full.length,
    ((taoSection7RenewalPathPoint start full (q + 1)).l : ℝ) ≤
      (taoSection7RenewalPathPoint start full q).l + V
  tube : ∀ q ≤ full.length, ((taoSection7RenewalPathPoint start full q).j : ℕ) ≤ J →
    |((taoSection7RenewalPathPoint start full q).l : ℝ) -
      4 * (((taoSection7RenewalPathPoint start full q).j : ℕ) : ℝ)| ≤ D

def trapHoldListGood (n J H : ℕ) (V D : ℝ) : List TaoSection7RenewalPoint → Prop
  | [] => False
  | start :: full => full.length = n / 2 ∧ TrapHoldGoodPath J H V D start full

theorem trap_endpoint_target_of_predecessor
    (J H : ℕ) (before after : TaoSection7Point) (D : ℝ)
    (hcross : J ≤ (after.j : ℕ)) (hstep : (after.j : ℕ) ≤ before.j + H)
    (htube : |(before.l : ℝ) - 4 * ((before.j : ℕ) : ℝ)| ≤ D)
    (hmono : before.l ≤ after.l) :
    |((min (4 * (J : ℤ)) after.l : ℤ) : ℝ) - 4 * (J : ℝ)| ≤ D + 4 * (H : ℝ) ∧
      min (4 * (J : ℤ)) after.l ≤ after.l := by
  have hD : 0 ≤ D := (abs_nonneg _).trans htube
  have hj : (J : ℝ) ≤ ((before.j : ℕ) : ℝ) + (H : ℝ) := by
    exact_mod_cast hcross.trans hstep
  have hl : (before.l : ℝ) ≤ (after.l : ℝ) := by exact_mod_cast hmono
  have hlo := (abs_le.mp htube).1
  refine ⟨?_, min_le_right _ _⟩
  by_cases htop : 4 * (J : ℤ) ≤ after.l
  · rw [min_eq_left htop]
    simpa using (show 0 ≤ D + 4 * (H : ℝ) by positivity)
  · rw [min_eq_right (le_of_not_ge htop)]
    have ha : (after.l : ℝ) ≤ 4 * (J : ℝ) := by exact_mod_cast (le_of_not_ge htop)
    rw [abs_of_nonpos (sub_nonpos.mpr ha)]
    linarith

theorem eventually_good_hold_path_has_many_stops_of_tube
    (R T : ℕ) (hRpos : 0 < R) (epsilon theta : ℝ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon < 1 / 4)
    (htheta : Real.log 3 < 2 * theta * Real.log 2)
    (H : ℕ → ℕ) (V D : ℕ → ℝ)
    (hV0 : ∀ n, 0 ≤ V n) (hD0 : ∀ n, 0 ≤ D n)
    (hH : TrapSublinearUpper (fun n => (H n : ℝ)))
    (hV : TrapSublinearUpper V) (hD : TrapSublinearUpper D) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ J : ℕ, 2 * J ≤ n → theta * (n : ℝ) ≤ (2 * J : ℕ) →
      ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
      ∀ (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
        (family : Set TaoSection7Triangle), full.length = n / 2 →
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family →
      TrapHoldGoodPath J (H n) (V n) (D n) start full →
      taoSection7QWhiteVisitCount
        (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)) start full ≤ T →
      ∃ t, tR? (lemma79CutoffTrace (lemma79HoldPathPointAt start full) family (n / 2)) R = some t ∧
        ((taoSection7RenewalPathPoint start full t).j : ℕ) ≤ J := by
  let widened := fun n => D n + 4 * (H n : ℝ)
  have hwidened0 : ∀ n, 0 ≤ widened n := by
    intro n
    exact add_nonneg (hD0 n) (by positivity)
  have hwidened : TrapSublinearUpper widened :=
    trap_sublinear_upper_add hD (trap_sublinear_upper_mul 4 (by norm_num) hH)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htheta0 : 0 < theta := by nlinarith
  obtain ⟨Nmain, hNmain⟩ := eventually_good_hold_path_has_many_stops R T hRpos
    epsilon theta hepsilon0 hepsilon htheta H V widened hV0 hwidened0 hH hV hwidened
  obtain ⟨Nroom, hNroom⟩ := eventually_atTop.mp (hH (theta / 2) (by positivity))
  refine ⟨max Nmain Nroom, ?_⟩
  intro n hn J hnJ hthetaJ xi hxi start full family hlen hcover hgood hcount
  have hnmain : Nmain ≤ n := (le_max_left _ _).trans hn
  have hnroom : Nroom ≤ n := (le_max_right _ _).trans hn
  have hJ : J ≤ full.length := by omega
  let M := trapHoldCrossing J start full hJ
  have hMfull : M ≤ full.length := (trap_hold_crossing_le J start full hJ).trans hJ
  have hHJ : H n ≤ J := by
    have hh := hNroom n hnroom
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hthetaJ
    linarith
  have hMpos : 0 < M := by
    by_contra hnot
    have hMzero : M = 0 := by omega
    have hcross := trap_hold_crossing_gt J start full hJ
    change J < ((taoSection7RenewalPathPoint start full M).j : ℕ) at hcross
    rw [hMzero, taoSection7RenewalPathPoint_zero] at hcross
    exact (not_lt_of_ge (hgood.start_le.trans hHJ)) hcross
  have hpred : M - 1 < M := by omega
  have hpredFull : M - 1 < full.length := hpred.trans_le hMfull
  have hsuc : M - 1 + 1 = M := by omega
  have hbeforeJ := trap_hold_before_crossing_le J start full hJ (M - 1) hpred
  have hstep := hgood.horizontal_step (M - 1) hpredFull
  have hmono := hgood.vertical_mono (M - 1) hpredFull
  rw [hsuc] at hstep hmono
  have htarget := trap_endpoint_target_of_predecessor J (H n)
    ((taoSection7RenewalPathPoint start full (M - 1)).toPoint)
    ((taoSection7RenewalPathPoint start full M).toPoint) (D n)
    (trap_hold_crossing_gt J start full hJ).le hstep
    (hgood.tube (M - 1) hpredFull.le hbeforeJ) hmono
  apply hNmain n hnmain J hnJ hthetaJ xi hxi start full family hJ hlen hcover hgood.start_le
    (fun q hq => hgood.horizontal_step q (hq.trans_le hMfull))
    (fun q hq => hgood.vertical_step q (hq.trans_le hMfull))
    (fun q hq => ?_)
    (min (4 * (J : ℤ)) (taoSection7RenewalPathPoint start full M).l)
    htarget.1 htarget.2 hcount
  have ht := hgood.tube q (hq.trans_le hMfull).le
    (trap_hold_before_crossing_le J start full hJ q hq)
  exact ht.trans (le_add_of_nonneg_right (by positivity))

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_endpoint_target_of_predecessor
#print axioms Erdos1135.Tao.eventually_good_hold_path_has_many_stops_of_tube
