import TrapHoldCrossing

/-! Sublinear good-path errors force many stops in the original full canonical trace. -/

set_option autoImplicit false
open Filter
open scoped Topology

namespace Erdos1135.Tao
open TaoSection7Case3SourceStoppingRun
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

def TrapSublinearUpper (f : ℕ → ℝ) : Prop :=
  ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, f n ≤ gamma * (n : ℝ)

theorem trap_sublinear_upper_add {f g : ℕ → ℝ}
    (hf : TrapSublinearUpper f) (hg : TrapSublinearUpper g) :
    TrapSublinearUpper (fun n => f n + g n) := by
  intro gamma hgamma
  filter_upwards [hf (gamma / 2) (by positivity), hg (gamma / 2) (by positivity)] with n hfn hgn
  linarith

theorem trap_sublinear_upper_mul (a : ℝ) (ha : 0 ≤ a) {f : ℕ → ℝ}
    (hf : TrapSublinearUpper f) : TrapSublinearUpper (fun n => a * f n) := by
  intro gamma hgamma
  by_cases ha0 : a = 0
  · exact Eventually.of_forall fun n => by simp [ha0, mul_nonneg hgamma.le (Nat.cast_nonneg n)]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    filter_upwards [hf (gamma / a) (div_pos hgamma hapos)] with n hn
    calc
      a * f n ≤ a * (gamma / a * (n : ℝ)) := mul_le_mul_of_nonneg_left hn ha
      _ = gamma * (n : ℝ) := by field_simp

theorem trap_crossing_endpoint_target
    (J : ℕ) (pointAt : ℕ → TaoSection7Point) (M : ℕ) (D : ℝ)
    (hcross : J ≤ ((pointAt M).j : ℕ))
    (htube : |((pointAt M).l : ℝ) - 4 * (((pointAt M).j : ℕ) : ℝ)| ≤ D) :
    |((min (4 * (J : ℤ)) (pointAt M).l : ℤ) : ℝ) - 4 * (J : ℝ)| ≤ D ∧
      min (4 * (J : ℤ)) (pointAt M).l ≤ (pointAt M).l := by
  have hD : 0 ≤ D := (abs_nonneg _).trans htube
  have hj : (J : ℝ) ≤ (((pointAt M).j : ℕ) : ℝ) := by exact_mod_cast hcross
  refine ⟨?_, min_le_right _ _⟩
  by_cases htop : 4 * (J : ℤ) ≤ (pointAt M).l
  · rw [min_eq_left htop]
    simpa using hD
  · rw [min_eq_right (le_of_not_ge htop)]
    have hl : ((pointAt M).l : ℝ) ≤ 4 * (J : ℝ) := by exact_mod_cast (le_of_not_ge htop)
    rw [abs_of_nonpos (sub_nonpos.mpr hl)]
    have hlo := (abs_le.mp htube).1
    linarith

theorem eventually_good_hold_path_has_many_stops
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
        (family : Set TaoSection7Triangle) (hJ : J ≤ full.length),
      full.length = n / 2 →
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family →
      (start.j : ℕ) ≤ H n →
      (∀ q < trapHoldCrossing J start full hJ,
        ((taoSection7RenewalPathPoint start full (q + 1)).j : ℕ) ≤
          (taoSection7RenewalPathPoint start full q).j + H n) →
      (∀ q < trapHoldCrossing J start full hJ,
        ((taoSection7RenewalPathPoint start full (q + 1)).l : ℝ) ≤
          (taoSection7RenewalPathPoint start full q).l + V n) →
      (∀ q < trapHoldCrossing J start full hJ,
        |((taoSection7RenewalPathPoint start full q).l : ℝ) -
          4 * (((taoSection7RenewalPathPoint start full q).j : ℕ) : ℝ)| ≤ D n) →
      ∀ S : ℤ, |(S : ℝ) - 4 * (J : ℝ)| ≤ D n →
      S ≤ (taoSection7RenewalPathPoint start full (trapHoldCrossing J start full hJ)).l →
      taoSection7QWhiteVisitCount
        (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)) start full ≤ T →
      ∃ t, tR? (lemma79CutoffTrace (lemma79HoldPathPointAt start full) family (n / 2)) R = some t ∧
        ((taoSection7RenewalPathPoint start full t).j : ℕ) ≤ J := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htheta0 : 0 < theta := by nlinarith
  let eta := (2 * theta * Real.log 2 - Real.log 3) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  let w := fun n => 2 * (R : ℝ) * D n + (3 * (T : ℝ) + 2 * R + 1) * V n
  let loss := fun n => 4 * ((T : ℝ) + 1) * (H n : ℝ) + 2 * D n + ((T : ℝ) + 1) * V n
  have hw : TrapSublinearUpper w := trap_sublinear_upper_add
    (trap_sublinear_upper_mul _ (by positivity) hD)
    (trap_sublinear_upper_mul _ (by positivity) hV)
  have hloss : TrapSublinearUpper loss := trap_sublinear_upper_add
    (trap_sublinear_upper_add
      (trap_sublinear_upper_mul _ (by positivity) hH)
      (trap_sublinear_upper_mul _ (by positivity) hD))
    (trap_sublinear_upper_mul _ (by positivity) hV)
  have hroom := (trap_sublinear_upper_mul ((T : ℝ) + 1) (by positivity) hH)
    (theta / 2) (by positivity)
  obtain ⟨Nfamily, hNfamily⟩ := eventually_no_bounded_native_black_trap_families R
    hepsilon0 hepsilon heta w hw
  obtain ⟨Nloss, hNloss⟩ := eventually_atTop.mp (hloss (eta / Real.log 2) (div_pos heta hlog2))
  obtain ⟨Nroom, hNroom⟩ := eventually_atTop.mp hroom
  refine ⟨max Nfamily (max Nloss Nroom), ?_⟩
  intro n hn J hnJ hthetaJ xi hxi start full family hJ hlen hcover hstart
    hstepJ hstepL htube S hS hendpoint hcount
  have hnfamily : Nfamily ≤ n := (le_max_left _ _).trans hn
  have hnloss : Nloss ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnroom : Nroom ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  let M := trapHoldCrossing J start full hJ
  let pointAt := lemma79HoldPathPointAt start full
  have hJcover : J ≤ n / 2 := by omega
  have hMC : M ≤ n / 2 := by
    rw [← hlen]
    exact (trap_hold_crossing_le J start full hJ).trans hJ
  have hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ J :=
    fun q hq => trap_hold_before_crossing_le J start full hJ q hq
  have hroomNat : (start.j : ℕ) + H n * T ≤ J := by
    have hr := hNroom n hnroom
    have hprod : H n * (T + 1) ≤ J := by
      apply (Nat.cast_le (α := ℝ)).mp
      push_cast
      push_cast at hthetaJ
      nlinarith
    nlinarith
  have hTM : T < M := trap_hold_crossing_gt_threshold J T (H n) start full hJ hstepJ hroomNat
  have hsourceCount : trapSourceWhiteCount n xi epsilon pointAt M ≤ T := by
    rw [← trap_hold_cutoff_count_eq_source_count n J xi epsilon start full hJ]
    exact hcount
  let steps := lemma79CutoffTrace pointAt family (n / 2)
  by_cases hlong : R ≤ (trapTraceBefore M steps).length
  · exact trap_full_stop_horizontal_of_truncated_length hMC
      (lemma79CutoffTrace_spec pointAt family (n / 2)) hRpos hlong hdomain
  · obtain ⟨r, f, hlength, hfxi, herror, hspan⟩ :=
      exists_native_black_trap_family_of_shortened_canonical_trace
        n (n / 2) J M (n / 2) T (H n) xi epsilon (V n) (D n)
        pointAt family S hxi hnJ hJcover hMC (hV0 n) hcover hdomain hsourceCount hTM
        (trap_holdPath_j_monotone start full) hstepJ hstepL htube hS hendpoint
    change (trapTraceBefore M steps).length = r + 1 at hlength
    have hr : r < R := by omega
    have hrR : (r : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast (show r + 1 ≤ R by omega)
    have herrorW : nativeTrapFamilyError f ≤ w n := by
      have hd := mul_le_mul_of_nonneg_right hrR (hD0 n)
      have hv := mul_le_mul_of_nonneg_right (show (r : ℝ) ≤ R by linarith) (hV0 n)
      dsimp [w]
      nlinarith
    have hupper := hNfamily n hnfamily r hr f herrorW
    have hstartReal : ((start.j : ℕ) : ℝ) ≤ (H n : ℝ) := by exact_mod_cast hstart
    have hzero : (pointAt 0).j = start.j := by
      simp [pointAt, lemma79HoldPathPointAt, TaoSection7RenewalPoint.toPoint]
    rw [hzero] at hspan
    change 4 * (J : ℝ) - 4 * ((((start.j : ℕ) + H n * T : ℕ)) : ℝ) -
      2 * D n - V n * ((T : ℝ) + 1) ≤ nativeTrapFamilySpan f at hspan
    push_cast at hspan
    have hspanLoss : 4 * (J : ℝ) - loss n ≤ nativeTrapFamilySpan f := by
      dsimp [loss]
      nlinarith
    have hLossLog := mul_le_mul_of_nonneg_right (hNloss n hnloss) hlog2.le
    have hcancel : eta / Real.log 2 * (n : ℝ) * Real.log 2 = eta * (n : ℝ) := by field_simp
    rw [hcancel] at hLossLog
    have hspanLog := mul_le_mul_of_nonneg_right hspanLoss hlog2.le
    push_cast at hthetaJ
    have hJLog := mul_le_mul_of_nonneg_right hthetaJ hlog2.le
    dsimp [eta] at hupper hLossLog
    exfalso
    nlinarith

end Erdos1135.Tao

#print axioms Erdos1135.Tao.eventually_good_hold_path_has_many_stops
