import BelowIntermediateStageClock

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open Erdos1135.Tao CollatzClockAudit

noncomputable def actualBarrierTime (M : ℝ) (q : ℕ) : ℕ := by
  classical
  exact if h : syracuseHitsAtMostReal q M then Nat.find h else 0

theorem actualBarrierTime_first_hit {M : ℝ} {q : ℕ}
    (h : syracuseHitsAtMostReal q M) :
    syracuseFirstHitAtMostReal M q (actualBarrierTime M q) := by
  classical
  rw [actualBarrierTime, dif_pos h]
  exact ⟨Nat.find_spec h, fun k hk => lt_of_not_ge (Nat.find_min h hk)⟩

theorem actualBarrierTime_eq_of_first_hit {M : ℝ} {q t : ℕ}
    (ht : syracuseFirstHitAtMostReal M q t) : actualBarrierTime M q = t := by
  have h := actualBarrierTime_first_hit (show syracuseHitsAtMostReal q M from ⟨t, ht.1⟩)
  exact le_antisymm (real_first_hit_time_mono le_rfl h ht)
    (real_first_hit_time_mono le_rfl ht h)

noncomputable def boundedBarrierRemainder (M : ℝ) (B : ℕ) : ℕ :=
  (Finset.range (B + 1)).sup (actualBarrierTime M)

theorem actualBarrierTime_le_boundedBarrierRemainder {M : ℝ} {B q : ℕ}
    (hq : q ≤ B) : actualBarrierTime M q ≤ boundedBarrierRemainder M B := by
  exact Finset.le_sup (f := actualBarrierTime M) (Finset.mem_range.mpr (by omega))

/-- Only successful lower passages appear. No termination assumption is
made for the other integers below B. -/
theorem real_first_hit_bounded_difference {M m : ℝ} {B q r t : ℕ}
    (hMm : M ≤ m) (hmB : m ≤ (B : ℝ))
    (hr : syracuseFirstHitAtMostReal m q r)
    (ht : syracuseFirstHitAtMostReal M q t) :
    t - r ≤ boundedBarrierRemainder M B := by
  have htail := real_first_hit_time_difference hMm hr ht
  have hland : (syracuse^[r]) q ≤ B := by exact_mod_cast hr.1.trans hmB
  rw [← actualBarrierTime_eq_of_first_hit htail]
  exact actualBarrierTime_le_boundedBarrierRemainder hland

theorem below_intermediate_clock_with_bottom_remainder
    {M m x e : ℝ} {B q r t s : ℕ}
    (hMm : M ≤ m) (hmx : m ≤ x) (hmB : m ≤ (B : ℝ))
    (hr : syracuseFirstHitAtMostReal x q r)
    (ht : syracuseFirstHitAtMostReal M q t)
    (hs : syracuseFirstHitAtMostReal m ((syracuse^[r]) q) s)
    (he : |(s : ℝ) - (Real.log x - Real.log m) / clockDrift| ≤ e) :
    |((t - r : ℕ) : ℝ) - Real.log x / clockDrift| ≤
      e + boundedBarrierRemainder M B + |Real.log m / clockDrift| := by
  have hm := real_first_hit_compose hmx hr hs
  have hmono := real_first_hit_time_mono hMm hm ht
  have hrem := real_first_hit_bounded_difference hMm hmB hm ht
  have hsk : s ≤ t - r := by omega
  have hsub : (t - r : ℕ) - s = t - (r + s) := by omega
  have hremR : ((t - r : ℕ) : ℝ) - s ≤ boundedBarrierRemainder M B := by
    rw [← Nat.cast_sub hsk, hsub]
    exact_mod_cast hrem
  exact clock_error_with_bounded_remainder hsk hremR he

theorem global_clock_good_intermediate_first_hit {m : ℝ} (hm : 1 ≤ m)
    (j n : ℕ) (hnj : n ≤ j) (q : TaoOddNat)
    (hq : q ∈ globalClockGoodEvent m hm j) :
    ∃ r, syracuseFirstHitAtMostReal (clockScale m n) q.1 r := by
  obtain ⟨r, hr, _⟩ := real_default_landing_stage_clock_from (clockScale m)
    (one_le_clockScale hm) (clockScale_mono hm) q.1 j
    (20 * (Real.log (clockScale m j)) ^ (3 / 5 : ℝ))
    (fun i => 40 * (Real.log (clockScale m (i + 1))) ^ (3 / 5 : ℝ))
    hq.1 hq.2.1 n hnj
  exact ⟨r, hr⟩

/-- The bottom remainder is bounded over a finite set of successful landings;
the main error depends on the intermediate barrier, not the remote source. -/
theorem global_clock_good_common_bottom_clock {M m : ℝ} (hm : 1 ≤ m)
    {B : ℕ} (hMm : M ≤ m) (hmB : m ≤ (B : ℝ))
    (j n : ℕ) (hnj : n ≤ j) (q : TaoOddNat)
    (hq : q ∈ globalClockGoodEvent m hm j)
    (hbottom : syracuseHitsAtMostReal q.1 M) :
    |((actualBarrierTime M q.1 - actualBarrierTime (clockScale m n) q.1 : ℕ) : ℝ) -
        Real.log (clockScale m n) / clockDrift| ≤
      globalClockErrorConstant * (Real.log (clockScale m n)) ^ (3 / 5 : ℝ) +
        boundedBarrierRemainder M B + |Real.log m / clockDrift| := by
  obtain ⟨r, hr⟩ := global_clock_good_intermediate_first_hit hm j n hnj q hq
  obtain ⟨s, hs, he⟩ := global_clock_good_lower_segment hm j n hnj q hq
  rw [real_pass_value_eq_of_first_hit (one_le_clockScale hm n) hr] at hs
  have h := below_intermediate_clock_with_bottom_remainder hMm (le_clockScale hm n)
    hmB hr (actualBarrierTime_first_hit hbottom) hs he
  simpa only [actualBarrierTime_eq_of_first_hit hr] using h

#print axioms real_first_hit_bounded_difference
#print axioms below_intermediate_clock_with_bottom_remainder
#print axioms global_clock_good_common_bottom_clock

end CollatzCanonical.RawOccupation
