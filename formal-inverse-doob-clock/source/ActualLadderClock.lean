import SourceLastVisitClock
import FiniteLadderClockEvent

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open Erdos1135.Tao CollatzClockAudit CollatzCanonical.NativeTao CollatzCanonical.RawOccupation

theorem validPrefix_finiteLadderClockEvent_of_source_good
    {n I : ℕ} {M : ℝ} {x : ℕ → ℕ} (hM : 1 ≤ M) (hnM : (n : ℝ) ≤ M)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hx : ValidPrefix n (ladderPrefixDepth n M I) x) (q : TaoOddNat)
    (hhit : ∃ A, iterate A q.1 = x (ladderPrefixDepth n M I))
    (hgood : q ∈ fixedLadderGoodEvent M hM I) :
    x ∈ finiteLadderClockEvent n M I := by
  obtain ⟨J, hIJ, hgood⟩ := hgood
  have hK0 : lastVisitDepthBound n ⌊M⌋₊ ≤ ladderPrefixDepth n M I := by
    simpa only [clockScale_zero] using
      (lastVisitDepthBound_le_ladderPrefixDepth (n := n) (M := M) (Nat.zero_le I))
  have hbottom := source_barrier_clock_add_lastVisit hx hnodd hnp q.2 hhit
    (zero_le_one.trans hM) hnM hK0
  intro i hi
  have hMi : M ≤ clockScale M i := le_clockScale hM i
  have hnonneg : 0 ≤ clockScale M i := (zero_le_one.trans hM).trans hMi
  have hKi := lastVisitDepthBound_le_ladderPrefixDepth (n := n) (M := M) hi
  have hfirst := source_first_passage_eq_reverse_lastVisit hx hnodd hnp q.2 hhit
    hnonneg (hnM.trans hMi) hKi
  have hfirst' : syracuseFirstHitAtMostReal (clockScale M i) q.1
      (actualBarrierTime (clockScale M i) q.1) := by
    rw [actualBarrierTime_eq_of_first_hit hfirst]
    exact hfirst
  obtain ⟨s, hs, he⟩ := global_clock_good_lower_segment hM J i (hi.trans hIJ) q hgood
  rw [real_pass_value_eq_of_first_hit (one_le_clockScale hM i) hfirst'] at hs
  have hcombined := real_first_hit_compose hMi hfirst' hs
  have htime := actualBarrierTime_eq_of_first_hit hcombined
  have htop := source_barrier_clock_add_lastVisit hx hnodd hnp q.2 hhit
    hnonneg (hnM.trans hMi) hKi
  have hdecomp : lastVisitIndex n ⌊clockScale M i⌋₊ x =
      s + lastVisitIndex n ⌊M⌋₊ x := by omega
  have hsle : s ≤ lastVisitIndex n ⌊clockScale M i⌋₊ x := by omega
  have hrem : (lastVisitIndex n ⌊clockScale M i⌋₊ x : ℝ) - s ≤
      lastVisitDepthBound n ⌊M⌋₊ := by
    rw [hdecomp, Nat.cast_add, add_sub_cancel_left]
    exact_mod_cast lastVisitIndex_le_bound n ⌊M⌋₊ x
  exact clock_error_with_bounded_remainder hsle hrem he

theorem actual_finite_ladder_clock_failure_probability
    {n I : ℕ} {M C c : ℝ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 < M) (hMe : Real.exp 1 ≤ M)
    (hnM : (n : ℝ) ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) :
    pathLaw n (finiteLadderClockEvent n M I)ᶜ ≤
      ENNReal.ofReal (2 * clockLadderFailureEnvelope C c M * taoAlpha / actualFirstHitDensity n) := by
  apply finiteLadderClock_failure_probability_of_source_good hn hu hnodd hnp hC hc hM hMe facts
  intro p q hp hhit hgood
  exact validPrefix_finiteLadderClockEvent_of_source_good hM.le hnM hnodd hnp hp q hhit hgood

theorem actual_reference_ladder_clock_ae {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n) {M : ℝ} (hM : 1 < M) :
    ∀ᵐ x ∂pathLaw n, x ∈ ladderClockLimitEvent n M := by
  obtain ⟨C, c, M0, hC, hc, _, hfacts⟩ := exists_clock_scale_uniform_cutoff
  let e : ℕ → ℝ := fun J =>
    2 * clockLadderFailureEnvelope C c (clockScale M J) * taoAlpha / actualFirstHitDensity n
  have he : Tendsto e atTop (𝓝 0) := by
    have h := (((clockLadderFailureEnvelope_tendsto_zero (C := C) hc).comp
      (clockScale_tendsto_atTop hM)).const_mul 2).mul_const taoAlpha
    simpa only [zero_mul, mul_zero, zero_div] using h.div_const (actualFirstHitDensity n)
  apply ae_ladderClockLimit_of_shifted_finite_errors hM e he
  filter_upwards [(clockScale_tendsto_atTop hM).eventually_ge_atTop M0,
    (clockScale_tendsto_atTop hM).eventually_ge_atTop (Real.exp 1),
    (clockScale_tendsto_atTop hM).eventually_ge_atTop (n : ℝ)] with J hJ hJe hnJ
  intro I
  exact actual_finite_ladder_clock_failure_probability hn hu hnodd hnp hC hc
    (hM.trans_le (le_clockScale hM.le J)) hJe hnJ (hfacts _ hJ)

#print axioms validPrefix_finiteLadderClockEvent_of_source_good
#print axioms actual_finite_ladder_clock_failure_probability
#print axioms actual_reference_ladder_clock_ae

end CollatzCylinderPacking.Arithmetic.InverseDoob
