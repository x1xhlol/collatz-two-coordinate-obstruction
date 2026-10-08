import RealPassageAtoms
import ClockScaleLadder
import GlobalClockGoodEvent
import LogarithmicRateComparison

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.NativeTao
open Erdos1135.Tao CollatzClockAudit CollatzPassageAtoms

theorem reference_passage_atom_probability {M D : ℝ} (hM : 1 ≤ M)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo M .alpha) (realClockSourceHi M .alpha)))
    (m : ℕ)
    (hsource : ((oddLogWindowOddNatPMF (realClockSourceLo M .alpha)
      (realClockSourceHi M .alpha) hmass).toOuterMeasure
      {q : TaoOddNat | (syracusePassLocationRealFloorOrOne M q.1 hM).val = m}).toReal ≤ D) :
    pmfProb (realClockPassageLaw M hM .alpha hmass) {u | u.val = m} ≤ D := by
  rw [pmfProb_eq_toOuterMeasure_toReal, ← real_odd_source_map_passage_eq,
    PMF.toOuterMeasure_map_apply]
  exact hsource

/-- Local atoms and the summable adjacent-law errors control every bottom
atom uniformly in the height of the source window. -/
theorem clock_ladder_bottom_atom_bound {M C c : ℝ} (hM : 1 < M)
    (hC : 0 ≤ C) (hc : 0 < c)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i))
    (hatom : ∀ hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo M .alpha) (realClockSourceHi M .alpha)),
      ∀ hx : 1 ≤ M, ∀ m : ℕ,
      ((oddLogWindowOddNatPMF (realClockSourceLo M .alpha)
        (realClockSourceHi M .alpha) hmass).toOuterMeasure
        {q : TaoOddNat | (syracusePassLocationRealFloorOrOne M q.1 hx).val = m}).toReal ≤
          200000 * M ^ (-(1 / 12800000 : ℝ)))
    (j m : ℕ) :
    ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) ((facts j).mass_pos .alpha)).toOuterMeasure
      {q : TaoOddNat | (syracusePassLocationRealFloorOrOne M q.1 hM.le).val = m}).toReal ≤
      200000 * M ^ (-(1 / 12800000 : ℝ)) +
        C / (1 - taoAlpha ^ (-c)) * (Real.log M) ^ (-c) := by
  have hatom0 : ∀ hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo (clockScale M 0) .alpha)
        (realClockSourceHi (clockScale M 0) .alpha)),
      ∀ hx : 1 ≤ clockScale M 0, ∀ m : ℕ,
      ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M 0) .alpha)
        (realClockSourceHi (clockScale M 0) .alpha) hmass).toOuterMeasure
        {q : TaoOddNat | (syracusePassLocationRealFloorOrOne (clockScale M 0) q.1 hx).val = m}).toReal ≤
          200000 * (clockScale M 0) ^ (-(1 / 12800000 : ℝ)) := by
    intro hmass hx m
    have hp := hatom (by simpa only [clockScale_zero] using hmass) hM.le m
    simpa only [real_pass_value_congr hx hM.le (clockScale_zero M), clockScale_zero] using hp
  have href := reference_passage_atom_probability (facts 0).one_le_x
    ((facts 0).mass_pos .alpha) m (hatom0 _ _ m)
  have h := clock_ladder_actual_event_le hM.le facts j 0 (Nat.zero_le j)
    {u | u.val = m} href
  rw [pmfProb_eq_toOuterMeasure_toReal,
    ← clock_ladder_odd_source_map_eq_actual_law hM.le j 0,
    PMF.toOuterMeasure_map_apply] at h
  have hs : (∑ r ∈ Finset.Ico 0 j, C * (Real.log (clockScale M r)) ^ (-c)) ≤
      C / (1 - taoAlpha ^ (-c)) * (Real.log M) ^ (-c) := by
    simp only [clockScale_log (by linarith : 0 < M)]
    exact geometric_decay_interval_le_bottom (Real.log_pos hM) taoAlpha_one_lt hc hC 0 j
  have hp : ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) ((facts j).mass_pos .alpha)).toOuterMeasure
      {q : TaoOddNat | (syracusePassLocationRealFloorOrOne M q.1 hM.le).val = m}).toReal ≤
      200000 * M ^ (-(1 / 12800000 : ℝ)) +
        ∑ r ∈ Finset.Ico 0 j, C * (Real.log (clockScale M r)) ^ (-c) := by
    simpa only [Set.preimage_setOf_eq, real_pass_value_congr _ hM.le (clockScale_zero M),
      clockScale_zero] using h
  exact hp.trans (add_le_add le_rfl hs)

/-- A single logarithmic rate controls all actual bottom passage atoms,
including the default-one atom, for all source-window heights. -/
theorem exists_uniform_bottom_passage_atom_log_rate :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ M : ℝ in atTop,
      ∃ hM : 1 < M, ∀ j : ℕ,
      ∃ hmass : 0 < logFinsetMass (oddLogWindow
        (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha)),
      ∀ m : ℕ,
      ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha) hmass).toOuterMeasure
        {q : TaoOddNat | (syracusePassLocationRealFloorOrOne M q.1 hM.le).val = m}).toReal ≤
          C * (Real.log M) ^ (-c) := by
  obtain ⟨C, c, M₀, hC, hc, _, hfacts⟩ := exists_clock_scale_uniform_cutoff
  let A := C / (1 - taoAlpha ^ (-c))
  have hA : 0 ≤ A := by
    apply div_nonneg hC
    have hp := Real.rpow_lt_one_of_one_lt_of_neg taoAlpha_one_lt (neg_neg_of_pos hc)
    linarith
  refine ⟨200000 + A, c, by linarith, hc, ?_⟩
  filter_upwards [eventually_ge_atTop M₀, eventually_gt_atTop (1 : ℝ),
    eventually_real_passage_atom_polynomial,
    eventually_negative_power_le_log_power (by norm_num : -(1 / 12800000 : ℝ) < 0) c]
    with M hM₀ hM hatom hpower
  refine ⟨hM, ?_⟩
  intro j
  let facts := hfacts M hM₀
  refine ⟨(facts j).mass_pos .alpha, ?_⟩
  intro m
  have h := clock_ladder_bottom_atom_bound hM hC hc facts (hatom .alpha) j m
  dsimp only [A] at h ⊢
  nlinarith

#print axioms clock_ladder_bottom_atom_bound
#print axioms exists_uniform_bottom_passage_atom_log_rate

end CollatzCanonical.NativeTao
