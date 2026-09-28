import ActualReferencePassageLaw
import GeometricProbabilityBudget

open Filter
open scoped BigOperators Topology

namespace CollatzClockAudit
open Erdos1135.Tao

noncomputable def clockScale (M : ℝ) (i : ℕ) : ℝ := M ^ (taoAlpha ^ i)

@[simp] theorem clockScale_zero (M : ℝ) : clockScale M 0 = M := by
  simp [clockScale]

theorem clockScale_pos {M : ℝ} (hM : 0 < M) (i : ℕ) : 0 < clockScale M i :=
  Real.rpow_pos_of_pos hM _

theorem clockScale_log {M : ℝ} (hM : 0 < M) (i : ℕ) :
    Real.log (clockScale M i) = Real.log M * taoAlpha ^ i := by
  rw [clockScale, Real.log_rpow hM, mul_comm]

theorem clockScale_succ {M : ℝ} (hM : 0 ≤ M) (i : ℕ) :
    clockScale M (i + 1) = (clockScale M i) ^ taoAlpha := by
  rw [clockScale, pow_succ, Real.rpow_mul hM]
  rfl

theorem clockScale_mono {M : ℝ} (hM : 1 ≤ M) : Monotone (clockScale M) := by
  intro i j hij
  exact Real.rpow_le_rpow_of_exponent_le hM (pow_le_pow_right₀ taoAlpha_one_lt.le hij)

theorem le_clockScale {M : ℝ} (hM : 1 ≤ M) (i : ℕ) : M ≤ clockScale M i := by
  simpa only [clockScale_zero] using clockScale_mono hM (Nat.zero_le i)

theorem one_le_clockScale {M : ℝ} (hM : 1 ≤ M) (i : ℕ) : 1 ≤ clockScale M i :=
  hM.trans (le_clockScale hM i)

noncomputable def clockLadderActualLaw (M : ℝ) (hM : 1 ≤ M) (j i : ℕ)
    (hmassTop : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha))) :
    PMF {m : ℕ // m ≤ Nat.floor (clockScale M i)} :=
  syracusePassLocationRealFloorLaw (realClockSourceLo (clockScale M j) .alpha)
    (realClockSourceHi (clockScale M j) .alpha) (clockScale M i)
    (one_le_clockScale hM i) hmassTop

theorem clock_ladder_odd_source_map_eq_actual_law {M : ℝ} (hM : 1 ≤ M) (j i : ℕ)
    (hmassTop : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha))) :
    (oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) hmassTop).map
      (fun q => syracusePassLocationRealFloorOrOne (clockScale M i) q.1
        (one_le_clockScale hM i)) = clockLadderActualLaw M hM j i hmassTop := by
  rw [oddLogWindowOddNatPMF, PMF.map_comp]
  rfl

theorem clockLadderActualLaw_map_lower {M : ℝ} (hM : 1 ≤ M) (j i : ℕ)
    (hmassTop : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha))) :
    (clockLadderActualLaw M hM j (i + 1) hmassTop).map
      (fun u => syracusePassLocationRealFloorOrOne (clockScale M i) u.1
        (one_le_clockScale hM i)) = clockLadderActualLaw M hM j i hmassTop := by
  exact realFloorPassLocationLaw_map_lower hmassTop (one_le_clockScale hM i)
    (clockScale_mono hM (Nat.le_succ i)) (one_le_clockScale hM (i + 1))

theorem adjacent_reference_passage_tv_of_scale_eq {C c x y : ℝ}
    (facts : RealClockScaleFacts C c x) (hy : 1 ≤ y) (hxy : y = x ^ taoAlpha)
    (hmassNext : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo y .alpha) (realClockSourceHi y .alpha)))
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x .alpha) (realClockSourceHi x .alpha))) :
    taoTV ((realClockPassageLaw y hy .alpha hmassNext).map
      (fun u => syracusePassLocationRealFloorOrOne x u.1 facts.one_le_x))
      (realClockPassageLaw x facts.one_le_x .alpha hmass) ≤ C * (Real.log x) ^ (-c) := by
  subst y
  exact adjacent_reference_passage_tv facts hmassNext hmass

theorem clockScale_adjacent_reference_tv {M C c : ℝ} (hM : 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (i : ℕ) :
    taoTV
      ((realClockPassageLaw (clockScale M (i + 1)) (one_le_clockScale hM (i + 1))
        .alpha ((facts (i + 1)).mass_pos .alpha)).map
          (fun u => syracusePassLocationRealFloorOrOne (clockScale M i) u.1
            (one_le_clockScale hM i)))
      (realClockPassageLaw (clockScale M i) (one_le_clockScale hM i)
        .alpha ((facts i).mass_pos .alpha)) ≤ C * (Real.log (clockScale M i)) ^ (-c) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  exact adjacent_reference_passage_tv_of_scale_eq (facts i) (one_le_clockScale hM (i + 1))
    (clockScale_succ hM0 i) ((facts (i + 1)).mass_pos .alpha) ((facts i).mass_pos .alpha)

/-- The actual lower-barrier marginals from the top source are compared
with canonical reference passage laws by the checked adjacent-window TV
estimate and exact default-map composition. -/
theorem clock_ladder_actual_tv_le {M C c : ℝ} (hM : 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j i : ℕ) (hij : i ≤ j) :
    taoTV (clockLadderActualLaw M hM j i ((facts j).mass_pos .alpha))
      (realClockPassageLaw (clockScale M i) (one_le_clockScale hM i)
        .alpha ((facts i).mass_pos .alpha)) ≤
      ∑ r ∈ Finset.Ico i j, C * (Real.log (clockScale M r)) ^ (-c) := by
  let A := fun i => {m : ℕ // m ≤ Nat.floor (clockScale M i)}
  let f : ∀ i, A (i + 1) → A i := fun i u =>
    syracusePassLocationRealFloorOrOne (clockScale M i) u.1 (one_le_clockScale hM i)
  let μ : ∀ i, PMF (A i) := fun i =>
    clockLadderActualLaw M hM j i ((facts j).mass_pos .alpha)
  let ν : ∀ i, PMF (A i) := fun i =>
    realClockPassageLaw (clockScale M i) (one_le_clockScale hM i)
      .alpha ((facts i).mass_pos .alpha)
  apply finite_pmf_ladder_tv_le A f μ ν
    (fun r => C * (Real.log (clockScale M r)) ^ (-c)) j rfl _ _ i hij
  · intro k hk
    exact (clockLadderActualLaw_map_lower hM j k ((facts j).mass_pos .alpha)).symm
  · intro k hk
    exact clockScale_adjacent_reference_tv hM facts k

theorem clock_ladder_actual_event_le {M C c : ℝ} (hM : 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j i : ℕ) (hij : i ≤ j)
    (E : Set {m : ℕ // m ≤ Nat.floor (clockScale M i)}) {δ : ℝ}
    (hE : pmfProb (realClockPassageLaw (clockScale M i) (one_le_clockScale hM i)
      .alpha ((facts i).mass_pos .alpha)) E ≤ δ) :
    pmfProb (clockLadderActualLaw M hM j i ((facts j).mass_pos .alpha)) E ≤
      δ + ∑ r ∈ Finset.Ico i j, C * (Real.log (clockScale M r)) ^ (-c) := by
  have htv := clock_ladder_actual_tv_le hM facts j i hij
  have he := pmfProb_sub_taoTV_le_pmfProb
    (clockLadderActualLaw M hM j i ((facts j).mass_pos .alpha))
    (realClockPassageLaw (clockScale M i) (one_le_clockScale hM i)
      .alpha ((facts i).mass_pos .alpha)) E
  linarith

theorem clock_ladder_actual_tv_le_geometric {M C c : ℝ} (hM : 1 < M)
    (hC : 0 ≤ C) (hc : 0 < c)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j i : ℕ) (hij : i ≤ j) :
    taoTV (clockLadderActualLaw M hM.le j i ((facts j).mass_pos .alpha))
      (realClockPassageLaw (clockScale M i) (one_le_clockScale hM.le i)
        .alpha ((facts i).mass_pos .alpha)) ≤
      C / (1 - taoAlpha ^ (-c)) * (Real.log (clockScale M i)) ^ (-c) := by
  apply (clock_ladder_actual_tv_le hM.le facts j i hij).trans
  have hMp : 0 < M := by linarith
  simp only [clockScale_log hMp]
  exact geometric_decay_tail (Real.log_pos hM) taoAlpha_one_lt hc hC i j

theorem exists_clock_scale_uniform_cutoff :
    ∃ C c M₀ : ℝ, 0 ≤ C ∧ 0 < c ∧ 1 ≤ M₀ ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ i : ℕ, RealClockScaleFacts C c (clockScale M i) := by
  obtain ⟨C, c, hC, hc, hfacts⟩ := exists_eventually_real_clock_scale_facts
  obtain ⟨R, hR⟩ := eventually_atTop.1 hfacts
  refine ⟨C, c, max 1 R, hC, hc, le_max_left _ _, ?_⟩
  intro M hM i
  have hM1 : 1 ≤ M := (le_max_left _ _).trans hM
  exact hR _ ((le_max_right _ _).trans (hM.trans (le_clockScale hM1 i)))

end CollatzClockAudit
