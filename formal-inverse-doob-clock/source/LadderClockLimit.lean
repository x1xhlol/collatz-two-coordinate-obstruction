import ActualLastVisitLaw
import BoundedBottomPassageClock
import NativeTargetClockWindows
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open Erdos1135.Tao CollatzClockAudit CollatzCanonical.NativeTao

noncomputable def ladderLastClock (n : ℕ) (M : ℝ) (x : ℕ → ℕ) (j : ℕ) : ℕ :=
  lastVisitIndex n ⌊clockScale M j⌋₊ x

noncomputable def ladderLastClockError (n : ℕ) (M : ℝ) (j : ℕ) : ℝ :=
  globalClockErrorConstant * (Real.log (clockScale M j)) ^ (3 / 5 : ℝ) +
    lastVisitDepthBound n ⌊M⌋₊ + |Real.log M / clockDrift|

def finiteLadderClockEvent (n : ℕ) (M : ℝ) (I : ℕ) : Set (ℕ → ℕ) :=
  {x | ∀ j ≤ I,
    |(ladderLastClock n M x j : ℝ) - Real.log (clockScale M j) / clockDrift| ≤
      ladderLastClockError n M j}

def ladderClockLimitEvent (n : ℕ) (M : ℝ) : Set (ℕ → ℕ) :=
  {x | Tendsto (fun j => (ladderLastClock n M x j : ℝ) /
      Real.log (clockScale M j)) atTop (𝓝 (1 / clockDrift))}

theorem measurableSet_ladderClockLimitEvent (n : ℕ) (M : ℝ) :
    MeasurableSet (ladderClockLimitEvent n M) := by
  apply measurableSet_tendsto
  intro j
  exact ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_lastVisitIndex n ⌊clockScale M j⌋₊)).div_const _

theorem clockScale_compose {M : ℝ} (hM : 0 ≤ M) (J j : ℕ) :
    clockScale (clockScale M J) j = clockScale M (j + J) := by
  unfold clockScale
  rw [← Real.rpow_mul hM, pow_add, mul_comm (taoAlpha ^ J)]

theorem ladderClockLimitEvent_shift {M : ℝ} (hM : 0 ≤ M) (n J : ℕ) :
    ladderClockLimitEvent n (clockScale M J) = ladderClockLimitEvent n M := by
  ext x
  simp only [ladderClockLimitEvent, Set.mem_setOf_eq, ladderLastClock,
    clockScale_compose hM]
  exact tendsto_add_atTop_iff_nat (f := fun j =>
    (lastVisitIndex n ⌊clockScale M j⌋₊ x : ℝ) / Real.log (clockScale M j)) J

theorem ladderLastClockError_normalized_tendsto_zero {M : ℝ} (hM : 1 < M) (n : ℕ) :
    Tendsto (fun j => ladderLastClockError n M j / Real.log (clockScale M j))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun j => Real.log (clockScale M j)) atTop atTop :=
    Real.tendsto_log_atTop.comp (clockScale_tendsto_atTop hM)
  have hp : Tendsto (fun j => (Real.log (clockScale M j)) ^ (3 / 5 : ℝ) /
      Real.log (clockScale M j)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp hlog
    apply h.congr'
    exact Eventually.of_forall (fun j => by
      have hj : 0 < Real.log (clockScale M j) :=
        Real.log_pos (hM.trans_le (le_clockScale hM.le j))
      simp only [Function.comp_apply]
      rw [show -(2 / 5 : ℝ) = (3 / 5 : ℝ) - 1 by norm_num,
        Real.rpow_sub hj, Real.rpow_one])
  have hi := tendsto_inv_atTop_zero.comp hlog
  have hc := hi.const_mul
    ((lastVisitDepthBound n ⌊M⌋₊ : ℝ) + |Real.log M / clockDrift|)
  convert (hp.const_mul globalClockErrorConstant).add hc using 1
  · ext j
    unfold ladderLastClockError
    simp only [Function.comp_apply]
    ring
  · ring

theorem ladderClockLimit_of_all_errors {n : ℕ} {M : ℝ} {x : ℕ → ℕ}
    (hM : 1 < M) (hx : ∀ I, x ∈ finiteLadderClockEvent n M I) :
    x ∈ ladderClockLimitEvent n M := by
  have hbound : ∀ j,
      |(ladderLastClock n M x j : ℝ) / Real.log (clockScale M j) - 1 / clockDrift| ≤
        ladderLastClockError n M j / Real.log (clockScale M j) := by
    intro j
    have hj : 0 < Real.log (clockScale M j) :=
      Real.log_pos (hM.trans_le (le_clockScale hM.le j))
    have he := hx j j le_rfl
    have hid : (ladderLastClock n M x j : ℝ) / Real.log (clockScale M j) -
        1 / clockDrift =
        ((ladderLastClock n M x j : ℝ) - Real.log (clockScale M j) / clockDrift) /
          Real.log (clockScale M j) := by
      rw [sub_div, div_right_comm (Real.log (clockScale M j)), div_self hj.ne']
    rw [hid, abs_div, abs_of_pos hj]
    exact div_le_div_of_nonneg_right he hj.le
  have hlo : Tendsto (fun j => -(ladderLastClockError n M j / Real.log (clockScale M j)) +
      1 / clockDrift) atTop (𝓝 (1 / clockDrift)) := by
    simpa using (ladderLastClockError_normalized_tendsto_zero hM n).neg.add_const (1 / clockDrift)
  have hhi : Tendsto (fun j => ladderLastClockError n M j / Real.log (clockScale M j) +
      1 / clockDrift) atTop (𝓝 (1 / clockDrift)) := by
    simpa using (ladderLastClockError_normalized_tendsto_zero hM n).add_const (1 / clockDrift)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (Eventually.of_forall (fun j => by have h := (abs_le.mp (hbound j)).1; linarith))
    (Eventually.of_forall (fun j => by have h := (abs_le.mp (hbound j)).2; linarith))

theorem finiteLadderClockEvent_antitone (n : ℕ) (M : ℝ) :
    Antitone (finiteLadderClockEvent n M) := by
  intro I J hIJ x hx j hj
  exact hx j (hj.trans hIJ)

theorem ladderClockLimit_compl_le_of_finite_errors {n : ℕ} {M : ℝ}
    (hM : 1 < M) (e : ℝ≥0∞)
    (hprob : ∀ I, pathLaw n (finiteLadderClockEvent n M I)ᶜ ≤ e) :
    pathLaw n (ladderClockLimitEvent n M)ᶜ ≤ e := by
  have hsub : (ladderClockLimitEvent n M)ᶜ ⊆
      ⋃ I, (finiteLadderClockEvent n M I)ᶜ := by
    intro x hx
    by_contra h
    apply hx
    apply ladderClockLimit_of_all_errors hM
    intro I
    by_contra hI
    exact h (Set.mem_iUnion.mpr ⟨I, hI⟩)
  apply (measure_mono hsub).trans
  have hmono : Monotone (fun I => (finiteLadderClockEvent n M I)ᶜ) := by
    intro I J hIJ
    exact Set.compl_subset_compl.mpr (finiteLadderClockEvent_antitone n M hIJ)
  rw [hmono.measure_iUnion]
  exact iSup_le hprob

theorem ae_ladderClockLimit_of_shifted_finite_errors {n : ℕ} {M : ℝ}
    (hM : 1 < M) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hprob : ∀ᶠ J : ℕ in atTop, ∀ I,
      pathLaw n (finiteLadderClockEvent n (clockScale M J) I)ᶜ ≤ ENNReal.ofReal (e J)) :
    ∀ᵐ x ∂pathLaw n, x ∈ ladderClockLimitEvent n M := by
  apply ae_iff.mpr
  have hh : ∀ᶠ J : ℕ in atTop,
      (pathLaw n (ladderClockLimitEvent n M)ᶜ).toReal ≤ max (e J) 0 := by
    filter_upwards [hprob] with J hJ
    have hMJ : 1 < clockScale M J := hM.trans_le (le_clockScale hM.le J)
    have h := ladderClockLimit_compl_le_of_finite_errors hMJ (ENNReal.ofReal (e J)) hJ
    rw [ladderClockLimitEvent_shift (zero_le_one.trans hM.le)] at h
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq ENNReal.toReal_ofReal'
  have hzero : (pathLaw n (ladderClockLimitEvent n M)ᶜ).toReal ≤ 0 := by
    have ht : Tendsto (fun J => max (e J) 0) atTop (𝓝 (0 : ℝ)) := by
      simpa using he.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact ge_of_tendsto ht hh
  exact (ENNReal.toReal_eq_zero_iff _).mp
    (le_antisymm hzero ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)

#print axioms clockScale_compose
#print axioms ladderClockLimitEvent_shift
#print axioms ladderClockLimit_of_all_errors
#print axioms ladderClockLimit_compl_le_of_finite_errors
#print axioms ae_ladderClockLimit_of_shifted_finite_errors

end CollatzCylinderPacking.Arithmetic.InverseDoob
