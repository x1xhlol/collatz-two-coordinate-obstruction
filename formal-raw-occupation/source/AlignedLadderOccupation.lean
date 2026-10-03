import BoundedBottomPassageClock
import PreBarrierWeightedOccupation

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open Erdos1135.Tao CollatzClockAudit

/-- Any intermediate barrier can be a rung of a ladder whose base stays in
one fixed compact interval. -/
theorem exists_aligned_clock_base {M x : ℝ} (hM : 1 < M) (hMx : M ≤ x) :
    ∃ m : ℝ, ∃ n : ℕ, M ≤ m ∧ m < M ^ taoAlpha ∧ clockScale m n = x := by
  have hLM : 0 < Real.log M := Real.log_pos hM
  have hMxlog : Real.log M ≤ Real.log x := Real.log_le_log (by linarith) hMx
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near ((one_le_div hLM).mpr hMxlog) taoAlpha_one_lt
  let m := Real.exp (Real.log x / taoAlpha ^ n)
  have hpow : 0 < taoAlpha ^ n := pow_pos taoAlpha_pos n
  have hlo' : Real.log M ≤ Real.log x / taoAlpha ^ n := by
    apply (le_div_iff₀ hpow).mpr
    have h := (le_div_iff₀ hLM).mp hlo
    simpa only [mul_comm] using h
  have hhi' : Real.log x / taoAlpha ^ n < Real.log M * taoAlpha := by
    apply (div_lt_iff₀ hpow).mpr
    have h := (div_lt_iff₀ hLM).mp hhi
    rw [pow_succ] at h
    nlinarith
  refine ⟨m, n, ?_, ?_, ?_⟩
  · calc
      M = Real.exp (Real.log M) := (Real.exp_log (by linarith)).symm
      _ ≤ m := Real.exp_le_exp.mpr hlo'
  · have hp : 0 < M ^ taoAlpha := Real.rpow_pos_of_pos (by linarith) _
    apply (Real.log_lt_log_iff (Real.exp_pos _) hp).mp
    simpa only [m, Real.log_exp, Real.log_rpow (show 0 < M by linarith), mul_comm] using hhi'
  · apply Real.log_injOn_pos (clockScale_pos (Real.exp_pos _) n) (show 0 < x by linarith)
    rw [clockScale_log (Real.exp_pos _), show Real.log m = Real.log x / taoAlpha ^ n by
      simp only [m, Real.log_exp]]
    exact div_mul_cancel₀ _ hpow.ne'

/-- This witness retains the actual global event and the rung number, rather
than replacing the lower segment clock by an endpoint approximation. -/
def AlignedClockWitness (M x : ℝ) (B : ℕ) (q : TaoOddNat) : Prop :=
  ∃ (m : ℝ) (hm : 1 ≤ m) (j n : ℕ),
    M ≤ m ∧ m ≤ (B : ℝ) ∧ clockScale m n = x ∧ n ≤ j ∧
      q ∈ globalClockGoodEvent m hm j

noncomputable def commonBottomClockError (M R : ℝ) (B : ℕ) : ℝ :=
  globalClockErrorConstant * (Real.log R) ^ (3 / 5 : ℝ) +
    boundedBarrierRemainder M B + |Real.log (B : ℝ) / clockDrift|

theorem aligned_clock_witness_first_hit {M x : ℝ} {B : ℕ} {q : TaoOddNat}
    (hw : AlignedClockWitness M x B q) :
    syracuseFirstHitAtMostReal x q.1 (actualBarrierTime x q.1) := by
  obtain ⟨m, hm, j, n, _, _, heq, hnj, hgood⟩ := hw
  obtain ⟨t, ht⟩ := global_clock_good_intermediate_first_hit hm j n hnj q hgood
  apply actualBarrierTime_first_hit
  exact ⟨t, by simpa only [heq] using ht.1⟩

theorem aligned_clock_witness_error {M x R : ℝ} {B : ℕ} {q : TaoOddNat}
    (hw : AlignedClockWitness M x B q) (hxR : x ≤ R)
    (hbottom : syracuseHitsAtMostReal q.1 M) :
    |((actualBarrierTime M q.1 - actualBarrierTime x q.1 : ℕ) : ℝ) -
      Real.log x / clockDrift| ≤ commonBottomClockError M R B := by
  obtain ⟨m, hm, j, n, hMm, hmB, heq, hnj, hgood⟩ := hw
  have h := global_clock_good_common_bottom_clock hm hMm hmB j n hnj q hgood hbottom
  rw [heq] at h
  apply h.trans
  unfold commonBottomClockError
  have hx : 1 ≤ x := heq ▸ one_le_clockScale hm n
  have hB : 1 ≤ (B : ℝ) := hm.trans hmB
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hB
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have herr := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hlogx (Real.log_le_log (by linarith) hxR) (by norm_num : (0 : ℝ) ≤ 3 / 5))
    globalClockErrorConstant_pos.le
  have hb := div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hmB) clockDrift_pos.le
  rw [abs_of_nonneg (div_nonneg hlogm clockDrift_pos.le),
    abs_of_nonneg (div_nonneg hlogB clockDrift_pos.le)]
  linarith

/-- Actual stage events on finitely many aligned ladders give the finite
weighted occupation bound with a single source-independent error budget. -/
theorem exists_aligned_ladder_occupation_lower (theta : ℝ)
    (htheta : CollatzCanonical.PackingParameters.beta < theta) (htheta1 : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℕ → ℝ) {M : ℝ} {R B n : ℕ} (q : TaoOddNat),
      1 ≤ M → (∀ i < n, x (i + 1) ≤ x i) →
      (∀ i ≤ n, M ≤ x i) → (∀ i ≤ n, x i ≤ (R : ℝ)) →
      (∀ i ≤ n, AlignedClockWitness M (x i) B q) →
      syracuseHitsAtMostReal q.1 M →
      (∀ i < n,
        (3 / 2 : ℝ) ^ ((Real.log (x i) - Real.log (x (i + 1))) / clockDrift +
          2 * commonBottomClockError M R B) * (x i + 1) ≤ (R : ℝ) + 1) →
      (3 / 2 : ℝ) ^ (Real.log (x n) / clockDrift + commonBottomClockError M R B) *
        (x n + 1) ≤ (R : ℝ) + 1 →
      max 0 (1 - C * M ^ (theta - 1)) *
        (Real.log (x 0) / clockDrift - commonBottomClockError M R B) ≤
          oddTargetOccupation R q.1 := by
  obtain ⟨C, hC, hocc⟩ := exists_finite_clock_grid_occupation_lower theta htheta htheta1
  refine ⟨C, hC, ?_⟩
  intro x M R B n q hM hdown hbot hxR hw hbottom hstage hlast
  exact hocc x (fun i => actualBarrierTime (x i) q.1) hM q.2 hdown hbot
    (fun i hi => aligned_clock_witness_first_hit (hw i hi))
    (actualBarrierTime_first_hit hbottom)
    (fun i hi => aligned_clock_witness_error (hw i hi) (hxR i hi) hbottom) hstage hlast

#print axioms exists_aligned_clock_base
#print axioms aligned_clock_witness_first_hit
#print axioms aligned_clock_witness_error
#print axioms exists_aligned_ladder_occupation_lower

end CollatzCanonical.RawOccupation
