import CanonicalCylinderAbel
import ActualFirstHitReconstruction
import ShortcutOddEndpoints
import NativeSyracuseClockBridge

set_option autoImplicit false
open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao Erdos1135

noncomputable section

/-- The coefficient of an odd source whose first target hit has exactly k odd steps. -/
def exactFirstHitTerm (k N q : ℕ) : ℝ :=
  if q % 2 = 1 ∧ ∃ A, FirstHit q N A ∧ oddCount A q = k
  then (N : ℝ) * firstHitWeight N q / (q : ℝ) else 0

def exactFirstHitCoefficient (k N : ℕ) : ℝ :=
  ∑' q : ℕ, exactFirstHitTerm k N q

theorem exactFirstHitTerm_nonneg (k N q : ℕ) : 0 ≤ exactFirstHitTerm k N q := by
  unfold exactFirstHitTerm
  split_ifs
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg N) (firstHitWeight_bounds N q).1)
      (Nat.cast_nonneg q)
  · exact le_rfl

theorem exactFirstHitTerm_of_first_hit {q N A : ℕ} (hf : FirstHit q N A) (k : ℕ) :
    exactFirstHitTerm k N q =
      if q % 2 = 1 ∧ oddCount A q = k then orbitRatio A q else 0 := by
  have he : (∃ B, FirstHit q N B ∧ oddCount B q = k) ↔ oddCount A q = k := by
    constructor
    · rintro ⟨B, hB, hd⟩
      rwa [firstHit_time_unique hB hf] at hd
    · intro hd
      exact ⟨A, hf, hd⟩
  rw [exactFirstHitTerm, he]
  split_ifs with h
  · exact (orbitRatio_first_hit (by omega) hf).symm
  · rfl

theorem exactFirstHitTerm_le_partial (k N q : ℕ) :
    exactFirstHitTerm k N q ≤ firstHitPartialTerm k N q := by
  rw [firstHitPartialTerm_eq_weight]
  unfold exactFirstHitTerm
  by_cases h : q % 2 = 1 ∧ ∃ A, FirstHit q N A ∧ oddCount A q = k
  · obtain ⟨ho, A, hf, hd⟩ := h
    rw [if_pos ⟨ho, A, hf, hd⟩, if_pos ⟨ho, A, hf, hd.le⟩]
  · rw [if_neg h]
    split_ifs
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg N) (firstHitWeight_bounds N q).1)
        (Nat.cast_nonneg q)
    · exact le_rfl

theorem exactFirstHitTerm_summable {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Summable (exactFirstHitTerm k N) :=
  Summable.of_nonneg_of_le (exactFirstHitTerm_nonneg k N)
    (exactFirstHitTerm_le_partial k N) (firstHitPartialTerm_summable hN k)

theorem exactFirstHitCoefficient_nonneg (k N : ℕ) : 0 ≤ exactFirstHitCoefficient k N :=
  tsum_nonneg (exactFirstHitTerm_nonneg k N)

theorem exactFirstHitTerm_succ (k N q : ℕ) :
    exactFirstHitTerm (k + 1) N q =
      firstHitPartialTerm (k + 1) N q - firstHitPartialTerm k N q := by
  by_cases hh : ∃ A, iterate A q = N
  · have hf := firstHitTime_spec hh
    rw [exactFirstHitTerm_of_first_hit hf, firstHitPartialTerm_of_first_hit hf,
      firstHitPartialTerm_of_first_hit hf]
    split_ifs <;> simp_all <;> omega
  · have hn (k : ℕ) : ¬ ∃ A, FirstHit q N A ∧ oddCount A q = k := by
      rintro ⟨A, hf, _⟩
      exact hh ⟨A, hf.1⟩
    simp [exactFirstHitTerm, hn, firstHitPartialTerm, hh]

/-- Exact depth is the increment of the native cumulative first-hit sum. -/
theorem exactFirstHitCoefficient_succ {N : ℕ} (hN : 0 < N) (k : ℕ) :
    exactFirstHitCoefficient (k + 1) N =
      firstHitPartialSum (k + 1) N - firstHitPartialSum k N := by
  simp_rw [exactFirstHitCoefficient, exactFirstHitTerm_succ]
  exact (firstHitPartialTerm_summable hN (k + 1)).tsum_sub
    (firstHitPartialTerm_summable hN k)

theorem shortcut_odd_return_eq_syracuse {N A : ℕ} (hN : Odd N)
    (hret : iterate A N = N) :
    (Tao.syracuse^[oddCount A N]) N = N := by
  obtain ⟨j, hj⟩ := shortcut_odd_endpoint_is_syracuse_clock A N hN (by rwa [hret])
  rw [hj, syracuse_shortcut_oddCount]
  simpa only [hj, syracuse_shortcut_landing] using hret

/-- Only returns of odd length at most K are excluded. -/
theorem cumulative_cylinder_eq_firstHit_of_finite_no_return {N : ℕ} (hN : Odd N)
    (K : ℕ) (hno : ∀ j : ℕ, 0 < j → j ≤ K → (Tao.syracuse^[j]) N ≠ N) :
    (∑ k ∈ Finset.range (K + 1), canonicalRho k N) = firstHitPartialSum K N := by
  have hNpos : 0 < N := by obtain ⟨t, ht⟩ := hN; omega
  have hNmod : N % 2 = 1 := Nat.odd_iff.mp hN
  simp_rw [canonicalRho_eq_arithmetic hNpos]
  by_cases hr : ∃ r : ℕ, 0 < r ∧ iterate r N = N
  · obtain ⟨r, hp⟩ := exists_least_positive_period hr
    have hm : K < oddCount r N := by
      by_contra h
      exact hno (oddCount r N)
        (positive_cycle_oddCount_pos hNpos hp.positive hp.returns)
        (Nat.le_of_not_gt h) (shortcut_odd_return_eq_syracuse hN hp.returns)
    rw [arithmetic_cumulative_periodic hNpos hp K, Nat.div_eq_of_lt hm]
    simp [hNmod]
  · have hret : ∀ r : ℕ, 0 < r → iterate r N ≠ N := by
      intro r hrp he
      exact hr ⟨r, hrp, he⟩
    rw [arithmetic_cumulative_no_return hNpos hret K]
    simp [hNmod]

/-- At a target with no return through depth k+1, the cylinder coefficient is first-hit only. -/
theorem canonicalRho_eq_exactFirstHitCoefficient_of_finite_no_return {N : ℕ}
    (hN : Odd N) (k : ℕ)
    (hno : ∀ j : ℕ, 0 < j → j ≤ k + 1 → (Tao.syracuse^[j]) N ≠ N) :
    canonicalRho (k + 1) N = exactFirstHitCoefficient (k + 1) N := by
  have hNpos : 0 < N := by obtain ⟨t, ht⟩ := hN; omega
  have hbig := cumulative_cylinder_eq_firstHit_of_finite_no_return hN (k + 1) hno
  have hsmall := cumulative_cylinder_eq_firstHit_of_finite_no_return hN k
    (fun j hj hk => hno j hj (by omega))
  rw [Finset.sum_range_succ] at hbig
  rw [hsmall] at hbig
  rw [exactFirstHitCoefficient_succ hNpos]
  linarith

#print axioms exactFirstHitCoefficient_succ
#print axioms canonicalRho_eq_exactFirstHitCoefficient_of_finite_no_return
end
end CollatzCanonical.PeriodicCensusFloor
