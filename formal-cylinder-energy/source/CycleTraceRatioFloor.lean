import CanonicalTracePolynomialFloor
import FixedBasinGreenBoundary

set_option autoImplicit false

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.GreenKernelScalars

noncomputable section

theorem harmonic_shifted_forward_bound (g : ℕ → ℝ) (c : ℝ)
    (hg : ∀ n, 0 ≤ g n)
    (hharm : ∀ n, 0 < n → g n = (1 / 2 : ℝ) * g (2 * n) +
      (3 / 2 : ℝ) * (if n % 3 = 2 then g (oddPredecessor n) else 0))
    (hfloor : ∀ n, 0 < n → n % 3 ≠ 0 → c ≤ g n)
    {n : ℕ} (hn : 0 < n) :
    orbitRatio 1 n * (g n - c * (n : ℝ)) ≤ g (step n) - c * (step n : ℝ) := by
  have hpos := CollatzCanonical.Correction.iterate_pos 1 hn
  change 0 < step n at hpos
  have hh := hharm (step n) hpos
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have heq := step_even he
    have hn' : n = 2 * step n := heq.symm
    have hratio : orbitRatio 1 n = (1 / 2 : ℝ) := by
      rw [hn', orbitRatio_one_even]
    have hnonneg : 0 ≤ (if step n % 3 = 2 then g (oddPredecessor (step n)) else 0) := by
      split_ifs
      · exact hg _
      · exact le_rfl
    have heqR : (n : ℝ) = 2 * (step n : ℝ) := by exact_mod_cast hn'
    rw [hratio]
    rw [← hn'] at hh
    have hc := congrArg (fun x : ℝ => c * x) heqR
    nlinarith only [hh, hnonneg, hc]
  · have hs := step_odd ho
    have hres : step n % 3 = 2 := by omega
    have hop : oddPredecessor (step n) = n := by unfold oddPredecessor; omega
    have htwo : 2 * step n = 3 * n + 1 := hs
    have hf := hfloor (3 * n + 1) (by omega) (by omega)
    rw [if_pos hres, hop, htwo] at hh
    have hsR : 2 * (step n : ℝ) = 3 * (n : ℝ) + 1 := by exact_mod_cast hs
    rw [orbitRatio_one_odd ho]
    have hc := congrArg (fun x : ℝ => c * x) hsR
    nlinarith only [hh, hf, hc]

theorem harmonic_shifted_iterate_bound (g : ℕ → ℝ) (c : ℝ)
    (hg : ∀ n, 0 ≤ g n)
    (hharm : ∀ n, 0 < n → g n = (1 / 2 : ℝ) * g (2 * n) +
      (3 / 2 : ℝ) * (if n % 3 = 2 then g (oddPredecessor n) else 0))
    (hfloor : ∀ n, 0 < n → n % 3 ≠ 0 → c ≤ g n)
    (k : ℕ) {n : ℕ} (hn : 0 < n) :
    orbitRatio k n * (g n - c * (n : ℝ)) ≤
      g (iterate k n) - c * (iterate k n : ℝ) := by
  induction k with
  | zero => simp [orbitRatio, oddCount, iterate]
  | succ k ih =>
    have hs := harmonic_shifted_forward_bound g c hg hharm hfloor
      (CollatzCanonical.Correction.iterate_pos k hn)
    have hm := mul_le_mul_of_nonneg_left ih (orbitRatio_pos 1 (iterate k n)).le
    rw [orbitRatio_add]
    change orbitRatio k n * orbitRatio 1 (iterate k n) * (g n - c * (n : ℝ)) ≤ _
    calc
      _ = orbitRatio 1 (iterate k n) * (orbitRatio k n * (g n - c * (n : ℝ))) := by ring
      _ ≤ orbitRatio 1 (iterate k n) * (g (iterate k n) - c * (iterate k n : ℝ)) := hm
      _ ≤ _ := hs

theorem harmonic_cycle_linear_floor (g : ℕ → ℝ) (c : ℝ)
    (hg : ∀ n, 0 ≤ g n)
    (hharm : ∀ n, 0 < n → g n = (1 / 2 : ℝ) * g (2 * n) +
      (3 / 2 : ℝ) * (if n % 3 = 2 then g (oddPredecessor n) else 0))
    (hfloor : ∀ n, 0 < n → n % 3 ≠ 0 → c ≤ g n)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hret : iterate k n = n) :
    c * (n : ℝ) ≤ g n := by
  have h := harmonic_shifted_iterate_bound g c hg hharm hfloor k hn
  rw [hret] at h
  have hratio := (positive_cycle_ratio_bounds hn hk hret).2
  nlinarith

theorem exists_uniform_cyclic_trace_ratio_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      (∃ k : ℕ, 0 < k ∧ iterate k n = n) →
      c * (n : ℝ) ≤ actualDensityValue actualFirstHitDensity n := by
  obtain ⟨c, hc, hfloor⟩ := exists_uniform_unit_canonical_trace_floor
  refine ⟨c, hc, ?_⟩
  intro n hn ⟨k, hk, hret⟩
  apply harmonic_cycle_linear_floor (actualDensityValue actualFirstHitDensity) c
    ?_ (fun n hn => actual_unconditional_density_harmonic hn) hfloor hn hk hret
  intro m
  by_cases hm : 0 < m
  · unfold actualDensityValue
    have hgamma := greenCycleFactor_one_ge_one hm
    exact mul_nonneg (mul_nonneg (mul_nonneg delta_pos.le (by linarith))
      (Nat.cast_nonneg m)) (actualFirstHitDensity_nonneg m)
  · have hm0 : m = 0 := by omega
    simp [hm0, actualDensityValue]

#print axioms harmonic_cycle_linear_floor
#print axioms exists_uniform_cyclic_trace_ratio_floor

end
end CollatzCanonical.PeriodicCensusFloor
