import ActualGreenSeries
import GreenKernelScalars
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false

open Filter Topology
open CollatzCanonical.GreenKernelScalars

namespace CollatzCylinderPacking.Arithmetic

noncomputable def actualGreen (s : ℝ) (N : ℕ) : ℝ :=
  ∑' A : ℕ, inverseIterate s A N

noncomputable def normalizedGreen (s : ℝ) (N : ℕ) : ℝ :=
  (1 - kappa s) * actualGreen s N

theorem greenCycleFactor_continuousAt_one {N : ℕ} (hN : 0 < N) :
    ContinuousAt (fun s : ℝ => greenCycleFactor s N) 1 := by
  classical
  by_cases hret : ∃ r : ℕ, 0 < r ∧ iterate r N = N
  · have hb := positive_cycle_ratio_bounds hN (Nat.find_spec hret).1 (Nat.find_spec hret).2
    simp only [greenCycleFactor, dif_pos hret]
    apply ContinuousAt.inv₀
    · exact continuousAt_const.sub (Real.continuousAt_const_rpow hb.1.ne')
    · rw [Real.rpow_one]
      exact sub_ne_zero.mpr (ne_of_gt hb.2)
  · simpa only [greenCycleFactor, dif_neg hret] using
      (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 1)

theorem greenCycleFactor_one_pos {N : ℕ} (hN : 0 < N) :
    0 < greenCycleFactor 1 N := by
  classical
  by_cases hret : ∃ r : ℕ, 0 < r ∧ iterate r N = N
  · have hb := positive_cycle_ratio_bounds hN (Nat.find_spec hret).1 (Nat.find_spec hret).2
    simp only [greenCycleFactor, dif_pos hret, Real.rpow_one]
    exact inv_pos.mpr (sub_pos.mpr hb.2)
  · simp only [greenCycleFactor, dif_neg hret]
    norm_num

/-- The actual Green formula gives the critical limit once the weighted
Dirichlet residue is known. The residue hypothesis is the remaining analytic input. -/
theorem actual_green_critical_of_dirichlet {N : ℕ} (hN : 0 < N) {D : ℝ}
    (hD : Tendsto (fun s : ℝ => (s - 1) * ∑' q, weightedDirichletTerm s N q)
      (𝓝[>] 1) (𝓝 D)) :
    Tendsto (fun s => normalizedGreen s N) (𝓝[>] 1)
      (𝓝 (delta * greenCycleFactor 1 N * N * D)) := by
  have hB : Tendsto (fun s : ℝ => greenCycleFactor s N)
      (𝓝[>] 1) (𝓝 (greenCycleFactor 1 N)) :=
    (greenCycleFactor_continuousAt_one hN).tendsto.mono_left nhdsWithin_le_nhds
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hpow : Tendsto (fun s : ℝ => (N : ℝ) ^ s) (𝓝[>] 1) (𝓝 (N : ℝ)) := by
    simpa only [Real.rpow_one] using
      (Real.continuousAt_const_rpow (b := (1 : ℝ)) hN0).tendsto.mono_left nhdsWithin_le_nhds
  have h := ((kappa_critical_right_limit.mul hB).mul hpow).mul hD
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : 1 < s := hs
  have hne : s - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hs1)
  unfold normalizedGreen actualGreen
  rw [actual_green_tsum hs1 hN]
  field_simp

theorem actual_green_resolvent {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    actualGreen s N = 1 + inverseOperator s (actualGreen s) N := by
  have hsum := actual_green_summable hs hN
  rw [actualGreen, hsum.tsum_eq_zero_add]
  simp only [inverseIterate]
  congr 1
  unfold inverseOperator
  by_cases hres : N % 3 = 2
  · simp only [if_pos hres]
    rw [Summable.tsum_add
      ((actual_green_summable hs (by omega : 0 < 2 * N)).mul_left _)
      ((actual_green_summable hs (oddPredecessor_spec hres).1).mul_left _),
      tsum_mul_left, tsum_mul_left]
    rfl
  · simp only [if_neg hres, mul_zero, add_zero]
    rw [tsum_mul_left]
    rfl

theorem normalized_green_resolvent {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    normalizedGreen s N = (1 - kappa s) + inverseOperator s (normalizedGreen s) N := by
  rw [normalizedGreen, actual_green_resolvent hs hN]
  unfold inverseOperator normalizedGreen
  by_cases hres : N % 3 = 2 <;> simp only [hres, if_true, if_false] <;> ring

theorem inverse_coefficients_tendsto :
    Tendsto (fun s : ℝ => (2 : ℝ) ^ (-s)) (𝓝[>] 1) (𝓝 (1 / 2)) ∧
    Tendsto (fun s : ℝ => (3 / 2 : ℝ) ^ s) (𝓝[>] 1) (𝓝 (3 / 2)) := by
  have hs : Tendsto (fun s : ℝ => s) (𝓝[>] 1) (𝓝 1) := nhdsWithin_le_nhds
  constructor
  · convert (tendsto_const_nhds (x := (2 : ℝ))).rpow hs.neg
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0)) using 1
    norm_num [Real.rpow_neg]
  · simpa only [Real.rpow_one] using
      (tendsto_const_nhds (x := (3 / 2 : ℝ))).rpow hs
        (Or.inl (by norm_num : (3 / 2 : ℝ) ≠ 0))

theorem one_sub_kappa_tendsto_zero :
    Tendsto (fun s : ℝ => 1 - kappa s) (𝓝[>] 1) (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (inverse_coefficients_tendsto.1.add (inverse_coefficients_tendsto.2.div_const 3))
  convert h using 1
  norm_num [kappa]

/-- The actual resolvent gives the critical harmonic equation whenever
the finite pointwise limits exist at every positive integer. -/
theorem actual_green_harmonic_of_pointwise {g : ℕ → ℝ}
    (hg : ∀ N : ℕ, 0 < N → Tendsto (fun s => normalizedGreen s N) (𝓝[>] 1) (𝓝 (g N)))
    {N : ℕ} (hN : 0 < N) :
    g N = (1 / 2 : ℝ) * g (2 * N) +
      (3 / 2 : ℝ) * (if N % 3 = 2 then g (oddPredecessor N) else 0) := by
  have hhalf := inverse_coefficients_tendsto.1.mul (hg (2 * N) (by omega))
  have hresolvent : ∀ᶠ s : ℝ in 𝓝[>] 1,
      normalizedGreen s N = (1 - kappa s) + inverseOperator s (normalizedGreen s) N := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact normalized_green_resolvent hs hN
  by_cases hres : N % 3 = 2
  · have hodd := inverse_coefficients_tendsto.2.mul
      (hg (oddPredecessor N) (oddPredecessor_spec hres).1)
    have h := one_sub_kappa_tendsto_zero.add (hhalf.add hodd)
    simp only [zero_add] at h
    rw [if_pos hres]
    apply tendsto_nhds_unique (hg N hN)
    apply h.congr'
    filter_upwards [hresolvent] with s hs
    simpa only [inverseOperator, if_pos hres] using hs.symm
  · have h := one_sub_kappa_tendsto_zero.add hhalf
    simp only [zero_add] at h
    rw [if_neg hres, mul_zero, add_zero]
    apply tendsto_nhds_unique (hg N hN)
    apply h.congr'
    filter_upwards [hresolvent] with s hs
    simpa only [inverseOperator, if_neg hres, mul_zero, add_zero] using hs.symm

end CollatzCylinderPacking.Arithmetic
