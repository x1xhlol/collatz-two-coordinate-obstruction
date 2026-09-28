import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicConvolution

/-- The unnormalized contribution from repeating a loop of length `r`. -/
noncomputable def loopConvolution (r : ℕ) (β : ℝ) (F : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K / r + 1), β ^ j * F (K - r * j)

/-- A convergent normalized sequence has a global linear majorant, including index zero. -/
theorem linear_bound_of_mean_tendsto {F : ℕ → ℝ} {L : ℝ}
    (hF : Tendsto (fun K : ℕ => F K / (K : ℝ)) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, |F K| ≤ C * ((K : ℝ) + 1) := by
  have hev : ∀ᶠ K : ℕ in atTop, |F K / (K : ℝ)| < |L| + 1 :=
    hF.abs.eventually (Iio_mem_nhds (lt_add_one _))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : ℝ := ∑ k ∈ Finset.range (N + 1), |F k|
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => abs_nonneg (F k)
  let C : ℝ := |L| + 1 + S
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCL : |L| + 1 ≤ C := by dsimp [C]; linarith
  have hCS : S ≤ C := by dsimp [C]; linarith [abs_nonneg L]
  refine ⟨C, hC, fun K => ?_⟩
  by_cases hsmall : K < N + 1
  · have hk : |F K| ≤ S :=
      Finset.single_le_sum (fun k _ => abs_nonneg (F k)) (Finset.mem_range.mpr hsmall)
    calc
      |F K| ≤ C := hk.trans hCS
      _ ≤ C * ((K : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) K]
  · have hKN : N ≤ K := by omega
    have hK : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
    have hh := hN K hKN
    rw [abs_div, abs_of_pos hK] at hh
    have hf : |F K| ≤ (|L| + 1) * (K : ℝ) := (div_lt_iff₀ hK).mp hh |>.le
    calc
      |F K| ≤ (|L| + 1) * (K : ℝ) := hf
      _ ≤ C * (K : ℝ) := mul_le_mul_of_nonneg_right hCL hK.le
      _ ≤ C * ((K : ℝ) + 1) := by nlinarith

/-- Removing any fixed finite number of indices preserves the normalized limit. -/
theorem shifted_mean_tendsto {F : ℕ → ℝ} {L : ℝ}
    (hF : Tendsto (fun K : ℕ => F K / (K : ℝ)) atTop (𝓝 L)) (m : ℕ) :
    Tendsto (fun K : ℕ => F (K - m) / (K : ℝ)) atTop (𝓝 L) := by
  have hratio : Tendsto (fun K : ℕ => ((K - m : ℕ) : ℝ) / (K : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (m + 1)] with K hK
    have hKm : m ≤ K := by omega
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    rw [Nat.cast_sub hKm]
    field_simp
  have hshift := hF.comp (tendsto_sub_atTop_nat m)
  have hprod := hshift.mul hratio
  simp only [mul_one] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (m + 1)] with K hK
  exact div_mul_div_cancel₀ (show ((K - m : ℕ) : ℝ) ≠ 0 by
    exact_mod_cast (show K - m ≠ 0 by omega))

/-- Tannery's theorem applies uniformly to the geometrically weighted loop summands. -/
theorem loop_convolution_tendsto_of_linear_bound {F : ℕ → ℝ} {L C β : ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hF : Tendsto (fun K : ℕ => F K / (K : ℝ)) atTop (𝓝 L))
    (hC : 0 ≤ C) (hbound : ∀ K : ℕ, |F K| ≤ C * ((K : ℝ) + 1)) :
    Tendsto (fun K : ℕ => (1 / (K : ℝ)) * loopConvolution r β F K)
      atTop (𝓝 (L / (1 - β))) := by
  let f : ℕ → ℕ → ℝ := fun K j =>
    if r * j ≤ K then β ^ j * (F (K - r * j) / (K : ℝ)) else 0
  have hterm (j : ℕ) : Tendsto (fun K => f K j) atTop (𝓝 (β ^ j * L)) := by
    have h := (tendsto_const_nhds (x := β ^ j)).mul (shifted_mean_tendsto hF (r * j))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (r * j)] with K hK
    simp only [f, if_pos hK]
  have hdom : ∀ᶠ K : ℕ in atTop, ∀ j : ℕ, ‖f K j‖ ≤ (2 * C) * β ^ j := by
    filter_upwards [eventually_ge_atTop 1] with K hK j
    have hKpos : 0 < (K : ℝ) := by exact_mod_cast hK
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hβj : 0 ≤ β ^ j := pow_nonneg hβ0 j
    by_cases hj : r * j ≤ K
    · have hsub : ((K - r * j : ℕ) : ℝ) ≤ (K : ℝ) :=
        Nat.cast_le.mpr (Nat.sub_le K (r * j))
      have hratio : |F (K - r * j) / (K : ℝ)| ≤ 2 * C := by
        rw [abs_div, abs_of_pos hKpos]
        apply (div_le_iff₀ hKpos).mpr
        calc
          |F (K - r * j)| ≤ C * (((K - r * j : ℕ) : ℝ) + 1) := hbound _
          _ ≤ C * (2 * (K : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hC
          _ = (2 * C) * (K : ℝ) := by ring
      simp only [f, if_pos hj, Real.norm_eq_abs, abs_mul, abs_of_nonneg hβj]
      calc
        β ^ j * |F (K - r * j) / (K : ℝ)| ≤ β ^ j * (2 * C) :=
          mul_le_mul_of_nonneg_left hratio hβj
        _ = (2 * C) * β ^ j := by ring
    · simp only [f, if_neg hj, norm_zero]
      positivity
  have hsum : Summable (fun j : ℕ => (2 * C) * β ^ j) :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left (2 * C)
  have hlim := tendsto_tsum_of_dominated_convergence hsum hterm hdom
  have hvalue : (∑' j : ℕ, β ^ j * L) = L / (1 - β) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]
    ring
  rw [hvalue] at hlim
  convert hlim using 1
  ext K
  have hmem (j : ℕ) : j ∈ Finset.range (K / r + 1) ↔ r * j ≤ K := by
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega : 0 < r)]
    rw [Nat.mul_comm]
  rw [tsum_eq_sum (s := Finset.range (K / r + 1)) (by
    intro j hj
    simp only [f, if_neg (mt (hmem j).mpr hj)])]
  unfold loopConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [f, if_pos ((hmem j).mp hj)]
  ring

/-- The geometric period-loop limit needs no separate growth hypothesis. -/
theorem loop_convolution_tendsto {F : ℕ → ℝ} {L β : ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hF : Tendsto (fun K : ℕ => F K / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => (1 / (K : ℝ)) * loopConvolution r β F K)
      atTop (𝓝 (L / (1 - β))) := by
  obtain ⟨C, hC, hbound⟩ := linear_bound_of_mean_tendsto hF
  exact loop_convolution_tendsto_of_linear_bound hr hβ0 hβ1 hF hC hbound

/-- A uniformly bounded extra depth-zero contribution vanishes after normalization. -/
theorem bounded_remainder_div_tendsto_zero {E : ℕ → ℝ} {D : ℝ}
    (hE : ∀ K : ℕ, |E K| ≤ D) :
    Tendsto (fun K : ℕ => E K / (K : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun K : ℕ => D / (K : ℝ))
  · intro K
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ (K : ℝ) from Nat.cast_nonneg K)]
    exact div_le_div_of_nonneg_right (hE K) (Nat.cast_nonneg K)
  · exact tendsto_const_div_atTop_nhds_zero_nat D

/-- A bounded term outside the loop convolution does not change its limit. -/
theorem loop_convolution_add_bounded_remainder_tendsto
    {F E : ℕ → ℝ} {L β D : ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hF : Tendsto (fun K : ℕ => F K / (K : ℝ)) atTop (𝓝 L))
    (hE : ∀ K : ℕ, |E K| ≤ D) :
    Tendsto (fun K : ℕ => (loopConvolution r β F K + E K) / (K : ℝ))
      atTop (𝓝 (L / (1 - β))) := by
  have h := (loop_convolution_tendsto hr hβ0 hβ1 hF).add
    (bounded_remainder_div_tendsto_zero hE)
  simp only [add_zero] at h
  convert h using 1
  ext K
  ring

/-- The reconstruction form used when all-hit sums differ by a bounded depth-zero term. -/
theorem periodic_reconstruction_tendsto {F G : ℕ → ℝ} {L β D : ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hF : Tendsto (fun K : ℕ => F K / (K : ℝ)) atTop (𝓝 L))
    (herror : ∀ K : ℕ, |G K - loopConvolution r β F K| ≤ D) :
    Tendsto (fun K : ℕ => G K / (K : ℝ)) atTop (𝓝 (L / (1 - β))) := by
  have h := loop_convolution_add_bounded_remainder_tendsto hr hβ0 hβ1 hF herror
  simpa only [add_sub_cancel] using h

#print axioms linear_bound_of_mean_tendsto
#print axioms shifted_mean_tendsto
#print axioms loop_convolution_tendsto_of_linear_bound
#print axioms loop_convolution_tendsto
#print axioms bounded_remainder_div_tendsto_zero
#print axioms loop_convolution_add_bounded_remainder_tendsto
#print axioms periodic_reconstruction_tendsto

end CollatzCanonical.PeriodicConvolution
