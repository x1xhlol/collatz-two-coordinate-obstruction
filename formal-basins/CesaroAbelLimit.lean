import WeightedKernelLimit
import Mathlib.Tactic.FieldSimp

set_option maxHeartbeats 800000

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.CesaroAbel

noncomputable def abelKernel (z : ℝ) (n : ℕ) : ℝ :=
  if 0 ≤ z ∧ z < 1 then (1 - z) ^ 2 * ((n : ℝ) + 1) * z ^ n
  else if n = 0 then 1 else 0

theorem abelKernel_nonneg (z : ℝ) (n : ℕ) : 0 ≤ abelKernel z n := by
  unfold abelKernel
  split_ifs with hz hn
  · have hz0 := hz.1
    positivity
  · norm_num
  · norm_num

theorem abelKernel_hasSum (z : ℝ) : HasSum (abelKernel z) 1 := by
  classical
  by_cases hz : 0 ≤ z ∧ z < 1
  · have hn : ‖z‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
      exact hz.2
    have hs : HasSum (fun n : ℕ => ((n : ℝ) + 1) * z ^ n) (1 / (1 - z) ^ 2) := by
      simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hn
    have hh := hs.mul_left ((1 - z) ^ 2)
    have he : (1 - z) ^ 2 * (1 / (1 - z) ^ 2) = 1 := by
      have hne : 1 - z ≠ 0 := by linarith [hz.2]
      field_simp
    rw [he] at hh
    have heq : abelKernel z = fun n : ℕ => (1 - z) ^ 2 * (((n : ℝ) + 1) * z ^ n) := by
      funext n
      simp [abelKernel, hz, mul_assoc]
    rw [heq]
    exact hh
  · have heq : abelKernel z = fun n : ℕ => if n = 0 then 1 else 0 := by
      funext n
      simp [abelKernel, hz]
    rw [heq]
    exact hasSum_ite_eq 0 (1 : ℝ)

theorem eventually_abel_interval : ∀ᶠ z : ℝ in 𝓝[<] 1, 0 ≤ z ∧ z < 1 := by
  have h0 : ∀ᶠ z : ℝ in 𝓝 (1 : ℝ), 0 < z := Ioi_mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin, h0.filter_mono nhdsWithin_le_nhds] with z hz hz0
  exact ⟨le_of_lt hz0, hz⟩

theorem abelKernel_tendsto (n : ℕ) :
    Tendsto (fun z => abelKernel z n) (𝓝[<] 1) (𝓝 0) := by
  have hz : Tendsto (fun z : ℝ => z) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have h := ((((tendsto_const_nhds (x := (1 : ℝ))).sub hz).pow 2).mul_const
    ((n : ℝ) + 1)).mul (hz.pow n)
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_abel_interval] with z hz
  simp only [abelKernel, if_pos hz]

theorem abelKernel_preserves_limit {u : ℕ → ℝ} {L : ℝ}
    (hu : Tendsto u atTop (𝓝 L)) :
    Tendsto (fun z => ∑' n, abelKernel z n * u n) (𝓝[<] 1) (𝓝 L) :=
  CollatzCanonical.WeightedKernel.normalized_kernel_tendsto abelKernel abelKernel_nonneg
    (fun z => (abelKernel_hasSum z).summable) (fun z => (abelKernel_hasSum z).tsum_eq)
    abelKernel_tendsto hu

noncomputable def cesaroMean (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), f i) / ((n : ℝ) + 1)

theorem abelKernel_cesaro_identity (f : ℕ → ℝ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hs : Summable (fun n => ‖f n * z ^ n‖)) :
    (∑' n, abelKernel z n * cesaroMean f n) = (1 - z) * ∑' n, f n * z ^ n := by
  have hn : ‖z‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hz0]
  have hg := summable_norm_geometric_of_norm_lt_one hn
  have hp := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hs hg
  have hterm (n : ℕ) : (∑ k ∈ Finset.range (n + 1), (f k * z ^ k) * z ^ (n - k)) =
      (∑ k ∈ Finset.range (n + 1), f k) * z ^ n := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega : k ≤ n)]
  simp_rw [hterm] at hp
  rw [(hasSum_geometric_of_lt_one hz0 hz1).tsum_eq] at hp
  have heq (n : ℕ) : abelKernel z n * cesaroMean f n =
      (1 - z) ^ 2 * ((∑ k ∈ Finset.range (n + 1), f k) * z ^ n) := by
    simp only [abelKernel, if_pos (show 0 ≤ z ∧ z < 1 from ⟨hz0, hz1⟩), cesaroMean]
    have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  simp_rw [heq]
  rw [tsum_mul_left, ← hp]
  have hz : 1 - z ≠ 0 := by linarith
  field_simp

/-- Cesàro convergence implies the Abel limit; absolute convergence of each generating
series is explicit, and is separately proved for the arithmetic cylinder masses. -/
theorem cesaro_abel_tendsto {f : ℕ → ℝ} {L : ℝ}
    (hm : Tendsto (cesaroMean f) atTop (𝓝 L))
    (hs : ∀ z : ℝ, 0 ≤ z → z < 1 → Summable (fun n => ‖f n * z ^ n‖)) :
    Tendsto (fun z => (1 - z) * ∑' n, f n * z ^ n) (𝓝[<] 1) (𝓝 L) := by
  apply (abelKernel_preserves_limit hm).congr'
  filter_upwards [eventually_abel_interval] with z hz
  exact abelKernel_cesaro_identity f hz.1 hz.2 (hs z hz.1 hz.2)

end CollatzCanonical.CesaroAbel
