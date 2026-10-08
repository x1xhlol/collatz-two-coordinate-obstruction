import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 800000

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.WeightedKernel

theorem bounded_of_tendsto {u : ℕ → ℝ} {L : ℝ}
    (hu : Tendsto u atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |u n| ≤ C := by
  have hev : ∀ᶠ n in atTop, |u n| < |L| + 1 :=
    hu.abs.eventually (Iio_mem_nhds (lt_add_one _))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : ℝ := ∑ n ∈ Finset.range N, |u n|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ => abs_nonneg (u n))
  refine ⟨|L| + 1 + S, by positivity, ?_⟩
  intro n
  by_cases hn : n < N
  · have h := Finset.single_le_sum (fun i _ => abs_nonneg (u i))
      (Finset.mem_range.mpr hn)
    change |u n| ≤ S at h
    linarith [abs_nonneg L]
  · have h := hN n (Nat.le_of_not_gt hn)
    linarith

theorem weighted_summable_of_bounded {w u : ℕ → ℝ} {C : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (hu : ∀ n, |u n| ≤ C) :
    Summable (fun n => w n * u n) := by
  apply (hs.mul_right C).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n)]
  exact mul_le_mul_of_nonneg_left (hu n) (hw n)

/-- Positive normalized kernels preserve sequence limits when the mass of every fixed index
tends to zero. -/
theorem normalized_kernel_tendsto {α : Type*} {l : Filter α}
    (w : α → ℕ → ℝ) (hw : ∀ x n, 0 ≤ w x n)
    (hs : ∀ x, Summable (w x)) (hm : ∀ x, ∑' n, w x n = 1)
    (hpoint : ∀ n, Tendsto (fun x => w x n) l (𝓝 0))
    {u : ℕ → ℝ} {L : ℝ} (hu : Tendsto u atTop (𝓝 L)) :
    Tendsto (fun x => ∑' n, w x n * u n) l (𝓝 L) := by
  obtain ⟨C, hC, hb⟩ := bounded_of_tendsto hu
  have hwu (x : α) := weighted_summable_of_bounded (hw x) (hs x) hb
  have hwa (x : α) : Summable (fun n => w x n * (u n - L)) := by
    simpa only [mul_sub] using (hwu x).sub ((hs x).mul_right L)
  have hwabs (x : α) : Summable (fun n => w x n * |u n - L|) := by
    have hbound : ∀ n, |u n - L| ≤ C + |L| := by
      intro n
      linarith [abs_sub (u n) L, hb n]
    exact weighted_summable_of_bounded (hw x) (hs x)
      (fun n => by simpa only [abs_abs] using hbound n)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε / 2 := by linarith
  have hev := (Metric.tendsto_atTop.mp hu) (ε / 2) he
  obtain ⟨N, hN⟩ := hev
  have hhead : Tendsto (fun x => ∑ n ∈ Finset.range N, w x n * |u n - L|)
      l (𝓝 0) := by
    simpa only [zero_mul, Finset.sum_const_zero] using
      tendsto_finset_sum (Finset.range N) (fun n _ => (hpoint n).mul_const |u n - L|)
  filter_upwards [hhead.eventually (Iio_mem_nhds he)] with x hx
  have hfinite : Summable (fun n => if n ∈ Finset.range N then w x n * |u n - L| else 0) := by
    exact summable_of_ne_finset_zero (s := Finset.range N) (fun n hn => by simp [hn])
  have hmajor : ∀ n, w x n * |u n - L| ≤
      (if n ∈ Finset.range N then w x n * |u n - L| else 0) + w x n * (ε / 2) := by
    intro n
    by_cases hn : n ∈ Finset.range N
    · simp only [if_pos hn]
      exact le_add_of_nonneg_right (mul_nonneg (hw x n) he.le)
    · simp only [if_neg hn, zero_add]
      apply mul_le_mul_of_nonneg_left _ (hw x n)
      have h := hN n (by simpa only [Finset.mem_range, not_lt] using hn)
      simpa only [Real.dist_eq] using h.le
  have hbound := (hwabs x).tsum_le_tsum hmajor (hfinite.add ((hs x).mul_right (ε / 2)))
  rw [Summable.tsum_add hfinite ((hs x).mul_right (ε / 2)),
    tsum_mul_right, hm x, one_mul] at hbound
  have hf : (∑' n, if n ∈ Finset.range N then w x n * |u n - L| else 0) =
      ∑ n ∈ Finset.range N, w x n * |u n - L| := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by simp [hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [hn])
  rw [hf] at hbound
  have heq : (∑' n, w x n * u n) - L = ∑' n, w x n * (u n - L) := by
    simp_rw [mul_sub]
    rw [Summable.tsum_sub (hwu x) ((hs x).mul_right L), tsum_mul_right, hm x, one_mul]
  rw [Real.dist_eq, heq]
  have hn : Summable (fun n => ‖w x n * (u n - L)‖) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw x _)] using hwabs x
  have hab : |∑' n, w x n * (u n - L)| ≤ ∑' n, w x n * |u n - L| := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw x _)] using
      norm_tsum_le_tsum_norm hn
  linarith

end CollatzCanonical.WeightedKernel
