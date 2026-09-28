import WeightPowerPerturbation
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

theorem shifted_power_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ) : ℕ → ℝ) := by
  exact (Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1)).comp_injective
    (fun a b h => Nat.add_right_cancel h)

theorem weighted_dirichlet_summable {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) := by
  apply (shifted_power_summable hε).of_nonneg_of_le
  · intro n
    exact mul_nonneg (hw0 _) (Real.rpow_nonneg (by positivity) _)
  · intro n
    simpa using mul_le_mul_of_nonneg_right (hw1 (n + 1))
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ)) (-1 - ε))

theorem powered_weight_dirichlet_summable {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => w (n + 1) ^ (1 + ε) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) := by
  apply weighted_dirichlet_summable (fun n => Real.rpow_nonneg (hw0 n) _) _ hε
  intro n
  exact (Real.rpow_le_self_of_le_one (hw0 n) (hw1 n) (by linarith)).trans (hw1 n)

theorem normalized_weight_power_error {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ ε * ((∑' n : ℕ, w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) -
      ∑' n : ℕ, w (n + 1) ^ (1 + ε) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) ∧
    ε * ((∑' n : ℕ, w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) -
      ∑' n : ℕ, w (n + 1) ^ (1 + ε) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) ≤
      (ε / Real.exp 1) * (ε * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) := by
  let f : ℕ → ℝ := fun n => (w (n + 1) - w (n + 1) ^ (1 + ε)) *
    ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)
  have hf : Summable f := by
    simpa only [f, sub_mul] using
      (weighted_dirichlet_summable hw0 hw1 hε).sub
        (powered_weight_dirichlet_summable hw0 hw1 hε)
  have hf0 (n : ℕ) : 0 ≤ f n := mul_nonneg
    (WeightPerturbation.uniform_weight_power_perturbation (hw0 _) (hw1 _) hε.le).1
    (Real.rpow_nonneg (by positivity) _)
  have hfu (n : ℕ) : f n ≤ ε / Real.exp 1 * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ) :=
    mul_le_mul_of_nonneg_right
      (WeightPerturbation.uniform_weight_power_perturbation (hw0 _) (hw1 _) hε.le).2
      (Real.rpow_nonneg (by positivity) _)
  have heq : (∑' n : ℕ, w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) -
      (∑' n : ℕ, w (n + 1) ^ (1 + ε) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) = ∑' n, f n := by
    rw [← Summable.tsum_sub (weighted_dirichlet_summable hw0 hw1 hε)
      (powered_weight_dirichlet_summable hw0 hw1 hε)]
    apply tsum_congr
    intro n
    simp only [f, sub_mul]
  rw [heq]
  refine ⟨mul_nonneg hε.le (tsum_nonneg hf0), ?_⟩
  have hu := Summable.tsum_le_tsum hfu hf ((shifted_power_summable hε).mul_left (ε / Real.exp 1))
  rw [tsum_mul_left] at hu
  nlinarith [mul_le_mul_of_nonneg_left hu hε.le]

theorem powered_dirichlet_limit_of_normalized_zeta_bound {w : ℕ → ℝ} {D : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hzeta : ∀ ε : ℝ, 0 < ε →
      ε * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) ≤ 1 + ε)
    (hlimit : Tendsto (fun ε : ℝ => ε *
      ∑' n : ℕ, w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 D)) :
    Tendsto (fun ε : ℝ => ε *
      ∑' n : ℕ, w (n + 1) ^ (1 + ε) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 D) := by
  let E : ℝ → ℝ := fun ε => ε *
    ((∑' n : ℕ, w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) -
      ∑' n : ℕ, w (n + 1) ^ (1 + ε) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ))
  have hεlim : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hupper : Tendsto (fun ε : ℝ => (ε / Real.exp 1) * (1 + ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hεlim.div_const (Real.exp 1)).mul (tendsto_const_nhds.add hεlim)
  have herr : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' _ hupper
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    obtain ⟨hl, hu⟩ := normalized_weight_power_error hw0 hw1 hεpos
    rw [Real.norm_of_nonneg hl]
    exact hu.trans (mul_le_mul_of_nonneg_left (hzeta ε hεpos) (by positivity))
  have h := hlimit.sub herr
  simpa only [sub_zero] using h.congr (fun ε => by dsimp [E]; ring)

#print axioms shifted_power_summable
#print axioms weighted_dirichlet_summable
#print axioms powered_weight_dirichlet_summable
#print axioms normalized_weight_power_error
#print axioms powered_dirichlet_limit_of_normalized_zeta_bound

end CollatzCanonical.DirichletAbelian
