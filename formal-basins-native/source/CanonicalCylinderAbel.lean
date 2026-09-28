import CesaroAbelLimit
import ArithmeticCylinderGrowth
import CanonicalSyracuseCylinderLaw

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCylinderPacking.Arithmetic

noncomputable def canonicalRho (k N : ℕ) : ℝ :=
  (3 : ℝ) ^ k *
    (canonicalSyracuseMeasure {x : ℤ_[3] |
      PadicInt.toZModPow k x = (N : ZMod (3 ^ k))}).toReal

theorem canonicalRho_eq_arithmetic {N : ℕ} (hN : 0 < N) (k : ℕ) :
    canonicalRho k N = (3 : ℝ) ^ k * arithmeticMass k N := by
  rw [canonicalRho, canonical_cylinder_arithmetic hN]

theorem canonicalRho_nonneg (k N : ℕ) : 0 ≤ canonicalRho k N := by
  unfold canonicalRho
  positivity

theorem canonicalRho_linear_bound {N : ℕ} (hN : 0 < N) (k : ℕ) :
    canonicalRho k N ≤ 5 * (k : ℝ) * N + 1 := by
  rw [canonicalRho_eq_arithmetic hN]
  exact arithmetic_rho_linear_bound hN k

theorem canonicalRho_abel_summable {N : ℕ} (hN : 0 < N)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun k => ‖canonicalRho k N * z ^ k‖) := by
  have hs := arithmetic_rho_abel_summable hN hz hz1
  convert hs using 1
  ext k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (canonicalRho_nonneg k N)
    (pow_nonneg hz k)), canonicalRho_eq_arithmetic hN]
  exact mul_comm _ _

/-- The actual canonical cylinders have the Abel limit whenever their Cesàro
means converge. Summability follows from the arithmetic integer-height bound. -/
theorem canonical_cylinder_abel_of_cesaro {N : ℕ} (hN : 0 < N) {L : ℝ}
    (hm : Tendsto (CollatzCanonical.CesaroAbel.cesaroMean (fun k => canonicalRho k N))
      atTop (𝓝 L)) :
    Tendsto (fun z => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 L) :=
  CollatzCanonical.CesaroAbel.cesaro_abel_tendsto hm
    (fun _ hz hz1 => canonicalRho_abel_summable hN hz hz1)

/-- Dividing the sum through depth `K` by `K` gives the same limit as
the conventional Cesàro normalization by `K + 1`. -/
theorem cesaroMean_of_depth_mean {f : ℕ → ℝ} {L : ℝ}
    (hm : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range (K + 1), f k) / (K : ℝ))
      atTop (𝓝 L)) :
    Tendsto (CollatzCanonical.CesaroAbel.cesaroMean f) atTop (𝓝 L) := by
  have h := hm.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  unfold CollatzCanonical.CesaroAbel.cesaroMean
  field_simp

/-- The normalization used in the basin paper implies the actual cylinder
Abel limit, with no separate generating-series convergence hypothesis. -/
theorem canonical_cylinder_abel_of_depth_mean {N : ℕ} (hN : 0 < N) {L : ℝ}
    (hm : Tendsto (fun K : ℕ =>
      (∑ k ∈ Finset.range (K + 1), canonicalRho k N) / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun z => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 L) :=
  canonical_cylinder_abel_of_cesaro hN (cesaroMean_of_depth_mean hm)

end CollatzCylinderPacking.Arithmetic
