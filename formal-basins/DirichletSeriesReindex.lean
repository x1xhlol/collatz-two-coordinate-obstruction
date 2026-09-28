import DirichletPowerPerturbation

open Filter Topology Set
open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

theorem powered_dirichlet_summable_all_nat {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s : ℝ} (hs : 1 < s) :
    Summable (fun q : ℕ => w q ^ s / (q : ℝ) ^ s) := by
  apply Summable.of_nonneg_of_le _ _ (Real.summable_one_div_nat_rpow.mpr hs)
  · intro q
    exact div_nonneg (Real.rpow_nonneg (hw0 q) _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  · intro q
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    exact (Real.rpow_le_self_of_le_one (hw0 q) (hw1 q) hs.le).trans (hw1 q)

theorem powered_dirichlet_reindex {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, w (n + 1) ^ (1 + ε) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) =
      ∑' q : ℕ, w q ^ (1 + ε) / (q : ℝ) ^ (1 + ε) := by
  have hsum := powered_dirichlet_summable_all_nat hw0 hw1 (by linarith : 1 < 1 + ε)
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Real.zero_rpow (by linarith : (1 : ℝ) + ε ≠ 0),
    div_zero, zero_add]
  apply tsum_congr
  intro n
  rw [show -1 - ε = -(1 + ε) by ring, Real.rpow_neg (by positivity), div_eq_mul_inv]

theorem subtract_one_tendsto_nhdsGT :
    Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun s : ℝ => s) (𝓝[>] (1 : ℝ)) (𝓝 1) := nhdsWithin_le_nhds
    simpa using h.sub_const 1
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 0 < s - 1
    exact sub_pos.mpr hs

#print axioms powered_dirichlet_summable_all_nat
#print axioms powered_dirichlet_reindex
#print axioms subtract_one_tendsto_nhdsGT

end CollatzCanonical.DirichletAbelian
