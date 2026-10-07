import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

open Filter Topology

namespace ActualInverseDoob

theorem tendsto_tsum_abs_sub_of_nonneg
    {α ι : Type*} {l : Filter α} {f : α → ι → ℝ} {g : ι → ℝ}
    (hf_nonneg : ∀ a i, 0 ≤ f a i) (hg_nonneg : ∀ i, 0 ≤ g i)
    (hf : ∀ a, Summable (f a)) (hg : Summable g)
    (hpoint : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i)))
    (hmass : Tendsto (fun a => ∑' i, f a i) l (𝓝 (∑' i, g i))) :
    Tendsto (fun a => ∑' i, |f a i - g i|) l (𝓝 0) := by
  have hmin_nonneg (a : α) (i : ι) : 0 ≤ min (f a i) (g i) :=
    le_min (hf_nonneg a i) (hg_nonneg i)
  have hmin_sum (a : α) : Summable (fun i => min (f a i) (g i)) :=
    hg.of_norm_bounded (fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hmin_nonneg a i)]
      exact min_le_right _ _)
  have hmin_limit : Tendsto (fun a => ∑' i, min (f a i) (g i)) l
      (𝓝 (∑' i, g i)) := by
    apply tendsto_tsum_of_dominated_convergence hg
    · intro i
      simpa using (hpoint i).min
        (tendsto_const_nhds : Tendsto (fun _ : α => g i) l (𝓝 (g i)))
    · exact Eventually.of_forall (fun a i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hmin_nonneg a i)]
        exact min_le_right _ _)
  have hidentity (a : α) :
      (∑' i, |f a i - g i|) =
        (∑' i, f a i) + (∑' i, g i) - 2 * (∑' i, min (f a i) (g i)) := by
    have hterm (i : ι) : |f a i - g i| = f a i + g i - 2 * min (f a i) (g i) := by
      rcases le_total (f a i) (g i) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    simp_rw [hterm]
    rw [((hf a).add hg).tsum_sub ((hmin_sum a).mul_left 2),
      (hf a).tsum_add hg, tsum_mul_left]
  simp_rw [hidentity]
  have hfinal := (hmass.add
    (tendsto_const_nhds : Tendsto (fun _ : α => ∑' i, g i) l (𝓝 (∑' i, g i)))).sub
      (hmin_limit.const_mul 2)
  simpa only [show (∑' i, g i) + (∑' i, g i) - 2 * (∑' i, g i) = 0 by ring]
    using hfinal

#print axioms tendsto_tsum_abs_sub_of_nonneg

end ActualInverseDoob
