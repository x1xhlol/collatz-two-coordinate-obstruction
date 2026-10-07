import CountableScheffe

set_option autoImplicit false

open Filter Topology

namespace ActualInverseDoob

theorem tendsto_tsum_of_nonneg_of_mass_upper_bound
    {α ι : Type*} {l : Filter α} {f : α → ι → ℝ} {g : ι → ℝ} {b : α → ℝ}
    (hf_nonneg : ∀ a i, 0 ≤ f a i) (hg_nonneg : ∀ i, 0 ≤ g i)
    (hf : ∀ a, Summable (f a)) (hg : Summable g)
    (hpoint : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i)))
    (hbound : ∀ᶠ a in l, (∑' i, f a i) ≤ b a)
    (hb : Tendsto b l (𝓝 (∑' i, g i))) :
    Tendsto (fun a => ∑' i, f a i) l (𝓝 (∑' i, g i)) := by
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
  exact hmin_limit.squeeze' hb (Eventually.of_forall (fun a =>
    (hmin_sum a).tsum_le_tsum (fun i => min_le_left _ _) (hf a))) hbound

theorem tendsto_tsum_abs_sub_of_nonneg_of_mass_upper_bound
    {α ι : Type*} {l : Filter α} {f : α → ι → ℝ} {g : ι → ℝ} {b : α → ℝ}
    (hf_nonneg : ∀ a i, 0 ≤ f a i) (hg_nonneg : ∀ i, 0 ≤ g i)
    (hf : ∀ a, Summable (f a)) (hg : Summable g)
    (hpoint : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i)))
    (hbound : ∀ᶠ a in l, (∑' i, f a i) ≤ b a)
    (hb : Tendsto b l (𝓝 (∑' i, g i))) :
    Tendsto (fun a => ∑' i, |f a i - g i|) l (𝓝 0) :=
  tendsto_tsum_abs_sub_of_nonneg hf_nonneg hg_nonneg hf hg hpoint
    (tendsto_tsum_of_nonneg_of_mass_upper_bound
      hf_nonneg hg_nonneg hf hg hpoint hbound hb)

#print axioms tendsto_tsum_of_nonneg_of_mass_upper_bound
#print axioms tendsto_tsum_abs_sub_of_nonneg_of_mass_upper_bound

end ActualInverseDoob
