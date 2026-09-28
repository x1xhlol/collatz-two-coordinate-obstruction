import LabelProbabilityVectors

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow CollatzCanonical.DirichletAbelian
variable {I : Type*}

noncomputable def labelSubsetMass (S : Set I) (p : LabelVector I) : ℝ :=
  ∑' i, S.indicator (fun i => p i) i

theorem labelSubsetMass_difference_le_fullL1 (S : Set I) (p q : LabelVector I) :
    |labelSubsetMass S p - labelSubsetMass S q| ≤ ‖p - q‖ := by
  classical
  have hp := (lp.memℓp p).summable_of_one
  have hq := (lp.memℓp q).summable_of_one
  have hd := (lp.memℓp (p - q)).summable_of_one
  have hn : Summable (fun i => |p i - q i|) := by
    simpa only [Real.norm_eq_abs, lp.coeFn_sub, Pi.sub_apply] using hd.norm
  have hSn : Summable (fun i => |S.indicator (fun i => p i - q i) i|) := by
    simpa only [Real.norm_eq_abs] using ((hp.sub hq).indicator S).norm
  have he : labelSubsetMass S p - labelSubsetMass S q =
      ∑' i, S.indicator (fun i => p i - q i) i := by
    unfold labelSubsetMass
    rw [← (hp.indicator S).tsum_sub (hq.indicator S)]
    apply tsum_congr
    intro i
    by_cases hi : i ∈ S <;> simp [hi]
  rw [he, labelVector_norm_eq_fullL1]
  calc
    _ ≤ ∑' i, |S.indicator (fun i => p i - q i) i| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm ((hp.sub hq).indicator S).norm
    _ ≤ _ := hSn.tsum_le_tsum (fun i => by
      by_cases hi : i ∈ S <;> simp [hi]) hn

theorem labelSubsetMass_uniform_convergence {L : ℝ → LabelVector I} {p : LabelVector I}
    (h : Tendsto L atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ S : Set I, |labelSubsetMass S (L t) - labelSubsetMass S p| < ε := by
  intro ε hε
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
  filter_upwards [hn.eventually_lt_const hε] with t ht
  intro S
  exact (labelSubsetMass_difference_le_fullL1 S (L t) p).trans_lt ht

theorem odd_harmonic_mass_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < oddLogarithmicCumulative (fun _ => 1) t := by
  have hf : 0 < ⌊Real.exp t⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr ht)
  unfold oddLogarithmicCumulative logarithmicCumulative
  apply Finset.sum_pos'
  · intro n _
    dsimp only
    split_ifs <;> positivity
  · refine ⟨0, Finset.mem_range.mpr hf, ?_⟩
    norm_num

theorem oddLabelLaw_isProbabilityVector (F : ℕ → I) {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityVector (oddLabelLaw F t) := by
  have hm := odd_harmonic_mass_pos ht
  constructor
  · intro i
    exact mul_nonneg (inv_nonneg.mpr hm.le) (oddLabel_cumulative_nonneg F t i)
  · change lp.tsumCLM ℝ I ℝ
      ((oddLogarithmicCumulative (fun _ => 1) t)⁻¹ •
        oddVectorCumulative (labelAtom ∘ F) t) = 1
    rw [map_smul, oddLabel_cumulative_mass]
    exact inv_mul_cancel₀ hm.ne'

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.labelSubsetMass_difference_le_fullL1
#print axioms CollatzCanonical.LabelLaw.labelSubsetMass_uniform_convergence
#print axioms CollatzCanonical.LabelLaw.oddLabelLaw_isProbabilityVector
