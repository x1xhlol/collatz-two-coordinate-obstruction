import BanachFiniteProbability
import OddVectorWindows

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow CollatzCanonical.DirichletAbelian

abbrev LabelVector (I : Type*) := ℓ¹(I, ℝ)

noncomputable def labelAtom {I : Type*} (i : I) : LabelVector I := by
  classical
  exact lp.single 1 i 1

noncomputable def oddLabelLaw {I : Type*} (F : ℕ → I) (t : ℝ) : LabelVector I :=
  (oddLogarithmicCumulative (fun _ => 1) t)⁻¹ • oddVectorCumulative (labelAtom ∘ F) t

def IsProbabilityVector {I : Type*} (p : LabelVector I) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑' i, p i = 1

theorem labelAtom_norm {I : Type*} (i : I) : ‖labelAtom i‖ = 1 := by
  simp [labelAtom, lp.norm_single]

theorem labelAtom_nonneg {I : Type*} (i j : I) : 0 ≤ labelAtom i j := by
  classical
  simp [labelAtom, Pi.single_apply]
  split_ifs <;> norm_num

theorem labelAtom_mass {I : Type*} (i : I) : lp.tsumCLM ℝ I ℝ (labelAtom i) = 1 := by
  classical
  simp [labelAtom, lp.tsumCLM_apply]

theorem oddLabel_cumulative_mass {I : Type*} (F : ℕ → I) (t : ℝ) :
    lp.tsumCLM ℝ I ℝ (oddVectorCumulative (labelAtom ∘ F) t) =
      oddLogarithmicCumulative (fun _ => 1) t := by
  classical
  unfold oddVectorCumulative oddLogarithmicCumulative logarithmicCumulative
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold oddVectorTerm
  split_ifs with hn
  · simp only [map_smul, Function.comp_apply, labelAtom_mass, smul_eq_mul, mul_one,
      if_pos hn]
  · rw [map_zero]
    simp only [if_neg hn, zero_div]

theorem oddLabel_cumulative_nonneg {I : Type*} (F : ℕ → I) (t : ℝ) (i : I) :
    0 ≤ oddVectorCumulative (labelAtom ∘ F) t i := by
  classical
  unfold oddVectorCumulative
  rw [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_nonneg
  intro n _
  unfold oddVectorTerm
  split_ifs
  · exact mul_nonneg (by positivity) (labelAtom_nonneg (F (n+1)) i)
  · change (0 : ℝ) ≤ 0
    exact le_rfl

theorem odd_harmonic_mass_ratio_tendsto :
    Tendsto (fun t => oddLogarithmicCumulative (fun _ => 1) t / t)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hb : ∀ᶠ t : ℝ in atTop,
      |oddLogarithmicCumulative (fun _ => 1) t / t - 1 / 2| ≤ 2 / t := by
    filter_upwards [eventually_ge_atTop (max (Real.log 2) 1)] with t ht
    have ht0 : 0 < t := by linarith [le_max_right (Real.log 2) (1:ℝ)]
    have he := oddLogarithmicCumulative_one_bound ((le_max_left _ _).trans ht)
    rw [show oddLogarithmicCumulative (fun _ => 1) t / t - 1 / 2 =
      (oddLogarithmicCumulative (fun _ => 1) t - t / 2) / t by field_simp,
      abs_div, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right he ht0.le
  have hr : Tendsto (fun t : ℝ => 2 / t) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2:ℝ))).div_atTop tendsto_id
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr
    (squeeze_zero' (Filter.Eventually.of_forall (fun t => abs_nonneg _)) hb hr)

theorem labelVector_norm_eq_fullL1 {I : Type*} (p q : LabelVector I) :
    ‖p - q‖ = ∑' i, |p i - q i| := by
  simpa [lp.coeFn_sub, Real.norm_eq_abs] using
    lp.norm_eq_tsum_rpow (p := (1:ℝ≥0∞)) (by norm_num) (p - q)

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.labelAtom_mass
#print axioms CollatzCanonical.LabelLaw.oddLabel_cumulative_mass
#print axioms CollatzCanonical.LabelLaw.oddLabel_cumulative_nonneg
#print axioms CollatzCanonical.LabelLaw.odd_harmonic_mass_ratio_tendsto
#print axioms CollatzCanonical.LabelLaw.labelVector_norm_eq_fullL1
