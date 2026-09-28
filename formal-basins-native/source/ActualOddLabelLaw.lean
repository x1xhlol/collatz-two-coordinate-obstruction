import ActualInvariantVectorMean
import LabelProbabilityVectors

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow CollatzCanonical.DirichletAbelian

variable {I : Type*}

def EventuallyLabelPassageInvariant (F : ℕ → I) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ), Odd q → ∀ (τ : ℕ),
    Erdos1135.Tao.syracuseFirstHitAtMostReal x q τ →
      F q = F ((Erdos1135.Tao.syracuse^[τ]) q)

theorem odd_label_probability_of_vector_mean (F : ℕ → I) (p : LabelVector I)
    (hp : Tendsto (fun t => t⁻¹ • oddVectorCumulative (labelAtom ∘ F) t) atTop (𝓝 p)) :
    IsProbabilityVector ((2 : ℝ) • p) ∧
      Tendsto (oddLabelLaw F) atTop (𝓝 ((2 : ℝ) • p)) := by
  have hcoord (i : I) : 0 ≤ p i := by
    have hi := ((lp.evalCLM ℝ (fun _ : I => ℝ) 1 i).continuous.tendsto p).comp hp
    apply ge_of_tendsto hi
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact mul_nonneg (inv_nonneg.mpr ht) (oddLabel_cumulative_nonneg F t i)
  have hmass : lp.tsumCLM ℝ I ℝ p = (1 / 2 : ℝ) := by
    have hm := ((lp.tsumCLM ℝ I ℝ).continuous.tendsto p).comp hp
    have he : (fun t => lp.tsumCLM ℝ I ℝ
        (t⁻¹ • oddVectorCumulative (labelAtom ∘ F) t)) =
        (fun t => oddLogarithmicCumulative (fun _ => 1) t / t) := by
      funext t
      rw [map_smul, oddLabel_cumulative_mass]
      simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [Function.comp_def, he] at hm
    exact tendsto_nhds_unique hm odd_harmonic_mass_ratio_tendsto
  constructor
  · constructor
    · intro i
      exact mul_nonneg (by norm_num) (hcoord i)
    · change lp.tsumCLM ℝ I ℝ ((2:ℝ) • p) = 1
      rw [map_smul, hmass]
      norm_num
  · have hr := (odd_harmonic_mass_ratio_tendsto.inv₀ (by norm_num)).smul hp
    have hr' : Tendsto
        (fun t => (oddLogarithmicCumulative (fun _ => 1) t / t)⁻¹ •
          (t⁻¹ • oddVectorCumulative (labelAtom ∘ F) t)) atTop (𝓝 ((2:ℝ) • p)) := by
      simpa using hr
    apply hr'.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    unfold oddLabelLaw
    rw [smul_smul]
    congr 1
    have ht0 : t ≠ 0 := by linarith
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    field_simp

theorem actual_odd_label_probability_law (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ p : LabelVector I, IsProbabilityVector p ∧
      Tendsto (oddLabelLaw F) atTop (𝓝 p) ∧
      Tendsto (fun t => ∑' i, |oddLabelLaw F t i - p i|) atTop (𝓝 0) := by
  have hv : EventuallyPassageInvariant (labelAtom ∘ F) := by
    filter_upwards [hpass] with x hx
    intro q hq τ hτ
    exact congrArg labelAtom (hx q hq τ hτ)
  obtain ⟨p, hp⟩ := actual_invariant_odd_vector_mean_exists (labelAtom ∘ F)
    (fun q => le_of_eq (labelAtom_norm (F q))) hv
  obtain ⟨hprob, hlim⟩ := odd_label_probability_of_vector_mean F p hp
  refine ⟨2 • p, hprob, hlim, ?_⟩
  simpa only [labelVector_norm_eq_fullL1] using
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim)

noncomputable def probabilityVectorPMF (p : LabelVector I) (hp : IsProbabilityVector p) : PMF I :=
  ⟨fun i => ENNReal.ofReal (p i), by
    have he : ∑' i, ENNReal.ofReal (p i) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hp.1 (lp.memℓp p).summable_of_one, hp.2]
      simp
    exact Eq.mp (congrArg (fun s : ℝ≥0∞ => HasSum (fun i => ENNReal.ofReal (p i)) s) he)
      ENNReal.summable.hasSum⟩

theorem probabilityVectorPMF_toReal (p : LabelVector I) (hp : IsProbabilityVector p) (i : I) :
    (probabilityVectorPMF p hp i).toReal = p i := ENNReal.toReal_ofReal (hp.1 i)

theorem actual_odd_label_PMF_law (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ μ : PMF I,
      Tendsto (fun t => ∑' i, |oddLabelLaw F t i - (μ i).toReal|) atTop (𝓝 0) := by
  obtain ⟨p, hp, _, hlim⟩ := actual_odd_label_probability_law F hpass
  refine ⟨probabilityVectorPMF p hp, ?_⟩
  simpa only [probabilityVectorPMF_toReal] using hlim

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.odd_label_probability_of_vector_mean
#print axioms CollatzCanonical.LabelLaw.actual_odd_label_probability_law
#print axioms CollatzCanonical.LabelLaw.probabilityVectorPMF_toReal
#print axioms CollatzCanonical.LabelLaw.actual_odd_label_PMF_law
