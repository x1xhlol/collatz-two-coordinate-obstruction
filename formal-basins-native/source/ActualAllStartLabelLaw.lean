import ActualOddLabelLaw
import LabelSubsetMass
import BanachOddFullMean
import Mathlib.Data.Nat.Factorization.Basic

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow CollatzCanonical.DirichletAbelian
variable {I : Type*}

noncomputable def oddPartLabel (F : ℕ → I) (q : ℕ) : I := F (ordCompl[2] q)

noncomputable def fullLabelLaw (F : ℕ → I) (t : ℝ) : LabelVector I :=
  (logarithmicCumulative (fun _ => 1) t)⁻¹ • fullVectorCumulative (labelAtom ∘ F) t

theorem oddPartLabel_eq_of_odd (F : ℕ → I) {q : ℕ} (hq : Odd q) :
    oddPartLabel F q = F q := by
  have hnot : ¬ 2 ∣ q := by
    simpa only [← even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hq)
  unfold oddPartLabel
  rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd q Nat.prime_two).mpr (Or.inr hnot)]

theorem oddPartLabel_double (F : ℕ → I) (q : ℕ) :
    oddPartLabel F (2 * q) = oddPartLabel F q := by
  unfold oddPartLabel
  rw [show 2 * q = 2 ^ 1 * q by simp, Nat.ordCompl_self_pow_mul q 1 Nat.prime_two]

theorem oddLabel_cumulative_oddPart (F : ℕ → I) (t : ℝ) :
    oddVectorCumulative (labelAtom ∘ oddPartLabel F) t =
      oddVectorCumulative (labelAtom ∘ F) t := by
  classical
  unfold oddVectorCumulative
  apply Finset.sum_congr rfl
  intro n _
  unfold oddVectorTerm
  split_ifs with hn
  · rw [Function.comp_apply, Function.comp_apply, oddPartLabel_eq_of_odd F (Nat.odd_iff.mpr hn)]
  · rfl

theorem full_harmonic_mass_ratio_tendsto :
    Tendsto (fun t => logarithmicCumulative (fun _ => 1) t / t) atTop (𝓝 (1:ℝ)) := by
  have hb : ∀ᶠ t : ℝ in atTop,
      |logarithmicCumulative (fun _ => 1) t / t - 1| ≤ 1 / t := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hlo := logarithmicCumulative_one_lower t
    have hhi := logarithmicCumulative_linear_bound (w := fun _ => 1)
      (fun _ => by norm_num) (fun _ => le_rfl) ht0.le
    have hnonneg : 0 ≤ logarithmicCumulative (fun _ => 1) t / t - 1 := by
      rw [sub_nonneg, le_div_iff₀ ht0, one_mul]
      exact hlo
    rw [abs_of_nonneg hnonneg]
    have hupper : logarithmicCumulative (fun _ => 1) t ≤ t + 1 :=
      (le_abs_self _).trans hhi
    rw [sub_le_iff_le_add, div_le_iff₀ ht0]
    field_simp
    linarith
  have hr : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hb hr)

theorem fullLabelLaw_tendsto_of_vector_mean (F : ℕ → I) (p : LabelVector I)
    (hp : Tendsto (fun t => t⁻¹ • fullVectorCumulative (labelAtom ∘ F) t) atTop (𝓝 p)) :
    Tendsto (fullLabelLaw F) atTop (𝓝 p) := by
  have hr := (full_harmonic_mass_ratio_tendsto.inv₀ (by norm_num)).smul hp
  simp only [inv_one, one_smul] at hr
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  unfold fullLabelLaw
  rw [smul_smul]
  congr 1
  have ht0 : t ≠ 0 := by linarith
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp

theorem actual_odd_and_all_start_label_law (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ p : LabelVector I, IsProbabilityVector p ∧
      Tendsto (oddLabelLaw F) atTop (𝓝 p) ∧
      Tendsto (fullLabelLaw (oddPartLabel F)) atTop (𝓝 p) := by
  have hv : EventuallyPassageInvariant (labelAtom ∘ F) := by
    filter_upwards [hpass] with x hx
    intro q hq τ hτ
    exact congrArg labelAtom (hx q hq τ hτ)
  obtain ⟨p, hp⟩ := actual_invariant_odd_vector_mean_exists (labelAtom ∘ F)
    (fun q => le_of_eq (labelAtom_norm (F q))) hv
  obtain ⟨hprob, hodd⟩ := odd_label_probability_of_vector_mean F p hp
  refine ⟨2 • p, hprob, hodd, ?_⟩
  apply fullLabelLaw_tendsto_of_vector_mean
  apply fullVector_mean_of_odd_mean (labelAtom ∘ oddPartLabel F)
    (fun q => le_of_eq (labelAtom_norm _))
    (fun q _ => congrArg labelAtom (oddPartLabel_double F q)) p
  simpa only [oddLabel_cumulative_oddPart] using hp

theorem actual_odd_and_all_start_label_PMF_law (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ μ : PMF I,
      Tendsto (fun t => ∑' i, |oddLabelLaw F t i - (μ i).toReal|) atTop (𝓝 0) ∧
      Tendsto (fun t => ∑' i, |fullLabelLaw (oddPartLabel F) t i - (μ i).toReal|)
        atTop (𝓝 0) := by
  obtain ⟨p, hp, hodd, hfull⟩ := actual_odd_and_all_start_label_law F hpass
  refine ⟨probabilityVectorPMF p hp, ?_, ?_⟩
  · simpa only [probabilityVectorPMF_toReal, labelVector_norm_eq_fullL1] using
      tendsto_iff_norm_sub_tendsto_zero.mp hodd
  · simpa only [probabilityVectorPMF_toReal, labelVector_norm_eq_fullL1] using
      tendsto_iff_norm_sub_tendsto_zero.mp hfull

theorem actual_label_law_uniform_over_subsets (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ p : LabelVector I, IsProbabilityVector p ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop, ∀ S : Set I,
        |labelSubsetMass S (oddLabelLaw F t) - labelSubsetMass S p| < ε ∧
        |labelSubsetMass S (fullLabelLaw (oddPartLabel F) t) - labelSubsetMass S p| < ε := by
  obtain ⟨p, hp, hodd, hfull⟩ := actual_odd_and_all_start_label_law F hpass
  refine ⟨p, hp, ?_⟩
  intro ε hε
  filter_upwards [labelSubsetMass_uniform_convergence hodd ε hε,
    labelSubsetMass_uniform_convergence hfull ε hε] with t ho hf
  exact fun S => ⟨ho S, hf S⟩

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.full_harmonic_mass_ratio_tendsto
#print axioms CollatzCanonical.LabelLaw.actual_odd_and_all_start_label_law
#print axioms CollatzCanonical.LabelLaw.actual_odd_and_all_start_label_PMF_law
#print axioms CollatzCanonical.LabelLaw.actual_label_law_uniform_over_subsets
