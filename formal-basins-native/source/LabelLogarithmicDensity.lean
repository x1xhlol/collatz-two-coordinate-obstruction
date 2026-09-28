import LabelHalvingInvariant
import LabelProbabilityTightness

set_option autoImplicit false
open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow CollatzCanonical.DirichletAbelian
variable {I : Type*}
attribute [local instance] Classical.propDecidable

theorem labelSubsetMass_smul (S : Set I) (c : ℝ) (p : LabelVector I) :
    labelSubsetMass S (c • p) = c * labelSubsetMass S p := by
  classical
  unfold labelSubsetMass
  have he (i : I) : S.indicator (fun i => (c • p) i) i =
      c * S.indicator (fun i => p i) i := by
    by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [he]
  exact tsum_mul_left

theorem labelSubsetMass_finset_sum {J : Type*} (s : Finset J) (P : J → LabelVector I)
    (S : Set I) : labelSubsetMass S (∑ j ∈ s, P j) = ∑ j ∈ s, labelSubsetMass S (P j) := by
  classical
  unfold labelSubsetMass
  have he (i : I) : S.indicator (fun i => (∑ j ∈ s, P j) i) i =
      ∑ j ∈ s, S.indicator (fun i => P j i) i := by
    by_cases hi : i ∈ S
    · simp only [Set.indicator_of_mem hi, lp.coeFn_sum, Finset.sum_apply]
    · simp only [Set.indicator_of_notMem hi, Finset.sum_const_zero]
  simp_rw [he]
  exact Summable.tsum_finsetSum (fun j _ => (lp.memℓp (P j)).summable_of_one.indicator S)

theorem labelSubsetMass_atom (S : Set I) (j : I) :
    labelSubsetMass S (labelAtom j) = if j ∈ S then 1 else 0 := by
  classical
  unfold labelSubsetMass
  have he (i : I) : S.indicator (fun i => labelAtom j i) i =
      if i = j then (if j ∈ S then (1 : ℝ) else 0) else 0 := by
    by_cases hij : i = j
    · subst i
      simp [labelAtom, Set.indicator_apply]
    · simp [Set.indicator_apply, labelAtom, Pi.single_apply, hij]
  simp_rw [he]
  simp

theorem labelSubsetMass_singleton (p : LabelVector I) (i : I) :
    labelSubsetMass {i} p = p i := by
  classical
  simp [labelSubsetMass, Set.indicator_apply]

theorem fullLabel_cumulative_subset_mass (F : ℕ → I) (S : Set I) (t : ℝ) :
    labelSubsetMass S (fullVectorCumulative (labelAtom ∘ F) t) =
      logarithmicCumulative (fun q => if F q ∈ S then 1 else 0) t := by
  classical
  unfold fullVectorCumulative logarithmicCumulative
  rw [labelSubsetMass_finset_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [labelSubsetMass_smul, Function.comp_apply, labelSubsetMass_atom]
  dsimp only
  split_ifs <;> simp

theorem fullLabelLaw_subset_mass (F : ℕ → I) (S : Set I) (t : ℝ) :
    labelSubsetMass S (fullLabelLaw F t) =
      logarithmicCumulative (fun q => if F q ∈ S then 1 else 0) t /
        logarithmicCumulative (fun _ => 1) t := by
  unfold fullLabelLaw
  rw [labelSubsetMass_smul, fullLabel_cumulative_subset_mass]
  ring

theorem labelSubsetMass_tendsto {L : ℝ → LabelVector I} {p : LabelVector I}
    (h : Tendsto L atTop (𝓝 p)) (S : Set I) :
    Tendsto (fun t => labelSubsetMass S (L t)) atTop (𝓝 (labelSubsetMass S p)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (Filter.Eventually.of_forall (fun t => ?_))
    (tendsto_iff_norm_sub_tendsto_zero.mp h)
  exact labelSubsetMass_difference_le_fullL1 S (L t) p

theorem full_label_law_logarithmic_mean {F : ℕ → I} {p : LabelVector I}
    (h : Tendsto (fullLabelLaw F) atTop (𝓝 p)) (S : Set I) :
    Tendsto (fun t => logarithmicCumulative (fun q => if F q ∈ S then 1 else 0) t / t)
      atTop (𝓝 (labelSubsetMass S p)) := by
  have hh := (labelSubsetMass_tendsto h S).mul full_harmonic_mass_ratio_tendsto
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [fullLabelLaw_subset_mass]
  have hm := (full_harmonic_mass_pos ht).ne'
  field_simp

theorem labelSubsetMass_nonneg {p : LabelVector I} (hp : IsProbabilityVector p) (S : Set I) :
    0 ≤ labelSubsetMass S p := by
  classical
  apply tsum_nonneg
  intro i
  by_cases hi : i ∈ S <;> simp [hi, hp.1 i]

theorem labelSubsetMass_le_one {p : LabelVector I} (hp : IsProbabilityVector p) (S : Set I) :
    labelSubsetMass S p ≤ 1 := by
  classical
  rw [← hp.2]
  apply ((lp.memℓp p).summable_of_one.indicator S).tsum_le_tsum
    (fun i => ?_) (lp.memℓp p).summable_of_one
  by_cases hi : i ∈ S <;> simp [hi, hp.1 i]

theorem labelSubsetMass_compl {p : LabelVector I} (hp : IsProbabilityVector p) (S : Set I) :
    labelSubsetMass Sᶜ p = 1 - labelSubsetMass S p := by
  classical
  have he : labelSubsetMass S p + labelSubsetMass Sᶜ p = 1 := by
    unfold labelSubsetMass
    rw [← ((lp.memℓp p).summable_of_one.indicator S).tsum_add
      ((lp.memℓp p).summable_of_one.indicator Sᶜ)]
    convert hp.2 using 1
    congr 1
    funext i
    by_cases hi : i ∈ S <;> simp [hi]
  linarith

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.full_label_law_logarithmic_mean
#print axioms CollatzCanonical.LabelLaw.labelSubsetMass_compl
