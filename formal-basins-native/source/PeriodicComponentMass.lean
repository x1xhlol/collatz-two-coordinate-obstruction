import ActualComponentMass
import ShortcutPeriodicComponents

set_option autoImplicit false
open Filter Topology
open scoped BigOperators lp

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.LabelLaw CollatzCanonical.DirichletAbelian
attribute [local instance] Classical.propDecidable

def DivergentComponentsNull : Prop :=
  ∀ n : ℕ, Function.Injective (fun j => iterate j n) → actualComponentMass n = 0

noncomputable def eventuallyPeriodicIndicator (q : ℕ) : ℝ :=
  if ¬ Function.Injective (fun j => iterate j q) then 1 else 0

def EventuallyPeriodicDensityOne : Prop :=
  Tendsto (fun t => logarithmicCumulative eventuallyPeriodicIndicator t / t) atTop (𝓝 1)

theorem actual_eventually_periodic_logarithmic_mean :
    Tendsto (fun t => logarithmicCumulative eventuallyPeriodicIndicator t / t) atTop
      (𝓝 (labelSubsetMass periodicComponents actualShortcutTailLaw)) := by
  have h := full_label_law_logarithmic_mean actualShortcutTailLaw_spec.2.2 periodicComponents
  simpa only [mem_periodicComponents_iff, eventuallyPeriodicIndicator] using h

theorem labelSubsetMass_zero_iff {I : Type*} {p : LabelVector I} (hp : IsProbabilityVector p)
    (S : Set I) : labelSubsetMass S p = 0 ↔ ∀ i ∈ S, p i = 0 := by
  constructor
  · intro hzero i hi
    have hle := ((lp.memℓp p).summable_of_one.indicator S).le_tsum i
      (fun j _ => by by_cases hj : j ∈ S <;> simp [hj, hp.1 j])
    have hpi : p i ≤ labelSubsetMass S p := by
      simpa only [Set.indicator_of_mem hi] using hle
    rw [hzero] at hpi
    exact le_antisymm hpi (hp.1 i)
  · intro hzero
    have he : ∀ i, S.indicator (fun i => p i) i = 0 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [Set.indicator_of_mem hi, hzero i hi]
      · exact Set.indicator_of_notMem hi _
    simp only [labelSubsetMass, he, tsum_zero]

theorem divergentComponentsNull_iff_periodic_mass_one :
    DivergentComponentsNull ↔ labelSubsetMass periodicComponents actualShortcutTailLaw = 1 := by
  constructor
  · intro hnull
    have hzero : labelSubsetMass periodicComponentsᶜ actualShortcutTailLaw = 0 := by
      apply (labelSubsetMass_zero_iff actualShortcutTailLaw_spec.1 _).mpr
      intro C hC
      obtain ⟨n, rfl⟩ := Quotient.exists_rep C
      have hn : Function.Injective (fun j => iterate j n) := by
        by_contra h
        exact hC ⟨n, rfl, h⟩
      exact hnull n hn
    rw [labelSubsetMass_compl actualShortcutTailLaw_spec.1] at hzero
    linarith
  · intro hmass n hinj
    have hzero : labelSubsetMass periodicComponentsᶜ actualShortcutTailLaw = 0 := by
      rw [labelSubsetMass_compl actualShortcutTailLaw_spec.1, hmass, sub_self]
    apply (labelSubsetMass_zero_iff actualShortcutTailLaw_spec.1 _).mp hzero (shortcutTailLabel n)
    intro hmem
    exact (mem_periodicComponents_iff n).mp hmem hinj

theorem divergentComponentsNull_iff_eventuallyPeriodicDensityOne :
    DivergentComponentsNull ↔ EventuallyPeriodicDensityOne := by
  rw [divergentComponentsNull_iff_periodic_mass_one]
  constructor
  · intro h
    simpa only [h] using actual_eventually_periodic_logarithmic_mean
  · intro h
    exact tendsto_nhds_unique actual_eventually_periodic_logarithmic_mean h

theorem periodic_components_finite_mass_approx (hnull : DivergentComponentsNull)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ShortcutTailComponent,
      (∀ C ∈ s, C ∈ periodicComponents) ∧
        1 - ε < ∑ C ∈ s, actualShortcutTailLaw C := by
  classical
  have hmass := divergentComponentsNull_iff_periodic_mass_one.mp hnull
  let f : ShortcutTailComponent → ℝ := periodicComponents.indicator (fun C => actualShortcutTailLaw C)
  have hf : Summable f := (lp.memℓp actualShortcutTailLaw).summable_of_one.indicator periodicComponents
  have hsum : HasSum f 1 := by
    rw [← hmass]
    exact hf.hasSum
  have he : ∀ᶠ s : Finset ShortcutTailComponent in atTop, 1 - ε < ∑ C ∈ s, f C :=
    hsum.eventually_const_lt (by linarith)
  obtain ⟨s, hs⟩ := he.exists
  refine ⟨s.filter (fun C => C ∈ periodicComponents), ?_, ?_⟩
  · intro C hC
    exact (Finset.mem_filter.mp hC).2
  · simpa only [Finset.sum_filter, f, Set.indicator_apply] using hs

theorem labelSubsetMass_finset (s : Finset ShortcutTailComponent) :
    labelSubsetMass (s : Set ShortcutTailComponent) actualShortcutTailLaw =
      ∑ C ∈ s, actualShortcutTailLaw C := by
  classical
  unfold labelSubsetMass
  rw [tsum_eq_sum (s := s)]
  · apply Finset.sum_congr rfl
    intro C hC
    exact Set.indicator_of_mem hC _
  · intro C hC
    exact Set.indicator_of_notMem hC _

theorem actualBasinDensity_le_labelSubsetMass (v : ℕ) (S : Set ShortcutTailComponent)
    (hv : shortcutTailLabel v ∈ S) :
    actualBasinDensity v ≤ labelSubsetMass S actualShortcutTailLaw := by
  apply logarithmicMean_mono (actual_basin_full_logarithmic_mean v)
    (full_label_law_logarithmic_mean actualShortcutTailLaw_spec.2.2 S)
  intro q _
  by_cases hh : ∃ A, iterate A q = v
  · obtain ⟨A, hA⟩ := hh
    have he : shortcutTailLabel q = shortcutTailLabel v :=
      (shortcutTailLabel_eq_iff q v).mpr ⟨A, 0, hA⟩
    have hq : shortcutTailLabel q ∈ S := by rw [he]; exact hv
    rw [if_pos hq]
    exact (basinIndicator_bounds v q).2
  · simp only [basinIndicator, if_neg hh]
    split_ifs <;> norm_num

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.divergentComponentsNull_iff_eventuallyPeriodicDensityOne
#print axioms CollatzCanonical.ForwardComponent.periodic_components_finite_mass_approx
