import ActualFinitePrefixTV

set_option autoImplicit false

open Filter Topology MeasureTheory ProbabilityTheory Preorder

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open CollatzCanonical.DirichletAbelian

def prefixEvent (k : ℕ) (E : Set (PrefixIndex k)) : Set (ℕ → ℕ) :=
  (frestrictLe (π := fun _ : ℕ => ℕ) k) ⁻¹' E

theorem measurableSet_prefixEvent (k : ℕ) (E : Set (PrefixIndex k)) :
    MeasurableSet (prefixEvent k E) :=
  (Set.to_countable E).measurableSet.preimage (measurable_frestrictLe k)

noncomputable def prefixEventSourceMass (n k : ℕ) (E : Set (PrefixIndex k)) (t : ℝ) : ℝ :=
  ∑' p, E.indicator (prefixSourceMass n k t) p

theorem prefixEvent_probability_tsum (n k : ℕ) (E : Set (PrefixIndex k)) :
    (pathLaw n (prefixEvent k E)).toReal =
      ∑' p, E.indicator (fun p => (finitePrefixPMF n k p).toReal) p := by
  haveI : IsProbabilityMeasure ((pathLaw n).map (frestrictLe (π := fun _ : ℕ => ℕ) k)) :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe k).aemeasurable
  have hμ : (finitePrefixPMF n k).toMeasure =
      (pathLaw n).map (frestrictLe (π := fun _ : ℕ => ℕ) k) := by
    exact Measure.toPMF_toMeasure _
  rw [prefixEvent, ← Measure.map_apply (measurable_frestrictLe k) (Set.to_countable E).measurableSet,
    ← hμ, (finitePrefixPMF n k).toMeasure_apply (Set.to_countable E).measurableSet,
    ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro p
    by_cases hp : p ∈ E
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, ENNReal.toReal_zero]
  · intro p
    by_cases hp : p ∈ E
    · simpa only [Set.indicator_of_mem hp] using (finitePrefixPMF n k).apply_ne_top p
    · rw [Set.indicator_of_notMem hp]
      exact ENNReal.zero_ne_top

theorem abs_tsum_indicator_sub_le {ι : Type*} (E : Set ι) {f g : ι → ℝ}
    (hf : Summable f) (hg : Summable g) :
    |(∑' i, E.indicator f i) - (∑' i, E.indicator g i)| ≤ ∑' i, |f i - g i| := by
  rw [← (hf.indicator E).tsum_sub (hg.indicator E)]
  have he : (fun i => E.indicator f i - E.indicator g i) = E.indicator (fun i => f i - g i) := by
    funext i
    by_cases hi : i ∈ E <;> simp [hi]
  rw [he]
  have hnorm := ((hf.sub hg).indicator E).norm
  calc
    _ ≤ ∑' i, ‖E.indicator (fun i => f i - g i) i‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, |f i - g i| := by
      apply hnorm.tsum_le_tsum _ (hf.sub hg).abs
      intro i
      by_cases hi : i ∈ E
      · simp only [Set.indicator_of_mem hi, Real.norm_eq_abs, le_refl]
      · simp only [Set.indicator_of_notMem hi, norm_zero, abs_nonneg]

theorem actual_prefix_event_source_limit {n : ℕ} (hn : 0 < n)
    (hu : n % 3 ≠ 0) (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (k : ℕ) (E : Set (PrefixIndex k)) :
    Tendsto (prefixEventSourceMass n k E) atTop (𝓝 (pathLaw n (prefixEvent k E)).toReal) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun t => norm_nonneg _)
    (fun t => ?_) (actual_fixed_prefix_total_variation hn hu hnodd hnp k)
  rw [Real.norm_eq_abs, prefixEventSourceMass, prefixEvent_probability_tsum]
  exact abs_tsum_indicator_sub_le E (prefixSourceMass_summable hnodd hnp t)
    (finitePrefixPMF_toReal_summable n k)

theorem finset_sum_le_of_unique_nonzero {ι : Type*} (S : Finset ι) (f : ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ i ∈ S, f i ≤ B)
    (hunique : ∀ i ∈ S, ∀ j ∈ S, f i ≠ 0 → f j ≠ 0 → i = j) :
    ∑ i ∈ S, f i ≤ B := by
  classical
  by_cases hex : ∃ i ∈ S, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := hex
    rw [Finset.sum_eq_single i]
    · exact hbound i hi
    · intro j hj hji
      by_contra hfj
      exact hji (hunique j hj i hi hfj hfi)
    · exact fun h => False.elim (h hi)
  · rw [Finset.sum_eq_zero (fun i hi => by by_contra h; exact hex ⟨i, hi, h⟩)]
    exact hB

theorem prefixSourceWeight_nonzero {n k q : ℕ} {p : PrefixIndex k}
    (h : prefixSourceWeight n k p q ≠ 0) :
    ValidPrefix n k (prefixExtend k p) ∧ ∃ B, iterate B q = prefixExtend k p k := by
  by_contra hbad
  exact h (if_neg hbad)

theorem prefixSourceWeight_event_sum_le {n k : ℕ} (hnodd : n % 2 = 1)
    (hnp : Nonperiodic n) (E : Set (PrefixIndex k)) (S : Finset (PrefixIndex k))
    (bad : ℕ → ℝ) (hbad : ∀ q, 0 ≤ bad q)
    (hdom : ∀ p ∈ E, ∀ q, prefixSourceWeight n k p q ≤ bad q) (q : ℕ) :
    ∑ p ∈ S, E.indicator (fun p => prefixSourceWeight n k p q) p ≤ bad q := by
  classical
  apply finset_sum_le_of_unique_nonzero S _ _ (hbad q)
  · intro p _
    by_cases hp : p ∈ E
    · simpa only [Set.indicator_of_mem hp] using hdom p hp q
    · simpa only [Set.indicator_of_notMem hp] using hbad q
  · intro p _ r _ hp hr
    have hpE : p ∈ E := by
      by_contra h
      exact hp (Set.indicator_of_notMem h _)
    have hrE : r ∈ E := by
      by_contra h
      exact hr (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hpE] at hp
    rw [Set.indicator_of_mem hrE] at hr
    have hp' := prefixSourceWeight_nonzero hp
    have hr' := prefixSourceWeight_nonzero hr
    exact prefixIndex_eq_of_common_ancestor hnodd hnp hp'.1 hr'.1 hp'.2 hr'.2

theorem prefixEventSourceMass_le_bad {n k : ℕ} (hnodd : n % 2 = 1)
    (hnp : Nonperiodic n) (E : Set (PrefixIndex k)) (bad : ℕ → ℝ)
    (hbad : ∀ q, 0 ≤ bad q)
    (hdom : ∀ p ∈ E, ∀ q, prefixSourceWeight n k p q ≤ bad q)
    {t : ℝ} (ht : 0 < t) :
    prefixEventSourceMass n k E t ≤ (2 / actualFirstHitDensity n) *
      (logarithmicCumulative bad t / t) := by
  apply ((prefixSourceMass_summable hnodd hnp t).indicator E).tsum_le_of_sum_le
  intro S
  have he : (∑ p ∈ S, E.indicator (prefixSourceMass n k t) p) =
      (2 / actualFirstHitDensity n) *
        (logarithmicCumulative (fun q =>
          ∑ p ∈ S, E.indicator (fun p => prefixSourceWeight n k p q) p) t / t) := by
    rw [logarithmicCumulative_sum, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ E
    · simp only [Set.indicator_of_mem hp, prefixSourceMass, if_pos ht]
    · simp only [Set.indicator_of_notMem hp, logarithmicCumulative, zero_div,
        Finset.sum_const_zero, mul_zero]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (actualFirstHitDensity_nonneg n))
  apply div_le_div_of_nonneg_right _ ht.le
  exact logarithmicCumulative_le_of_positive_weights
    (fun q _ => prefixSourceWeight_event_sum_le hnodd hnp E S bad hbad hdom q) t

/-- A source cumulative upper bound transfers to every fixed countable
prefix event under the actual normalized inverse law. -/
theorem actual_prefix_event_probability_le {n k : ℕ} (hn : 0 < n)
    (hu : n % 3 ≠ 0) (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (E : Set (PrefixIndex k)) (bad : ℕ → ℝ) (hbad : ∀ q, 0 ≤ bad q)
    (hdom : ∀ p ∈ E, ∀ q, prefixSourceWeight n k p q ≤ bad q)
    {B : ℝ} (hbound : ∀ᶠ t : ℝ in atTop, (2 / actualFirstHitDensity n) *
      (logarithmicCumulative bad t / t) ≤ B) :
    (pathLaw n (prefixEvent k E)).toReal ≤ B := by
  apply le_of_tendsto (actual_prefix_event_source_limit hn hu hnodd hnp k E)
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with t hb ht
  exact (prefixEventSourceMass_le_bad hnodd hnp E bad hbad hdom ht).trans hb

theorem actual_prefix_event_probability_le_of_eventual_add {n k : ℕ} (hn : 0 < n)
    (hu : n % 3 ≠ 0) (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (E : Set (PrefixIndex k)) (bad : ℕ → ℝ) (hbad : ∀ q, 0 ≤ bad q)
    (hdom : ∀ p ∈ E, ∀ q, prefixSourceWeight n k p q ≤ bad q)
    {B : ℝ} (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      (2 / actualFirstHitDensity n) * (logarithmicCumulative bad t / t) ≤ B + ε) :
    (pathLaw n (prefixEvent k E)).toReal ≤ B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact actual_prefix_event_probability_le hn hu hnodd hnp E bad hbad hdom (hbound ε hε)

end CollatzCylinderPacking.Arithmetic.InverseDoob
