import UniformOrbitReciprocalPacking
import OrbitCorrectionProduct

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.UniformCorrection

open CollatzCylinderPacking CollatzCanonical.PackingParameters CollatzCanonical.Correction

/-- Correction factors of any finite family are bounded by one third of its reciprocal budget. -/
theorem finite_family_product_bounds {ι : Type*} (I : Finset ι) (x : ι → ℕ) :
    1 ≤ ∏ i ∈ I, (1 + oddCorrection (x i)) ∧
      (∏ i ∈ I, (1 + oddCorrection (x i))) ≤
        Real.exp ((1 / 3 : ℝ) * ∑ i ∈ I, (x i : ℝ)⁻¹) := by
  obtain ⟨hl, hu⟩ := finite_product_bounds (fun i => oddCorrection_nonneg (x i)) I
  refine ⟨hl, hu.trans (Real.exp_le_exp.mpr ?_)⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => oddCorrection_le_third_reciprocal (x i))

/-- Only odd source states need exceed the cutoff when bounding a correction product. -/
theorem finite_correction_sum_le_reciprocal_tail {ι : Type*} (I : Finset ι) (x : ι → ℕ)
    (M : ℝ) (hhigh : ∀ i ∈ I, x i % 2 = 1 → M ≤ (x i : ℝ)) :
    (∑ i ∈ I, oddCorrection (x i)) ≤
      (1 / 3 : ℝ) * ∑ i ∈ I.filter (fun i => M ≤ (x i : ℝ)), (x i : ℝ)⁻¹ := by
  classical
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hM : M ≤ (x i : ℝ)
  · rw [if_pos hM]
    exact oddCorrection_le_third_reciprocal (x i)
  · rw [if_neg hM]
    have he : x i % 2 ≠ 1 := fun ho => hM (hhigh i hi ho)
    simp only [oddCorrection, if_neg he, le_refl]

/-- One constant controls the correction product of every finite positive distinct shortcut path,
including the sharper estimate for paths whose odd source states all exceed a cutoff. -/
theorem uniform_finite_path_correction_bounds (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (L : ℕ) (x : ℕ → ℕ), 0 < x 0 →
      (∀ i, i + 1 < L → x (i + 1) = step (x i)) →
      Set.InjOn x (Finset.range L) →
      (1 ≤ ∏ i ∈ Finset.range L, (1 + oddCorrection (x i))) ∧
      (∏ i ∈ Finset.range L, (1 + oddCorrection (x i))) ≤ Real.exp (R / 3) ∧
      ∀ M : ℝ, 1 ≤ M → (∀ i, i < L → x i % 2 = 1 → M ≤ (x i : ℝ)) →
        (∏ i ∈ Finset.range L, (1 + oddCorrection (x i))) ≤
          Real.exp ((R / 3) * M ^ (b - 1)) := by
  obtain ⟨R, hR, hrecip⟩ :=
    CollatzUniformOrbitReciprocalPacking.uniform_finite_path_reciprocal_bounds b hbβ hb1
  refine ⟨R, hR, ?_⟩
  intro L x hx hpath hinj
  obtain ⟨hfull, htail⟩ := hrecip L x hx hpath hinj
  simp only [one_div] at hfull htail
  obtain ⟨hlo, hup⟩ := finite_family_product_bounds (Finset.range L) x
  refine ⟨hlo, hup.trans (Real.exp_le_exp.mpr (by linarith)), ?_⟩
  intro M hM hhigh
  have hsum := finite_correction_sum_le_reciprocal_tail (Finset.range L) x M
    (fun i hi => hhigh i (Finset.mem_range.mp hi))
  have hbudget := mul_le_mul_of_nonneg_left (htail M hM) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hp := (finite_product_bounds (fun i => oddCorrection_nonneg (x i)) (Finset.range L)).2
  apply hp.trans (Real.exp_le_exp.mpr ?_)
  exact hsum.trans (hbudget.trans_eq (by ring))

/-- A single numerical constant bounds every finite positive distinct-path correction product. -/
theorem exists_uniform_finite_path_product_bound :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ (L : ℕ) (x : ℕ → ℕ), 0 < x 0 →
      (∀ i, i + 1 < L → x (i + 1) = step (x i)) →
      Set.InjOn x (Finset.range L) →
      1 ≤ ∏ i ∈ Finset.range L, (1 + oddCorrection (x i)) ∧
        (∏ i ∈ Finset.range L, (1 + oddCorrection (x i))) ≤ P₀ := by
  obtain ⟨b, hbβ, hb1⟩ := exists_between beta_lt_one
  obtain ⟨R, hR, hbound⟩ := uniform_finite_path_correction_bounds b hbβ hb1
  refine ⟨Real.exp (R / 3), Real.one_le_exp_iff.mpr (by positivity), ?_⟩
  intro L x hx hpath hinj
  have hh := hbound L x hx hpath hinj
  exact ⟨hh.1, hh.2.1⟩

/-- Distinct positive infinite orbits inherit a uniform reciprocal sum and every value-tail budget. -/
theorem uniform_distinct_orbit_reciprocal_bounds (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ N : ℕ, 0 < N →
      Function.Injective (fun i => iterate i N) →
      Summable (fun i => (iterate i N : ℝ)⁻¹) ∧
      (∑' i, (iterate i N : ℝ)⁻¹) ≤ R ∧
      ∀ M : ℝ, 1 ≤ M →
        (∑' i, if M ≤ (iterate i N : ℝ) then (iterate i N : ℝ)⁻¹ else 0) ≤
          R * M ^ (b - 1) := by
  obtain ⟨R, hR, hbound⟩ :=
    CollatzUniformOrbitReciprocalPacking.uniform_finite_path_reciprocal_bounds b hbβ hb1
  refine ⟨R, hR, ?_⟩
  intro N hN hinj
  have hnonneg (i : ℕ) : 0 ≤ (iterate i N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hprefix (L : ℕ) : (∑ i ∈ Finset.range L, (iterate i N : ℝ)⁻¹) ≤ R := by
    have hh := (hbound L (fun i => iterate i N) hN (fun i _ => rfl) hinj.injOn).1
    simpa only [one_div] using hh
  have hs := summable_of_sum_range_le hnonneg hprefix
  refine ⟨hs, Real.tsum_le_of_sum_range_le hnonneg hprefix, ?_⟩
  intro M hM
  apply Real.tsum_le_of_sum_range_le
  · intro i
    split_ifs <;> positivity
  · intro L
    have hh := (hbound L (fun i => iterate i N) hN (fun i _ => rfl) hinj.injOn).2 M hM
    simpa only [one_div, Finset.sum_filter] using hh

/-- Reciprocal summability is a consequence of distinctness, not a separate infinite-orbit premise. -/
theorem distinct_orbit_reciprocal_summable (N : ℕ) (hN : 0 < N)
    (hinj : Function.Injective (fun i => iterate i N)) :
    Summable (fun i => (iterate i N : ℝ)⁻¹) := by
  obtain ⟨b, hbβ, hb1⟩ := exists_between beta_lt_one
  obtain ⟨R, hR, hbound⟩ := uniform_distinct_orbit_reciprocal_bounds b hbβ hb1
  exact (hbound N hN hinj).1

/-- The correction infinite product of a distinct positive orbit is an actual convergent product. -/
theorem distinct_orbit_correction_hasProd (N : ℕ) (hN : 0 < N)
    (hinj : Function.Injective (fun i => iterate i N)) :
    HasProd (fun i => 1 + oddCorrection (iterate i N))
      (∏' i, (1 + oddCorrection (iterate i N))) := by
  have hs := distinct_orbit_reciprocal_summable N hN hinj
  have hc := orbit_corrections_summable N hs
  have hl := summable_log_correction (fun i => oddCorrection_nonneg (iterate i N)) hc
  rw [product_eq_exp_sum (fun i => oddCorrection_nonneg (iterate i N)) hc]
  have heq : (Real.exp ∘ fun i => Real.log (1 + oddCorrection (iterate i N))) =
      (fun i => 1 + oddCorrection (iterate i N)) := by
    funext i
    exact Real.exp_log (by linarith [oddCorrection_nonneg (iterate i N)])
  simpa only [heq] using hl.hasSum.rexp

/-- Finite correction products converge to the positive infinite-orbit correction. -/
theorem distinct_orbit_correction_prefix_tendsto (N : ℕ) (hN : 0 < N)
    (hinj : Function.Injective (fun i => iterate i N)) :
    Tendsto (fun L => ∏ i ∈ Finset.range L, (1 + oddCorrection (iterate i N))) atTop
      (𝓝 (∏' i, (1 + oddCorrection (iterate i N)))) :=
  (distinct_orbit_correction_hasProd N hN hinj).tendsto_prod_nat

/-- The same absolute constant controls all finite paths and all positive distinct infinite orbits. -/
theorem exists_uniform_finite_and_infinite_product_bound :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧
      (∀ (L : ℕ) (x : ℕ → ℕ), 0 < x 0 →
        (∀ i, i + 1 < L → x (i + 1) = step (x i)) →
        Set.InjOn x (Finset.range L) →
        1 ≤ ∏ i ∈ Finset.range L, (1 + oddCorrection (x i)) ∧
          (∏ i ∈ Finset.range L, (1 + oddCorrection (x i))) ≤ P₀) ∧
      ∀ N : ℕ, 0 < N → Function.Injective (fun i => iterate i N) →
        HasProd (fun i => 1 + oddCorrection (iterate i N))
          (∏' i, (1 + oddCorrection (iterate i N))) ∧
        1 ≤ ∏' i, (1 + oddCorrection (iterate i N)) ∧
          (∏' i, (1 + oddCorrection (iterate i N))) ≤ P₀ := by
  obtain ⟨P₀, hP₀, hfinite⟩ := exists_uniform_finite_path_product_bound
  refine ⟨P₀, hP₀, hfinite, ?_⟩
  intro N hN hinj
  have hs := distinct_orbit_reciprocal_summable N hN hinj
  refine ⟨distinct_orbit_correction_hasProd N hN hinj, (orbit_product_bounds N hs).1, ?_⟩
  apply le_of_tendsto (distinct_orbit_correction_prefix_tendsto N hN hinj)
  exact Eventually.of_forall (fun L =>
    (hfinite L (fun i => iterate i N) hN (fun i _ => rfl) hinj.injOn).2)

/-- Correction products factor exactly at every forward time, without an extra summability assumption. -/
theorem distinct_orbit_product_prefix_tail (N j : ℕ) (hN : 0 < N)
    (hinj : Function.Injective (fun i => iterate i N)) :
    (∏ i ∈ Finset.range j, (1 + oddCorrection (iterate i N))) *
      (∏' i, (1 + oddCorrection (iterate i (iterate j N)))) =
        ∏' i, (1 + oddCorrection (iterate i N)) :=
  orbit_product_prefix_tail N j (distinct_orbit_reciprocal_summable N hN hinj)

/-- The whole-orbit correction tends to one along the forward spine of a distinct orbit. -/
theorem distinct_orbit_forward_product_tendsto_one (N : ℕ) (hN : 0 < N)
    (hinj : Function.Injective (fun i => iterate i N)) :
    Tendsto (fun j => ∏' i, (1 + oddCorrection (iterate i (iterate j N)))) atTop (𝓝 1) :=
  forward_orbit_product_tendsto_one N (distinct_orbit_reciprocal_summable N hN hinj)

end CollatzCanonical.UniformCorrection
