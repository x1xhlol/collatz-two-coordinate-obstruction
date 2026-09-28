import ActualComponentMass
import UniformOrbitCorrection

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.Correction CollatzCanonical.UniformCorrection
attribute [local instance] Classical.propDecidable

theorem shortcut_iterate_zero_start (j : ℕ) : iterate j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [iterate, ih, step]; norm_num

theorem shortcut_component_positive {q n : ℕ} (hn : 0 < n) (h : ShortcutTailRelated q n) :
    0 < q := by
  obtain ⟨i, j, hij⟩ := h
  by_contra hq
  have hq0 : q = 0 := by omega
  rw [hq0, shortcut_iterate_zero_start] at hij
  have hpos := CollatzCanonical.Correction.iterate_pos j hn
  omega

noncomputable def wholeOrbitCorrection (q : ℕ) : ℝ :=
  ∏' i : ℕ, (1 + oddCorrection (iterate i q))

theorem wholeOrbitCorrection_one_le {q : ℕ} (hq : 0 < q)
    (hinj : Function.Injective (fun i => iterate i q)) : 1 ≤ wholeOrbitCorrection q :=
  (orbit_product_bounds q (distinct_orbit_reciprocal_summable q hq hinj)).1

theorem exists_uniform_wholeOrbitCorrection_bound :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ q : ℕ, 0 < q → Function.Injective (fun i => iterate i q) →
      wholeOrbitCorrection q ≤ P := by
  obtain ⟨P, hP, _, hbound⟩ := exists_uniform_finite_and_infinite_product_bound
  exact ⟨P, hP, fun q hq hinj => (hbound q hq hinj).2.2⟩

theorem wholeOrbitCorrection_at_hit {q N A : ℕ} (hq : 0 < q)
    (hinj : Function.Injective (fun i => iterate i q)) (hA : iterate A q = N) :
    pathCorrection A q * wholeOrbitCorrection N = wholeOrbitCorrection q := by
  have h := distinct_orbit_product_prefix_tail q A hq hinj
  simpa only [hA, wholeOrbitCorrection, pathCorrection] using h

theorem wholeOrbitCorrection_forward_tendsto_one {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) :
    Tendsto (fun j => wholeOrbitCorrection (iterate j n)) atTop (𝓝 1) :=
  distinct_orbit_forward_product_tendsto_one n hn hinj

noncomputable def componentOrbitWeight (n q : ℕ) : ℝ :=
  if ShortcutTailRelated q n then (wholeOrbitCorrection q)⁻¹ else 0

noncomputable def truncatedComponentWeight (n j q : ℕ) : ℝ :=
  if ∃ a, iterate a q = iterate j n then componentOrbitWeight n q else 0

theorem componentOrbitWeight_bounds {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (q : ℕ) :
    0 ≤ componentOrbitWeight n q ∧ componentOrbitWeight n q ≤ componentIndicator n q := by
  by_cases hrel : ShortcutTailRelated q n
  · have hone := wholeOrbitCorrection_one_le (shortcut_component_positive hn hrel)
      (shortcut_component_injective hrel hinj)
    have hpos : 0 < wholeOrbitCorrection q := by linarith
    simp only [componentOrbitWeight, componentIndicator, if_pos hrel]
    exact ⟨(inv_pos.mpr hpos).le, inv_le_one_of_one_le₀ hone⟩
  · simp only [componentOrbitWeight, componentIndicator, if_neg hrel, le_refl, and_self]

theorem componentOrbitWeight_lower_bound {P : ℝ}
    (hbound : ∀ q : ℕ, 0 < q → Function.Injective (fun i => iterate i q) →
      wholeOrbitCorrection q ≤ P) {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (q : ℕ) :
    componentIndicator n q / P ≤ componentOrbitWeight n q := by
  by_cases hrel : ShortcutTailRelated q n
  · have hq := shortcut_component_positive hn hrel
    have hi := shortcut_component_injective hrel hinj
    have hone := wholeOrbitCorrection_one_le hq hi
    have hpos : 0 < wholeOrbitCorrection q := by linarith
    simp only [componentIndicator, componentOrbitWeight, if_pos hrel, one_div]
    exact inv_anti₀ hpos (hbound q hq hi)
  · simp only [componentIndicator, componentOrbitWeight, if_neg hrel, zero_div, le_refl]

theorem truncatedComponentWeight_eq_firstHit {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (j q : ℕ) :
    truncatedComponentWeight n j q = firstHitWeight (iterate j n) q /
      wholeOrbitCorrection (iterate j n) := by
  by_cases hhit : ∃ a, iterate a q = iterate j n
  · have hfirst := firstHit_find hhit
    have hrel : ShortcutTailRelated q n := ⟨Nat.find hhit, j, hfirst.1⟩
    have hq := shortcut_component_positive hn hrel
    have hi := shortcut_component_injective hrel hinj
    have hfactor := wholeOrbitCorrection_at_hit hq hi hfirst.1
    rw [truncatedComponentWeight, if_pos hhit, componentOrbitWeight, if_pos hrel,
      firstHitWeight_eq_pathWeight hfirst, pathWeight, ← hfactor, mul_inv, div_eq_mul_inv]
  · simp only [truncatedComponentWeight, if_neg hhit, firstHitWeight, dif_neg hhit, zero_div]

theorem truncatedComponentWeight_monotone {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (q : ℕ) :
    Monotone (fun j => truncatedComponentWeight n j q) := by
  intro i j hij
  by_cases hi : ∃ a, iterate a q = iterate i n
  · have hj := shortcut_basin_spine_monotone hij hi
    simp only [truncatedComponentWeight, if_pos hi, if_pos hj, le_refl]
  · simp only [truncatedComponentWeight, if_neg hi]
    split_ifs
    · exact (componentOrbitWeight_bounds hn hinj q).1
    · exact le_rfl

theorem truncatedComponentWeight_bounds {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (j q : ℕ) :
    0 ≤ truncatedComponentWeight n j q ∧
      truncatedComponentWeight n j q ≤ componentOrbitWeight n q := by
  unfold truncatedComponentWeight
  split_ifs
  · exact ⟨(componentOrbitWeight_bounds hn hinj q).1, le_rfl⟩
  · exact ⟨le_rfl, (componentOrbitWeight_bounds hn hinj q).1⟩

theorem component_weight_truncation_error {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (j q : ℕ) :
    componentOrbitWeight n q - truncatedComponentWeight n j q ≤
      componentIndicator n q - basinIndicator (iterate j n) q := by
  by_cases hh : ∃ a, iterate a q = iterate j n
  · obtain ⟨a, ha⟩ := hh
    have hrel : ShortcutTailRelated q n := ⟨a, j, ha⟩
    have hhit : ∃ a, iterate a q = iterate j n := ⟨a, ha⟩
    simp only [truncatedComponentWeight, if_pos hhit, componentIndicator, if_pos hrel,
      basinIndicator, sub_self, le_refl]
  · simp only [truncatedComponentWeight, if_neg hh, basinIndicator, sub_zero]
    exact (componentOrbitWeight_bounds hn hinj q).2

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.truncatedComponentWeight_eq_firstHit
#print axioms CollatzCanonical.ForwardComponent.component_weight_truncation_error
