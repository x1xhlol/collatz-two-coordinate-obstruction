import UniformOrbitPacking
import FiniteReciprocalPacking

open scoped BigOperators

namespace CollatzUniformOrbitReciprocalPacking

open CollatzCylinderPacking CollatzCanonical.PackingParameters
open CollatzCanonical.ReciprocalPacking

/-- Every finite positive distinct shortcut path has the same reciprocal value-tail bound. -/
theorem uniform_finite_path_reciprocal_tail (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (L : ℕ) (x : ℕ → ℕ), 0 < x 0 →
      (∀ i, i + 1 < L → x (i + 1) = step (x i)) →
      Set.InjOn x (Finset.range L) →
      ∀ M : ℝ, 1 ≤ M →
        (∑ i ∈ (Finset.range L).filter (fun i => M ≤ (x i : ℝ)), 1 / (x i : ℝ)) ≤
          R * M ^ (b - 1) := by
  obtain ⟨K, hK, hcount⟩ := CollatzUniformOrbitPacking.uniform_finite_path_packing b hbβ hb1
  refine ⟨tailConstant K b, tailConstant_nonneg K b hK hb1, ?_⟩
  intro L x hx hpath hinj
  apply finite_indexed_reciprocal_tail (Finset.range L) x K b hK (beta_pos.trans hbβ) hb1 hinj
  intro X hX
  exact hcount L x hx hpath hinj X (zero_le_one.trans hX)

/-- Positivity propagates along every finite shortcut path. -/
theorem finite_path_positive (L : ℕ) (x : ℕ → ℕ) (hx : 0 < x 0)
    (hpath : ∀ i, i + 1 < L → x (i + 1) = step (x i)) :
    ∀ i, i < L → 0 < x i := by
  intro i
  induction i with
  | zero => intro _; exact hx
  | succ i ih =>
    intro hi
    rw [hpath i hi]
    exact CollatzOrbitPackingFiniteRecurrence.step_positive (ih (by omega))

/-- One constant controls both the whole reciprocal sum and every value tail of every finite path. -/
theorem uniform_finite_path_reciprocal_bounds (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (L : ℕ) (x : ℕ → ℕ), 0 < x 0 →
      (∀ i, i + 1 < L → x (i + 1) = step (x i)) →
      Set.InjOn x (Finset.range L) →
      (∑ i ∈ Finset.range L, 1 / (x i : ℝ)) ≤ R ∧
        ∀ M : ℝ, 1 ≤ M →
          (∑ i ∈ (Finset.range L).filter (fun i => M ≤ (x i : ℝ)), 1 / (x i : ℝ)) ≤
            R * M ^ (b - 1) := by
  obtain ⟨R, hR, htail⟩ := uniform_finite_path_reciprocal_tail b hbβ hb1
  refine ⟨R, hR, ?_⟩
  intro L x hx hpath hinj
  refine ⟨?_, htail L x hx hpath hinj⟩
  have ht := htail L x hx hpath hinj 1 le_rfl
  have he : (Finset.range L).filter (fun i => (1 : ℝ) ≤ (x i : ℝ)) = Finset.range L := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact_mod_cast finite_path_positive L x hx hpath i (Finset.mem_range.mp hi)
  simpa only [he, Real.one_rpow, mul_one] using ht

end CollatzUniformOrbitReciprocalPacking
