import ArithmeticWordFibers
import CylinderExpansionBound

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

noncomputable def arithmeticTerm (k N : ℕ) (w : GeometricWord k) : ℝ := by
  classical
  exact if ValidWord k N w then (1 / 2 : ℝ) ^ wordLength k w else 0

noncomputable def arithmeticMass (k N : ℕ) : ℝ :=
  ∑' w : GeometricWord k, arithmeticTerm k N w

theorem arithmeticTerm_nonneg (k N : ℕ) (w : GeometricWord k) :
    0 ≤ arithmeticTerm k N w := by
  classical
  unfold arithmeticTerm
  split_ifs <;> positivity

theorem arithmeticTerm_le_probability (k N : ℕ) (w : GeometricWord k) :
    arithmeticTerm k N w ≤ (1 / 2 : ℝ) ^ wordLength k w := by
  classical
  unfold arithmeticTerm
  split_ifs
  · exact le_rfl
  · positivity

theorem arithmeticTerm_summable (k N : ℕ) : Summable (arithmeticTerm k N) :=
  Summable.of_nonneg_of_le (arithmeticTerm_nonneg k N)
    (arithmeticTerm_le_probability k N) (geometric_word_probability k).summable

noncomputable def arithmeticHeadTerm (k N : ℕ) (w : GeometricWord k) : ℝ := by
  classical
  exact if w ∈ headSet k N then (1 / 2 : ℝ) ^ wordLength k w else 0

theorem arithmeticHeadTerm_summable (k N : ℕ) : Summable (arithmeticHeadTerm k N) := by
  classical
  apply Summable.of_nonneg_of_le _ _ (geometric_word_probability k).summable
  · intro w
    unfold arithmeticHeadTerm
    split_ifs <;> positivity
  · intro w
    unfold arithmeticHeadTerm
    split_ifs
    · exact le_rfl
    · positivity

theorem arithmeticTerm_split (k N : ℕ) (w : GeometricWord k) :
    arithmeticTerm k N w = arithmeticHeadTerm k N w +
      filteredGeometricTail k (ValidWord k N) w := by
  classical
  by_cases hv : ValidWord k N w
  · by_cases hl : wordLength k w < 5 * k
    · simp [arithmeticTerm, arithmeticHeadTerm, filteredGeometricTail,
        geometricTailTerm, mem_headSet, hv, hl, Nat.not_le.mpr hl]
    · simp [arithmeticTerm, arithmeticHeadTerm, filteredGeometricTail,
        geometricTailTerm, mem_headSet, hv, hl, Nat.le_of_not_gt hl]
  · simp [arithmeticTerm, arithmeticHeadTerm, filteredGeometricTail, mem_headSet, hv]

theorem arithmeticHeadTerm_tsum (k N : ℕ) :
    (∑' w : GeometricWord k, arithmeticHeadTerm k N w) =
      ∑ w ∈ headSet k N, (1 / 2 : ℝ) ^ wordLength k w := by
  classical
  rw [tsum_eq_sum (s := headSet k N) (fun w hw => by simp [arithmeticHeadTerm, hw])]
  apply Finset.sum_congr rfl
  intro w hw
  simp [arithmeticHeadTerm, hw]

theorem arithmetic_head_fiberwise (k N : ℕ) :
    (∑ w ∈ headSet k N, (1 / 2 : ℝ) ^ wordLength k w) =
      ∑ i ∈ Finset.range (4 * k), ((tupleFiber k N (k + i)).card : ℝ) / 2 ^ (k + i) := by
  classical
  have hm : ∀ w ∈ headSet k N, wordLength k w - k ∈ Finset.range (4 * k) := by
    intro w hw
    have hl := ((mem_headSet k N w).mp hw).2
    have hg := wordLength_ge_depth k w
    apply Finset.mem_range.mpr
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun w => (1 / 2 : ℝ) ^ wordLength k w)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [headSet_fiber k N i (Finset.mem_range.mp hi)]
  calc
    (∑ w ∈ validFiber k N (k + i), (1 / 2 : ℝ) ^ wordLength k w) =
        ∑ _w ∈ validFiber k N (k + i), (1 / 2 : ℝ) ^ (k + i) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [((mem_validFiber k N (k + i) w).mp hw).1]
    _ = ((tupleFiber k N (k + i)).card : ℝ) / 2 ^ (k + i) := by
      rw [Finset.sum_const, nsmul_eq_mul, tupleFiber_card, one_div_pow]
      ring

/-- An identity for the directly defined, arithmetically admissible word law.
No stationary-measure or residue compatibility identity is assumed. -/
theorem arithmetic_mass_expansion (k N : ℕ) :
    arithmeticMass k N =
      (∑ i ∈ Finset.range (4 * k), ((tupleFiber k N (k + i)).card : ℝ) / 2 ^ (k + i)) +
      ∑' w : GeometricWord k, filteredGeometricTail k (ValidWord k N) w := by
  unfold arithmeticMass
  simp_rw [arithmeticTerm_split]
  rw [Summable.tsum_add (arithmeticHeadTerm_summable k N)
    (filtered_tail_summable k (ValidWord k N))]
  rw [arithmeticHeadTerm_tsum, arithmetic_head_fiberwise]

/-- Uniform upper bound for the actual arithmetic inverse-word law. -/
theorem arithmetic_mass_upper {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    arithmeticMass k N ≤ (2 * (k : ℝ) + 3) / (2 : ℝ) ^ k := by
  apply cylinder_bound_of_expansion k N (arithmeticMass k N)
    (fun i => tupleFiber k N (k + i)) (fun _ => tupleEndpoint N) (ValidWord k N)
  · intro i _ as ha
    exact tupleFiber_sum ha
  · intro i _ as ha
    exact tupleFiber_length ha
  · intro i _ as ha
    exact tupleFiber_admissible hk hN ha
  · exact arithmetic_mass_expansion k N

#print axioms arithmetic_mass_expansion
#print axioms arithmetic_mass_upper

end CollatzCylinderPacking.Arithmetic
