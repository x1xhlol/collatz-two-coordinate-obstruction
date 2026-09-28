import NaturalVectorMeans

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.NaturalPrefix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem fullNaturalPrefixSum_halving (F : ℕ → V) (X : ℕ) :
    fullNaturalPrefixSum F X = oddNaturalPrefixSum F X +
      fullNaturalPrefixSum (fun q => F (2 * q)) (X / 2) := by
  induction X with
  | zero => simp [fullNaturalPrefixSum, oddNaturalPrefixSum]
  | succ X ih =>
    have hmod : (X + 1) % 2 = 0 ∨ (X + 1) % 2 = 1 := by omega
    rcases hmod with heven | hodd
    · have hhalf : (X + 1) / 2 = X / 2 + 1 := by omega
      have htwice : 2 * (X / 2 + 1) = X + 1 := by omega
      simp only [fullNaturalPrefixSum, oddNaturalPrefixSum, Finset.sum_range_succ,
        heven, Nat.zero_ne_one, if_false, add_zero, hhalf, htwice] at ih ⊢
      rw [ih]
      abel
    · have hhalf : (X + 1) / 2 = X / 2 := by omega
      simp only [fullNaturalPrefixSum, oddNaturalPrefixSum, Finset.sum_range_succ,
        hodd, if_true, hhalf] at ih ⊢
      rw [ih]
      abel

theorem fullNaturalPrefixMean_norm_le_one {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    (X : ℕ) : ‖(X : ℝ)⁻¹ • fullNaturalPrefixSum F X‖ ≤ 1 := by
  simpa only [finiteVectorMean, Finset.card_range, fullNaturalPrefixSum] using
    finiteVectorMean_norm_le_one (fun q => hF (q + 1)) (Finset.range X)

theorem natural_half_ratio_error {X : ℕ} (hX : 0 < X) :
    |((X / 2 : ℕ) : ℝ) / X - (1 / 2 : ℝ)| ≤ (X : ℝ)⁻¹ := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hlo : 2 * (X / 2) ≤ X := by omega
  have hhi : X ≤ 2 * (X / 2) + 1 := by omega
  have hlo' : 2 * ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hlo
  have hhi' : (X : ℝ) ≤ 2 * ((X / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hhi
  have he : ((X / 2 : ℕ) : ℝ) / X - (1 / 2 : ℝ) =
      (((X / 2 : ℕ) : ℝ) - (X : ℝ) / 2) / X := by
    field_simp
  rw [he, abs_div, abs_of_pos hx, inv_eq_one_div]
  apply (div_le_div_iff_of_pos_right hx).mpr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms fullNaturalPrefixSum_halving
#print axioms natural_half_ratio_error

end CollatzCanonical.NaturalPrefix
