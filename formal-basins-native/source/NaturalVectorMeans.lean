import Erdos1135.ND.Conventions
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.NaturalPrefix
open Erdos1135

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def finiteVectorMean (s : Finset ℕ) (F : ℕ → V) : V :=
  (s.card : ℝ)⁻¹ • ∑ q ∈ s, F q

noncomputable def naturalOddVectorBlockMean (F : ℕ → V) (y : ℝ) : V :=
  finiteVectorMean (ND.oddBlock y) F

def oddNaturalPrefix (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun q => q % 2 = 1)

noncomputable def oddNaturalPrefixSum (F : ℕ → V) (X : ℕ) : V :=
  ∑ n ∈ Finset.range X, if (n + 1) % 2 = 1 then F (n + 1) else 0

noncomputable def fullNaturalPrefixSum (F : ℕ → V) (X : ℕ) : V :=
  ∑ n ∈ Finset.range X, F (n + 1)

omit [NormedSpace ℝ V] in
theorem oddNaturalPrefixSum_eq_sum (F : ℕ → V) (X : ℕ) :
    oddNaturalPrefixSum F X = ∑ q ∈ oddNaturalPrefix X, F q := by
  rw [oddNaturalPrefix, Finset.sum_filter, Finset.sum_range_succ']
  simp only [Nat.zero_mod, Nat.zero_ne_one, if_false, add_zero]
  rfl

theorem finiteVectorMean_norm_le_one {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    (s : Finset ℕ) : ‖finiteVectorMean s F‖ ≤ 1 := by
  classical
  by_cases hs : s.Nonempty
  · have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
    have hb : ‖∑ q ∈ s, F q‖ ≤ (s.card : ℝ) := by
      apply (norm_sum_le _ _).trans
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
        Finset.sum_le_sum (fun q (_ : q ∈ s) => hF q)
    unfold finiteVectorMean
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      _ ≤ (s.card : ℝ)⁻¹ * (s.card : ℝ) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ hc.ne'
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [finiteVectorMean, he]

theorem finiteVectorMean_card_smul (s : Finset ℕ) (F : ℕ → V) :
    (s.card : ℝ) • finiteVectorMean s F = ∑ q ∈ s, F q := by
  classical
  by_cases hs : s.Nonempty
  · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hs).ne'
    rw [finiteVectorMean, smul_smul, mul_inv_cancel₀ hc, one_smul]
  · simp [finiteVectorMean, Finset.not_nonempty_iff_eq_empty.mp hs]

theorem oddNaturalPrefix_card (X : ℕ) : (oddNaturalPrefix X).card = (X + 1) / 2 := by
  rw [oddNaturalPrefix, ← Nat.count_eq_card_filter_range]
  have h := Nat.count_modEq_card (X + 1) (by omega : 0 < 2) 1
  have hnmod : ¬ 1 < (X + 1) % 2 := by omega
  simpa [Nat.ModEq, hnmod] using h

theorem oddNaturalPrefix_mem {X q : ℕ} :
    q ∈ oddNaturalPrefix X ↔ q ≤ X ∧ q % 2 = 1 := by
  simp only [oddNaturalPrefix, Finset.mem_filter, Finset.mem_range]
  omega

theorem oddNaturalPrefix_card_error (X : ℕ) :
    |((oddNaturalPrefix X).card : ℝ) - (X : ℝ) / 2| ≤ 1 := by
  have hnlo : X ≤ 2 * (oddNaturalPrefix X).card := by rw [oddNaturalPrefix_card]; omega
  have hnhi : 2 * (oddNaturalPrefix X).card ≤ X + 1 := by rw [oddNaturalPrefix_card]; omega
  have hlo : (X : ℝ) ≤ 2 * ((oddNaturalPrefix X).card : ℝ) := by exact_mod_cast hnlo
  have hhi : 2 * ((oddNaturalPrefix X).card : ℝ) ≤ (X : ℝ) + 1 := by exact_mod_cast hnhi
  apply abs_le.mpr
  constructor <;> linarith

#print axioms finiteVectorMean_norm_le_one
#print axioms oddNaturalPrefix_card_error

end CollatzCanonical.NaturalPrefix
