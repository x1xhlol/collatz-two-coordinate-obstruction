import Erdos1135.Tao.Section6.HighRegimeMixing
import Erdos1135.Tao.Section6.AdjacentTelescope
import Erdos1135.Tao.Section6.InversePowerTail

/-!
# High-Regime To Large-Scale Mixing

This leaf combines adjacent high-regime estimates with the finite telescope
and shifted inverse-power tail.  It stops at the eventual large-lower-scale
bound, before the global small-scale fallback and Proposition 1.14 packaging.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Coefficient-one adjacent inverse-power estimates sum to the corresponding
lower-scale inverse-power estimate. -/
theorem syracFineScaleOscillation_le_of_adjacent_inverse_power
    {A m n : ℕ} {C : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hadj : ∀ r ∈ Finset.Ico m n,
      syracFineScaleOscillation r (r + 1) ≤
        C / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) :
    syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A := by
  calc
    syracFineScaleOscillation m n ≤
        ∑ r ∈ Finset.Ico m n,
          syracFineScaleOscillation r (r + 1) :=
      syracFineScaleOscillation_le_sum_adjacent hmn
    _ ≤ ∑ r ∈ Finset.Ico m n,
        C / (((r + 1 : ℕ) : ℝ) ^ (A + 1)) := by
      exact Finset.sum_le_sum hadj
    _ = C * (∑ r ∈ Finset.Ico m n,
        1 / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ C * (1 / (m : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_left
        (sum_Ico_one_div_succ_pow_le hA hm hmn) hC
    _ = C / (m : ℝ) ^ A := by ring

/-- Proposition 1.17 gives the all-upper-scale `m^(-A)` estimate once the
lower scale exceeds the source cutoff and the high-regime threshold. -/
theorem TaoProp117PrimitivePolynomialDecayStatement.exists_syracFineScaleOscillation_le_allScale_large
    (h117 : TaoProp117PrimitivePolynomialDecayStatement)
    (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M0 : ℕ, 10 ≤ M0 ∧
      ∀ n m : ℕ, M0 ≤ m → m ≤ n →
        syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A := by
  obtain ⟨C, hC, N0, hN0, hhigh⟩ :=
    h117.exists_syracFineScaleOscillation_le_highRegime A
  refine ⟨C, hC, max 10 N0, le_max_left 10 N0, ?_⟩
  intro n m hM0m hmn
  have hm : 1 ≤ m := by omega
  apply syracFineScaleOscillation_le_of_adjacent_inverse_power
    hA hC hm hmn
  intro r hr
  simp only [Finset.mem_Ico] at hr
  have hrTen : 10 ≤ r :=
    (le_max_left 10 N0).trans (hM0m.trans hr.1)
  apply hhigh (r + 1) r
  · exact (le_max_right 10 N0).trans
      (hM0m.trans (hr.1.trans (Nat.le_succ r)))
  · exact Nat.le_succ r
  · omega

/-- Exponent-one canary for the eventual large-scale theorem. -/
theorem TaoProp117PrimitivePolynomialDecayStatement.exists_syracFineScaleOscillation_le_allScale_large_one
    (h117 : TaoProp117PrimitivePolynomialDecayStatement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M0 : ℕ, 10 ≤ M0 ∧
      ∀ n m : ℕ, M0 ≤ m → m ≤ n →
        syracFineScaleOscillation m n ≤ C / (m : ℝ) := by
  simpa using
    h117.exists_syracFineScaleOscillation_le_allScale_large 1 (by omega)

/-- Empty, singleton, and lower-cutoff boundary canaries for a large-scale
rate family. -/
theorem syracFineScaleOscillation_largeScale_endpoint_canaries
    {A M0 : ℕ} {C : ℝ}
    (hlarge : ∀ n m : ℕ, M0 ≤ m → m ≤ n →
      syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A) :
    (∀ m : ℕ, M0 ≤ m →
      syracFineScaleOscillation m m ≤ C / (m : ℝ) ^ A) ∧
    (∀ m : ℕ, M0 ≤ m →
      syracFineScaleOscillation m (m + 1) ≤ C / (m : ℝ) ^ A) ∧
    (∀ n : ℕ, M0 ≤ n →
      syracFineScaleOscillation M0 n ≤ C / (M0 : ℝ) ^ A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    exact hlarge m m hm (le_refl m)
  · intro m hm
    exact hlarge (m + 1) m hm (Nat.le_succ m)
  · intro n hn
    exact hlarge n M0 (le_refl M0) hn

end

end Tao
end Erdos1135
