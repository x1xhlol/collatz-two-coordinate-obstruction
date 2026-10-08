import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

noncomputable section

def sourceMean (w : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ q ∈ Finset.range X, w q) / (X : ℝ)

def adjacentVariation (w : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ q ∈ Finset.range X, |w (q + 1) - w q|

theorem periodic_zero_sum_prefix_bound (p : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hp : Function.Periodic p M) (hs : ∑ q ∈ Finset.range M, p q = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, |∑ q ∈ Finset.range X, p q| ≤ C := by
  let F : ℕ → ℝ := fun X => ∑ q ∈ Finset.range X, p q
  have hF : Function.Periodic F M := by
    intro X
    induction X with
    | zero => simpa [F] using hs
    | succ X ih =>
      change (∑ q ∈ Finset.range (X + 1 + M), p q) =
        ∑ q ∈ Finset.range (X + 1), p q
      rw [show X + 1 + M = (X + M) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, hp X]
      exact congrArg (fun a : ℝ => a + p X) ih
  refine ⟨∑ q ∈ Finset.range M, |p q|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro X
  change |F X| ≤ _
  rw [← hF.map_mod_nat X]
  exact (Finset.abs_sum_le_sum_abs p (Finset.range (X % M))).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_of_lt (Nat.mod_lt X hM)))
      (fun _ _ _ => abs_nonneg _))

theorem weighted_centered_sum_bound (w p : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ q, |w q| ≤ 1)
    (hp : ∀ X, |∑ q ∈ Finset.range X, p q| ≤ C) (X : ℕ) :
    |∑ q ∈ Finset.range X, w q * p q| ≤ C + C * adjacentVariation w X := by
  have hb := Finset.sum_range_by_parts w p X
  simp only [smul_eq_mul] at hb
  rw [hb]
  calc
    _ ≤ |w (X - 1) * ∑ q ∈ Finset.range X, p q| +
        |∑ q ∈ Finset.range (X - 1),
          (w (q + 1) - w q) * ∑ j ∈ Finset.range (q + 1), p j| := abs_sub _ _
    _ ≤ C + ∑ q ∈ Finset.range (X - 1), |w (q + 1) - w q| * C := by
      apply add_le_add
      · rw [abs_mul]
        exact (mul_le_mul (hw _) (hp _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul C)
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
    _ ≤ C + C * adjacentVariation w X := by
      rw [← Finset.sum_mul, mul_comm (∑ q ∈ Finset.range (X - 1), |w (q + 1) - w q|)]
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.sub_le X 1)) (fun _ _ _ => abs_nonneg _)

theorem centered_weighted_mean_tendsto_zero (w p : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hp : Function.Periodic p M) (hs : ∑ q ∈ Finset.range M, p q = 0)
    (hw : ∀ q, |w q| ≤ 1)
    (hvar : Tendsto (fun X => adjacentVariation w X / (X : ℝ)) atTop (𝓝 0)) :
    Tendsto (sourceMean (fun q => w q * p q)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hpC⟩ := periodic_zero_sum_prefix_bound p M hM hp hs
  have hupper : Tendsto (fun X : ℕ => C / (X : ℝ) + C *
      (adjacentVariation w X / (X : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat C).add (hvar.const_mul C)
  apply squeeze_zero_norm' _ hupper
  filter_upwards [] with X
  have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  rw [sourceMean, Real.norm_eq_abs, abs_div, abs_of_nonneg hX]
  have h := div_le_div_of_nonneg_right
    (weighted_centered_sum_bound w p C hC hw hpC X) (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
  simpa [add_div, mul_div_assoc] using h

theorem periodic_weighted_mean (w p : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hp : Function.Periodic p M) (hw : ∀ q, |w q| ≤ 1)
    (hvar : Tendsto (fun X => adjacentVariation w X / (X : ℝ)) atTop (𝓝 0))
    {d : ℝ} (hmean : Tendsto (sourceMean w) atTop (𝓝 d)) :
    Tendsto (sourceMean (fun q => w q * p q)) atTop
      (𝓝 (d * ((∑ q ∈ Finset.range M, p q) / (M : ℝ)))) := by
  let a : ℝ := (∑ q ∈ Finset.range M, p q) / (M : ℝ)
  have hcenter : Function.Periodic (fun q => p q - a) M := by
    intro q
    change p (q + M) - a = p q - a
    rw [hp q]
  have hsum : ∑ q ∈ Finset.range M, (p q - a) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    dsimp [a]
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hM.ne')]
    exact sub_self _
  have hz := centered_weighted_mean_tendsto_zero w (fun q => p q - a)
    M hM hcenter hsum hw hvar
  have h := hz.add (hmean.mul_const a)
  simp only [zero_add] at h
  convert h using 1
  funext X
  simp only [sourceMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem sourceMean_shift_sub (w : ℕ → ℝ) (X : ℕ) :
    sourceMean (fun q => w (q + 1)) X - sourceMean w X = (w X - w 0) / (X : ℝ) := by
  rw [sourceMean, sourceMean, ← sub_div, ← Finset.sum_sub_distrib, Finset.sum_range_sub]

theorem sourceMean_of_shift (w : ℕ → ℝ) (hw : ∀ q, |w q| ≤ 1)
    {d : ℝ} (hmean : Tendsto (sourceMean (fun q => w (q + 1))) atTop (𝓝 d)) :
    Tendsto (sourceMean w) atTop (𝓝 d) := by
  have hz : Tendsto (fun X : ℕ => (w X - w 0) / (X : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    filter_upwards [] with X
    have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hX]
    apply div_le_div_of_nonneg_right _ hX
    exact (abs_sub _ _).trans (by linarith [hw X, hw 0])
  have h := hmean.sub hz
  simp only [sub_zero] at h
  convert h using 1
  funext X
  have hs := sourceMean_shift_sub w X
  linarith

#print axioms periodic_weighted_mean
#print axioms sourceMean_of_shift

end
end CollatzCanonical.PeriodicCensusFloor
