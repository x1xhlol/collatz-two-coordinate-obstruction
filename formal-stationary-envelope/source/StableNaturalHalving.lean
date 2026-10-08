import NaturalVectorMeans
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.NaturalPrefix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bounded contracting recurrence along integer halvings has zero limit
when its forcing term tends to zero. -/
theorem stable_natural_halving_tendsto_zero (E Z : ℕ → V) {d C : ℝ}
    (hd : 0 ≤ d) (hd1 : d < 1) (hbound : ∀ n, ‖E n‖ ≤ C)
    (hrec : ∀ n, E n = d • E (n / 2) + Z n)
    (hZ : Tendsto Z atTop (𝓝 0)) : Tendsto E atTop (𝓝 0) := by
  have hC : 0 ≤ C := (norm_nonneg (E 0)).trans (hbound 0)
  have herr (k : ℕ) : Tendsto (fun n : ℕ => E n - d ^ k • E (n / 2 ^ k)) atTop (𝓝 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hz := (hZ.comp (Nat.tendsto_div_const_atTop
        (pow_ne_zero k (by decide : (2 : ℕ) ≠ 0)))).const_smul (d ^ k)
      have hh := ih.add hz
      simp only [smul_zero, add_zero] at hh
      apply hh.congr'
      apply Filter.Eventually.of_forall
      intro n
      have he := hrec (n / 2 ^ k)
      have hdv : n / 2 ^ k / 2 = n / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
      rw [hdv] at he
      dsimp only [Function.comp_def]
      rw [he, pow_succ, smul_add, smul_smul]
      abel
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hpow : Tendsto (fun k : ℕ => d ^ k * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hd hd1).mul_const C
  obtain ⟨k, hk⟩ := (hpow.eventually_lt_const (half_pos hε)).exists
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (herr k) (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro n hn
  have herror : ‖E n - d ^ k • E (n / 2 ^ k)‖ < ε / 2 := by simpa using hN n hn
  have htail : ‖d ^ k • E (n / 2 ^ k)‖ ≤ d ^ k * C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hd _)]
    exact mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hd _)
  have hnorm := norm_add_le (E n - d ^ k • E (n / 2 ^ k)) (d ^ k • E (n / 2 ^ k))
  rw [sub_add_cancel] at hnorm
  rw [dist_eq_norm, sub_zero]
  linarith

#print axioms stable_natural_halving_tendsto_zero

end CollatzCanonical.NaturalPrefix
