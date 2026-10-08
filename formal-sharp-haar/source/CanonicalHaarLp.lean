import CanonicalLpInterpolation
import CanonicalHaarEnergy
import CanonicalHaarLimitIdentification
import HarmonicFiberBounds

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

noncomputable def canonicalHaarDifference (k : ℕ) (x : ℤ_[3]) : ℝ :=
  canonicalPadicRho (k + 1) x - canonicalPadicRho k x

theorem canonicalHaarDifference_memLp (k : ℕ) (p : ℝ≥0∞) :
    MemLp (canonicalHaarDifference k) p padicThreeHaar :=
  (canonicalPadicRho_memLp (k + 1) p).sub (canonicalPadicRho_memLp k p)

theorem canonicalHaarDifference_sq_integral_le (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℤ_[3], (canonicalHaarDifference k x) ^ 2 ∂padicThreeHaar) ≤
      320 * (k : ℝ) ^ 2 := by
  have hnext := (canonicalPadicRho_memLp (k + 1) 2).integrable_sq
  have hcur := (canonicalPadicRho_memLp k 2).integrable_sq
  have hdiff := (canonicalHaarDifference_memLp k 2).integrable_sq
  calc
    _ ≤ ∫ x : ℤ_[3], 2 * ((canonicalPadicRho (k + 1) x) ^ 2 +
        (canonicalPadicRho k x) ^ 2) ∂padicThreeHaar := by
      apply integral_mono hdiff ((hnext.add hcur).const_mul 2)
      intro x
      simp only [canonicalHaarDifference, Pi.add_apply]
      nlinarith [sq_nonneg (canonicalPadicRho (k + 1) x + canonicalPadicRho k x)]
    _ = 2 * ((∫ x : ℤ_[3], (canonicalPadicRho (k + 1) x) ^ 2 ∂padicThreeHaar) +
        ∫ x : ℤ_[3], (canonicalPadicRho k x) ^ 2 ∂padicThreeHaar) := by
      rw [integral_const_mul, integral_add hnext hcur]
    _ ≤ 320 * (k : ℝ) ^ 2 := by
      have hn := canonicalPadicRho_sq_integral_le_thirtytwo_quadratic (k + 1) (by omega)
      have hc := canonicalPadicRho_sq_integral_le_thirtytwo_quadratic k hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at hn
      nlinarith [sq_nonneg ((k : ℝ) - 1)]

theorem exists_canonicalHaarDifference_first_moment_bound (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      (∫ x : ℤ_[3], |canonicalHaarDifference k x| ∂padicThreeHaar) ≤
        C / (k : ℝ) ^ A := by
  obtain ⟨C, hC, hmix⟩ := taoProp114FineScaleMixing.bound hA
  refine ⟨C, hC, fun k hk => ?_⟩
  change (∫ x : ℤ_[3], |canonicalPadicRho (k + 1) x - canonicalPadicRho k x|
    ∂padicThreeHaar) ≤ _
  rw [canonicalPadicRho_twoScale_error (by omega : k ≤ k + 1)]
  exact hmix (k + 1) k hk (by omega)

theorem exists_canonicalHaarDifference_eLpNorm_bound {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k : ℕ, 1 ≤ k →
      eLpNorm (canonicalHaarDifference k) (ENNReal.ofReal p) padicThreeHaar ≤
        ENNReal.ofReal (D / (k : ℝ) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have ha : 0 < (2 - p) / p := div_pos (by linarith) hp0
  obtain ⟨A, hA⟩ := exists_nat_gt ((2 + 2 * ((p - 1) / p)) / ((2 - p) / p))
  have hlarge : 2 * ((p - 1) / p) - (A : ℝ) * ((2 - p) / p) ≤ -2 := by
    have := (div_lt_iff₀ ha).mp hA
    linarith
  have hA0 : 0 < A := by
    have hb : 0 < (p - 1) / p := div_pos (by linarith) hp0
    have : (0 : ℝ) < A := lt_trans (div_pos (by positivity) ha) hA
    exact_mod_cast this
  obtain ⟨C, hC, hfirst⟩ := exists_canonicalHaarDifference_first_moment_bound A hA0
  refine ⟨C ^ ((2 - p) / p) * (320 : ℝ) ^ ((p - 1) / p),
    mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  refine (eLpNorm_le_real_moment_bounds
    (memLp_one_iff_integrable.mp (canonicalHaarDifference_memLp k 1))
    (canonicalHaarDifference_memLp k 2).integrable_sq hp hp2
    (div_nonneg hC (pow_nonneg hk0 _)) (by positivity)
    (hfirst k hk) (canonicalHaarDifference_sq_integral_le k hk)).trans ?_
  exact ENNReal.ofReal_le_ofReal
    (polynomial_interpolation_le_inverse_square hC (by norm_num) hk1 hlarge)

theorem exists_canonicalPadicRho_uniform_eLpNorm_bound {p : ℝ}
    (hp : 1 < p) (hp2 : p < 2) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ n : ℕ, 1 ≤ n →
      eLpNorm (canonicalPadicRho n) (ENNReal.ofReal p) padicThreeHaar ≤ B := by
  obtain ⟨D, hD, hdiff⟩ := exists_canonicalHaarDifference_eLpNorm_bound hp hp2
  refine ⟨eLpNorm (canonicalPadicRho 1) (ENNReal.ofReal p) padicThreeHaar +
    ENNReal.ofReal (2 * D), ENNReal.add_lt_top.mpr
      ⟨(canonicalPadicRho_memLp 1 _).eLpNorm_lt_top, ENNReal.ofReal_lt_top⟩, ?_⟩
  intro n hn
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have htel : canonicalPadicRho n = canonicalPadicRho 1 +
      ∑ k ∈ Finset.Ico 1 n, canonicalHaarDifference k := by
    funext x
    have h := Finset.sum_Ico_sub (f := fun k => canonicalPadicRho k x) hn
    simp only [Pi.add_apply, Finset.sum_apply, canonicalHaarDifference]
    linarith
  have hsum : (∑ k ∈ Finset.Ico 1 n, ENNReal.ofReal (D / (k : ℝ) ^ 2)) ≤
      ENNReal.ofReal (2 * D) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => div_nonneg hD (sq_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    simp_rw [div_eq_mul_inv]
    rw [← Finset.mul_sum]
    have h := FairEnergy.sum_inverse_square_Ico_le 1 n (by omega)
    simp only [Nat.cast_one, div_one, one_div] at h
    nlinarith
  calc
    _ = eLpNorm (canonicalPadicRho 1 + ∑ k ∈ Finset.Ico 1 n, canonicalHaarDifference k)
        (ENNReal.ofReal p) padicThreeHaar := by rw [← htel]
    _ ≤ eLpNorm (canonicalPadicRho 1) (ENNReal.ofReal p) padicThreeHaar +
        eLpNorm (∑ k ∈ Finset.Ico 1 n, canonicalHaarDifference k)
          (ENNReal.ofReal p) padicThreeHaar :=
      eLpNorm_add_le (canonicalPadicRho_memLp 1 1).aestronglyMeasurable
        (Finset.aestronglyMeasurable_sum _ fun k _ =>
          (canonicalHaarDifference_memLp k 1).aestronglyMeasurable) hp1
    _ ≤ eLpNorm (canonicalPadicRho 1) (ENNReal.ofReal p) padicThreeHaar +
        ∑ k ∈ Finset.Ico 1 n, eLpNorm (canonicalHaarDifference k)
          (ENNReal.ofReal p) padicThreeHaar := by
      gcongr
      exact eLpNorm_sum_le (fun k _ =>
        (canonicalHaarDifference_memLp k 1).aestronglyMeasurable) hp1
    _ ≤ eLpNorm (canonicalPadicRho 1) (ENNReal.ofReal p) padicThreeHaar +
        ∑ k ∈ Finset.Ico 1 n, ENNReal.ofReal (D / (k : ℝ) ^ 2) := by
      gcongr with k hk
      exact hdiff k (Finset.mem_Ico.mp hk).1
    _ ≤ _ := add_le_add le_rfl hsum

theorem canonicalPadicRho_tendstoInMeasure :
    TendstoInMeasure padicThreeHaar canonicalPadicRho atTop canonicalHaarDensity := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    (fun n => (canonicalPadicRho_memLp n 1).aestronglyMeasurable)
    canonicalHaarDensity_integrable.aestronglyMeasurable
  have heq (n : ℕ) : eLpNorm (canonicalPadicRho n - canonicalHaarDensity) 1 padicThreeHaar =
      ENNReal.ofReal (∫ x : ℤ_[3], |canonicalPadicRho n x - canonicalHaarDensity x|
        ∂padicThreeHaar) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm
      ((canonicalPadicRho_integrable padicThreeHaar n).sub canonicalHaarDensity_integrable)]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  simp_rw [heq]
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal canonicalHaarDensity_L1_tendsto

/-- The actual canonical Haar density belongs to every subcritical real Lp space. -/
theorem canonicalHaarDensity_memLp_of_lt_two {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp canonicalHaarDensity (ENNReal.ofReal p) padicThreeHaar := by
  rcases hp.eq_or_lt with rfl | hp
  · simpa only [ENNReal.ofReal_one] using
      (memLp_one_iff_integrable.mpr canonicalHaarDensity_integrable)
  obtain ⟨B, hB, hbound⟩ := exists_canonicalPadicRho_uniform_eLpNorm_bound hp hp2
  refine ⟨canonicalHaarDensity_integrable.aestronglyMeasurable, lt_of_le_of_lt ?_ hB⟩
  exact eLpNorm_le_of_tendstoInMeasure
    ((eventually_ge_atTop 1).mono fun n hn => hbound n hn)
    canonicalPadicRho_tendstoInMeasure
    (fun n => (canonicalPadicRho_memLp n 1).aestronglyMeasurable)

/-- A single density represents the canonical Syracuse law and has all subcritical Lp moments. -/
theorem canonicalSyracuseMeasure_has_subcritical_density :
    ∃ f : ℤ_[3] → ℝ, (∀ x, 0 ≤ f x) ∧
      (∫ x, f x ∂padicThreeHaar) = 1 ∧
      canonicalSyracuseMeasure = padicThreeHaar.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ∀ p : ℝ, 1 ≤ p → p < 2 → MemLp f (ENNReal.ofReal p) padicThreeHaar :=
  ⟨canonicalHaarDensity, canonicalHaarDensity_nonneg, canonicalHaarDensity_integral,
    canonicalSyracuseMeasure_eq_withDensity_canonicalHaarDensity,
    fun _ hp hp2 => canonicalHaarDensity_memLp_of_lt_two hp hp2⟩

#print axioms canonicalHaarDifference_sq_integral_le
#print axioms exists_canonicalHaarDifference_eLpNorm_bound
#print axioms canonicalHaarDensity_memLp_of_lt_two
#print axioms canonicalSyracuseMeasure_has_subcritical_density

end Erdos1135.Tao
