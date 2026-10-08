import UnitSourcePadicDensityComparison
import Erdos1135.Tao.Fourier.Prop114CanonicalAssembly
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Canonical cylinder densities are Cauchy in actual Haar L1

The exact finite marginal identity identifies the two-scale Haar L1 error
with the already proved native fine-scale oscillation.
-/

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

theorem taoProjection_padic_reduce {m n : ℕ} (hmn : m ≤ n) (x : ℤ_[3]) :
    taoZModThreeProjection hmn (PadicInt.toZModPow n x) = PadicInt.toZModPow m x := by
  exact padic_projection_reduce hmn x

theorem canonicalPadicRho_nonneg (n : ℕ) (x : ℤ_[3]) :
    0 ≤ canonicalPadicRho n x := by
  rw [canonicalPadicRho_eq_syracMass]
  positivity

theorem canonicalPadicRho_integral (n : ℕ) :
    (∫ x : ℤ_[3], canonicalPadicRho n x ∂padicThreeHaar) = 1 := by
  simp_rw [canonicalPadicRho_eq_syracMass]
  rw [integral_padicThreeHaar_cylinder n (fun y => (3 : ℝ)^n * (syracPMF n y).toReal),
    ← Finset.mul_sum, pmf_sum_toReal]
  simp

theorem canonicalPadicRho_twoScale_error {m n : ℕ} (hmn : m ≤ n) :
    (∫ x : ℤ_[3], |canonicalPadicRho n x - canonicalPadicRho m x| ∂padicThreeHaar) =
      syracFineScaleOscillation m n := by
  simp_rw [canonicalPadicRho_eq_syracMass,
    ← taoProjection_padic_reduce hmn]
  rw [integral_padicThreeHaar_cylinder n (fun y =>
    |(3 : ℝ)^n * (syracPMF n y).toReal -
      (3 : ℝ)^m * (syracPMF m (taoZModThreeProjection hmn y)).toReal|)]
  unfold syracFineScaleOscillation taoZModPowOscillation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [zmodPowFiberSum_syracPMFMassVector_eq_projection hmn y]
  unfold zmodPowFiberAverageScale syracPMFMassVector
  push_cast
  have hp : (3 : ℝ) ^ n ≠ 0 := by positivity
  rw [← abs_of_pos (show (0 : ℝ) < 3 ^ n by positivity), ← abs_div]
  congr 1
  field_simp
  rw [abs_of_pos (show (0 : ℝ) < 3 ^ n by positivity)]

/-- Each finer canonical cylinder density integrates to the exact canonical
probability on every coarser cylinder. -/
theorem canonicalPadicRho_cylinder_integral {k n : ℕ} (hkn : k ≤ n)
    (v : ZMod (3 ^ k)) :
    (∫ x : ℤ_[3] in {x | PadicInt.toZModPow k x = v},
      canonicalPadicRho n x ∂padicThreeHaar) =
      (canonicalSyracuseMeasure {x | PadicInt.toZModPow k x = v}).toReal := by
  classical
  rw [← integral_indicator (padic_cylinder_measurable k v)]
  have hind : {x : ℤ_[3] | PadicInt.toZModPow k x = v}.indicator
      (canonicalPadicRho n) = fun x =>
      if taoZModThreeProjection hkn (PadicInt.toZModPow n x) = v then
        (3 : ℝ)^n * (syracPMF n (PadicInt.toZModPow n x)).toReal else 0 := by
    funext x
    simp [Set.indicator, taoProjection_padic_reduce, canonicalPadicRho_eq_syracMass]
  rw [hind, integral_padicThreeHaar_cylinder n (fun y =>
    if taoZModThreeProjection hkn y = v then (3 : ℝ)^n * (syracPMF n y).toReal else 0)]
  rw [canonical_cylinder_real_eq_syracPMF,
    ← syracPMF_map_taoZModThreeProjection_eq_of_le hkn,
    pmf_map_apply_toReal_tsum, tsum_fintype, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases h : taoZModThreeProjection hkn y = v
  · rw [if_pos h, if_pos h.symm]
    field_simp
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp

noncomputable def canonicalHaarL1 (n : ℕ) : ℤ_[3] →₁[padicThreeHaar] ℝ :=
  (canonicalPadicRho_integrable padicThreeHaar n).toL1 (canonicalPadicRho n)

theorem canonicalHaarL1_coe (n : ℕ) :
    canonicalHaarL1 n =ᵐ[padicThreeHaar] canonicalPadicRho n :=
  Integrable.coeFn_toL1 _

theorem canonicalHaarL1_dist_eq_error (m n : ℕ) :
    dist (canonicalHaarL1 n) (canonicalHaarL1 m) =
      ∫ x : ℤ_[3], |canonicalPadicRho n x - canonicalPadicRho m x| ∂padicThreeHaar := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [canonicalHaarL1_coe n, canonicalHaarL1_coe m] with x hn hm
  rw [hn, hm, Real.dist_eq]

theorem canonicalHaarL1_dist_eq_oscillation {m n : ℕ} (hmn : m ≤ n) :
    dist (canonicalHaarL1 n) (canonicalHaarL1 m) = syracFineScaleOscillation m n := by
  rw [canonicalHaarL1_dist_eq_error, canonicalPadicRho_twoScale_error hmn]

theorem canonicalHaarL1_cauchy : CauchySeq canonicalHaarL1 := by
  obtain ⟨C, hC, hmix⟩ := taoProp114FineScaleMixing.bound (A := 1) (by omega)
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε + 1)
  have hN0 : 1 ≤ N := by
    have : (0 : ℝ) ≤ C / ε := div_nonneg hC hε.le
    have : (1 : ℝ) < N := by linarith
    exact_mod_cast this.le
  refine ⟨N, fun n hn => ?_⟩
  rw [canonicalHaarL1_dist_eq_oscillation hn]
  have hb := hmix n N hN0 hn
  simp only [pow_one] at hb
  apply hb.trans_lt
  apply (div_lt_iff₀ (by exact_mod_cast (show 0 < N by omega))).mpr
  have hCN : C / ε < N := by linarith
  have := (div_lt_iff₀ hε).mp hCN
  nlinarith

theorem exists_canonicalHaarL1_limit :
    ∃ L : ℤ_[3] →₁[padicThreeHaar] ℝ, Tendsto canonicalHaarL1 atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete canonicalHaarL1_cauchy

theorem canonicalHaarL1_limit_polynomial_rate
    (L : ℤ_[3] →₁[padicThreeHaar] ℝ)
    (hL : Tendsto canonicalHaarL1 atTop (𝓝 L)) (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
      dist L (canonicalHaarL1 m) ≤ C / (m : ℝ)^A := by
  obtain ⟨C, hC, hmix⟩ := taoProp114FineScaleMixing.bound hA
  refine ⟨C, hC, fun m hm => ?_⟩
  apply le_of_tendsto (hL.dist tendsto_const_nhds)
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [canonicalHaarL1_dist_eq_oscillation hn]
  exact hmix n m hm hn

#print axioms canonicalPadicRho_twoScale_error
#print axioms canonicalPadicRho_cylinder_integral
#print axioms exists_canonicalHaarL1_limit
#print axioms canonicalHaarL1_limit_polynomial_rate

end Erdos1135.Tao
