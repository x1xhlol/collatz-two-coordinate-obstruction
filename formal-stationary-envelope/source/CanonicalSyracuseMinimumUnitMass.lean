import CanonicalEnvelopeUniformCylinderFloor
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

open Filter
open scoped Topology ENNReal BigOperators
open Erdos1135.Tao CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

noncomputable def canonicalMinimumUnitMass : ℕ → ℝ
  | 0 => 1
  | j + 1 => Finset.univ.inf' Finset.univ_nonempty
      (fun d : Fin 2 × Fin (3 ^ j) => (syracPMF (j + 1) (unitSourceSeedPoint j d)).toReal)

theorem canonicalMinimumUnitMass_le_atom {k : ℕ} (hk : 1 ≤ k)
    (b : ZMod (3 ^ k)) (hb : b.val % 3 ≠ 0) :
    canonicalMinimumUnitMass k ≤ (syracPMF k b).toReal := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨d, rfl⟩ := (unitSourceSeedPoint_range j b).mpr hb
  exact Finset.inf'_le _ (Finset.mem_univ d)

theorem le_canonicalMinimumUnitMass {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : ∀ b : ZMod (3 ^ k), b.val % 3 ≠ 0 → a ≤ (syracPMF k b).toReal) :
    a ≤ canonicalMinimumUnitMass k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  apply Finset.le_inf' Finset.univ_nonempty _
  intro d _
  apply ha
  rw [unitSourceSeedPoint_mod_three]
  omega

theorem canonicalMinimumUnitMass_upper {k : ℕ} (hk : 1 ≤ k) :
    canonicalMinimumUnitMass k ≤ (3 / 2 : ℝ) * ((3 : ℝ) ^ k)⁻¹ := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hsum : (∑ d : Fin 2 × Fin (3 ^ j),
      (syracPMF (j + 1) (unitSourceSeedPoint j d)).toReal) ≤ 1 := by
    calc
      _ = ∑ b ∈ Finset.univ.image (unitSourceSeedPoint j),
          (syracPMF (j + 1) b).toReal := by
        rw [Finset.sum_image]
        intro d _ e _ h
        exact unitSourceSeedPoint_injective j h
      _ ≤ ∑ b : ZMod (3 ^ (j + 1)), (syracPMF (j + 1) b).toReal :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => ENNReal.toReal_nonneg)
      _ = 1 := pmf_sum_toReal _
  have hmin : (2 * (3 : ℝ) ^ j) * canonicalMinimumUnitMass (j + 1) ≤ 1 := by
    calc
      _ = ∑ _d : Fin 2 × Fin (3 ^ j), canonicalMinimumUnitMass (j + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ ∑ d : Fin 2 × Fin (3 ^ j),
          (syracPMF (j + 1) (unitSourceSeedPoint j d)).toReal := by
        apply Finset.sum_le_sum
        intro d _
        exact Finset.inf'_le _ (Finset.mem_univ d)
      _ ≤ 1 := hsum
  have hbound : canonicalMinimumUnitMass (j + 1) ≤ 1 / (2 * (3 : ℝ) ^ j) :=
    (le_div_iff₀ (by positivity : 0 < 2 * (3 : ℝ) ^ j)).mpr
    (by simpa only [mul_comm] using hmin)
  convert hbound using 1
  rw [pow_succ]
  field_simp

theorem canonicalMinimumUnitMass_uniform_bounds :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      c * ((3 : ℝ) ^ k)⁻¹ ≤ canonicalMinimumUnitMass k ∧
      canonicalMinimumUnitMass k ≤ (3 / 2 : ℝ) * ((3 : ℝ) ^ k)⁻¹ := by
  obtain ⟨c, hc, hfloor⟩ := exists_uniform_syracPMF_toReal_unit_floor
  refine ⟨c, hc, fun k hk => ⟨?_, canonicalMinimumUnitMass_upper hk⟩⟩
  exact le_canonicalMinimumUnitMass hk (hfloor k hk)

theorem canonicalMinimumUnitMass_pos (k : ℕ) : 0 < canonicalMinimumUnitMass k := by
  cases k with
  | zero => norm_num [canonicalMinimumUnitMass]
  | succ j =>
    obtain ⟨c, hc, hbound⟩ := canonicalMinimumUnitMass_uniform_bounds
    exact lt_of_lt_of_le (by positivity) (hbound (j + 1) (by omega)).1

theorem canonicalMinimumUnitMass_log_bounds {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ k : ℕ, 1 ≤ k → c * ((3 : ℝ) ^ k)⁻¹ ≤ canonicalMinimumUnitMass k)
    {k : ℕ} (hk : 1 ≤ k) :
    Real.log c / (k : ℝ) - Real.log 3 ≤ Real.log (canonicalMinimumUnitMass k) / k ∧
      Real.log (canonicalMinimumUnitMass k) / k ≤ Real.log (3 / 2 : ℝ) / k - Real.log 3 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlo := Real.log_le_log (by positivity : 0 < c * ((3 : ℝ) ^ k)⁻¹) (hfloor k hk)
  have hhi := Real.log_le_log (canonicalMinimumUnitMass_pos k) (canonicalMinimumUnitMass_upper hk)
  rw [Real.log_mul hc.ne' (by positivity), Real.log_inv, Real.log_pow] at hlo
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_inv, Real.log_pow] at hhi
  constructor
  · apply (le_div_iff₀ hkR).mpr
    have he : (Real.log c / (k : ℝ) - Real.log 3) * (k : ℝ) =
        Real.log c - (k : ℝ) * Real.log 3 := by field_simp
    rw [he]
    linarith
  · apply (div_le_iff₀ hkR).mpr
    have he : (Real.log (3 / 2 : ℝ) / (k : ℝ) - Real.log 3) * (k : ℝ) =
        Real.log (3 / 2 : ℝ) - (k : ℝ) * Real.log 3 := by field_simp
    rw [he]
    linarith

theorem canonicalMinimumUnitMass_logarithmic_rate :
    Tendsto (fun k : ℕ => Real.log (canonicalMinimumUnitMass k) / (k : ℝ))
      atTop (𝓝 (-Real.log 3)) := by
  obtain ⟨c, hc, hbound⟩ := canonicalMinimumUnitMass_uniform_bounds
  have hvanish (a : ℝ) : Tendsto (fun k : ℕ => a / (k : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun k : ℕ => Real.log c / (k : ℝ) - Real.log 3)
      atTop (𝓝 (-Real.log 3)) := by
    simpa only [zero_sub] using (hvanish (Real.log c)).sub_const (Real.log 3)
  have hhi : Tendsto (fun k : ℕ => Real.log (3 / 2 : ℝ) / (k : ℝ) - Real.log 3)
      atTop (𝓝 (-Real.log 3)) := by
    simpa only [zero_sub] using (hvanish (Real.log (3 / 2 : ℝ))).sub_const (Real.log 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    exact (canonicalMinimumUnitMass_log_bounds hc (fun k hk => (hbound k hk).1) hk).1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    exact (canonicalMinimumUnitMass_log_bounds hc (fun k hk => (hbound k hk).1) hk).2

#print axioms canonicalMinimumUnitMass_uniform_bounds
#print axioms canonicalMinimumUnitMass_logarithmic_rate

theorem canonicalMinimumUnitMass_base_three_rate :
    Tendsto (fun k : ℕ => -Real.log (canonicalMinimumUnitMass k) /
      ((k : ℝ) * Real.log 3)) atTop (𝓝 1) := by
  have h := canonicalMinimumUnitMass_logarithmic_rate.neg.div_const (Real.log 3)
  have hlog : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simpa only [neg_div, div_div, neg_neg, div_self hlog] using h

#print axioms canonicalMinimumUnitMass_base_three_rate

end CollatzCanonical.IntegerStationaryEnvelope
