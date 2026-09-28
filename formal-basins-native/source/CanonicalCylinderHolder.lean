import CanonicalSyracuseCylinderLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace CollatzCylinderPacking.Arithmetic

theorem canonical_cylinder_le_maximum (k : ℕ) (v : ZMod (3 ^ k)) :
    (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal ≤
      canonicalMaximumCylinder k := by
  classical
  exact Finset.le_sup' (f := fun v : ZMod (3 ^ k) =>
    (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal)
    (Finset.mem_univ v)

theorem canonical_maximum_le_one (k : ℕ) : canonicalMaximumCylinder k ≤ 1 := by
  classical
  unfold canonicalMaximumCylinder
  apply Finset.sup'_le
  intro v _
  exact measureReal_le_one

theorem eventually_canonical_maximum_holder {θ : ℝ}
    (hθ : θ < Real.log 2 / Real.log 3) :
    ∀ᶠ k : ℕ in atTop, canonicalMaximumCylinder k ≤ (3 : ℝ) ^ (-θ * (k : ℝ)) := by
  filter_upwards [canonical_maximum_exponent.eventually (lt_mem_nhds hθ),
    eventually_gt_atTop (0 : ℕ)] with k hk hk0
  have hp : 0 < canonicalMaximumCylinder k :=
    lt_of_lt_of_le (by positivity) (canonical_maximum_bounds hk0).1
  have hd : 0 < (k : ℝ) * Real.log 3 :=
    mul_pos (by exact_mod_cast hk0) (Real.log_pos (by norm_num))
  have hr := (lt_div_iff₀ hd).mp hk
  apply (Real.log_le_log_iff hp (Real.rpow_pos_of_pos (by norm_num) _)).mp
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  nlinarith

theorem canonical_cylinder_holder_bound {θ : ℝ}
    (hθ : θ < Real.log 2 / Real.log 3) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : ℕ) (v : ZMod (3 ^ k)),
      (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal ≤
        C * (3 : ℝ) ^ (-θ * (k : ℝ)) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_canonical_maximum_holder hθ)
  let C : ℝ := (3 : ℝ) ^ (max θ 0 * (K : ℝ))
  have hC : 1 ≤ C := Real.one_le_rpow (by norm_num) (mul_nonneg (le_max_right _ _) (by positivity))
  refine ⟨C, hC, ?_⟩
  intro k v
  apply (canonical_cylinder_le_maximum k v).trans
  by_cases hk : K ≤ k
  · exact (hK k hk).trans (le_mul_of_one_le_left (Real.rpow_nonneg (by norm_num) _) hC)
  · apply (canonical_maximum_le_one k).trans
    dsimp only [C]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.one_le_rpow (by norm_num)
    have hkr : (k : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hk))
    have hmul := mul_le_mul_of_nonneg_left hkr (le_max_right θ 0)
    have hmul' := mul_le_mul_of_nonneg_right (le_max_left θ 0) (show (0 : ℝ) ≤ k by positivity)
    linarith

theorem canonical_cylinder_uniform_exponent_le {θ C : ℝ}
    (hbound : ∀ (k : ℕ) (v : ZMod (3 ^ k)),
      (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal ≤
        C * (3 : ℝ) ^ (-θ * (k : ℝ))) : θ ≤ Real.log 2 / Real.log 3 := by
  classical
  have hmax (k : ℕ) : canonicalMaximumCylinder k ≤ C * (3 : ℝ) ^ (-θ * (k : ℝ)) := by
    unfold canonicalMaximumCylinder
    apply Finset.sup'_le
    intro v _
    exact hbound k v
  have hCp : 0 < C := by
    have h := (canonical_maximum_bounds (by omega : 0 < 1)).1.trans (hmax 1)
    have hp : 0 < C * (3 : ℝ) ^ (-θ * (1 : ℝ)) :=
      by simpa only [Nat.cast_one] using
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 / 2 : ℝ) ^ (1 : ℕ)) h
    exact (mul_pos_iff.mp hp).elim (fun h => h.1)
      (fun h => False.elim ((Real.rpow_pos_of_pos (by norm_num) _).not_gt h.2))
  by_contra hθ
  have hd : 0 < θ * Real.log 3 - Real.log 2 := by
    have h := (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))).mp (lt_of_not_ge hθ)
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (Real.log C / (θ * Real.log 3 - Real.log 2)))
  have hk0 : 0 < k := by
    have : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) this)
  have hb := (canonical_maximum_bounds hk0).1.trans (hmax k)
  have hl := Real.log_le_log (by positivity : 0 < (1 / 2 : ℝ) ^ k) hb
  rw [Real.log_pow, Real.log_div (by norm_num) (by norm_num), Real.log_one,
    Real.log_mul hCp.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hl
  have hk' := (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hk)
  nlinarith

theorem no_canonical_cylinder_holder_exponent_above {θ : ℝ}
    (hθ : Real.log 2 / Real.log 3 < θ) :
    ¬ ∃ C : ℝ, ∀ (k : ℕ) (v : ZMod (3 ^ k)),
      (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal ≤
        C * (3 : ℝ) ^ (-θ * (k : ℝ)) := by
  rintro ⟨C, hC⟩
  exact (canonical_cylinder_uniform_exponent_le hC).not_gt hθ

end CollatzCylinderPacking.Arithmetic

#print axioms CollatzCylinderPacking.Arithmetic.canonical_cylinder_le_maximum
#print axioms CollatzCylinderPacking.Arithmetic.canonical_maximum_le_one
#print axioms CollatzCylinderPacking.Arithmetic.eventually_canonical_maximum_holder
#print axioms CollatzCylinderPacking.Arithmetic.canonical_cylinder_holder_bound
#print axioms CollatzCylinderPacking.Arithmetic.canonical_cylinder_uniform_exponent_le
#print axioms CollatzCylinderPacking.Arithmetic.no_canonical_cylinder_holder_exponent_above
