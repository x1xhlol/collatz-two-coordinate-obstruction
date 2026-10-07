import ActualUnitSupport
import FixedBasinGreenBoundary
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

noncomputable def potential (n : ℕ) : ℝ :=
  actualDensityValue actualFirstHitDensity n

theorem potential_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ potential n := by
  unfold potential actualDensityValue
  exact mul_nonneg
    (mul_nonneg (mul_nonneg CollatzCanonical.GreenKernelScalars.delta_pos.le
      (greenCycleFactor_one_pos hn).le) (Nat.cast_nonneg n))
    (actualFirstHitDensity_nonneg n)

theorem potential_pos_of_unit {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0) :
    0 < potential n := (actual_trace_positive_iff_unit hn).mpr hu

/-- The index counts the even shortcut steps after the first odd step.
The full Syracuse valuation of this inverse branch is `a + 1`. -/
def inverseEndpoint (n a : ℕ) : ℕ := oddPredecessor (2 ^ a * n)

noncomputable def inverseRowMass (n a : ℕ) : ℝ :=
  if (2 ^ a * n) % 3 = 2 then
    (3 / 2 : ℝ) * potential (inverseEndpoint n a) / (2 : ℝ) ^ a else 0

theorem inverseRowMass_nonneg (n a : ℕ) : 0 ≤ inverseRowMass n a := by
  unfold inverseRowMass
  split_ifs with h
  · exact div_nonneg (mul_nonneg (by norm_num)
      (potential_nonneg (oddPredecessor_spec h).1)) (by positivity)
  · exact le_rfl

theorem iterate_dyadic (n k : ℕ) : iterate k (2 ^ k * n) = n := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have he : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
    rw [he, show k + 1 = 1 + k by omega, iterate_add]
    simpa only [iterate, step_two_mul] using ih

theorem dyadic_row_telescope {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (∑ a ∈ Finset.range k, inverseRowMass n a) +
      potential (2 ^ k * n) / (2 : ℝ) ^ k = potential n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 < 2 ^ k * n := Nat.mul_pos (by positivity) hn
    have hh := actual_unconditional_density_harmonic hp
    change potential (2 ^ k * n) =
      (1 / 2 : ℝ) * potential (2 * (2 ^ k * n)) +
      (3 / 2 : ℝ) * (if (2 ^ k * n) % 3 = 2 then
        potential (inverseEndpoint n k) else 0) at hh
    rw [Finset.sum_range_succ]
    have he : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
    rw [he, pow_succ]
    unfold inverseRowMass at ih ⊢
    split_ifs at hh ⊢ with h
    · have hk : (2 : ℝ) ^ k ≠ 0 := by positivity
      have heq : (3 / 2 : ℝ) * potential (inverseEndpoint n k) / 2 ^ k +
          potential (2 * (2 ^ k * n)) / (2 ^ k * 2) =
          potential (2 ^ k * n) / 2 ^ k := by
        rw [hh]
        field_simp
        ring
      linarith [heq]
    · have heq : potential (2 * (2 ^ k * n)) / ((2 : ℝ) ^ k * 2) =
          potential (2 ^ k * n) / (2 : ℝ) ^ k := by
        rw [hh]
        ring
      simpa only [add_zero, heq] using ih

theorem dyadic_potential_remainder_tendsto_zero {n : ℕ} (hn : 0 < n) :
    Tendsto (fun k : ℕ => potential (2 ^ k * n) / (2 : ℝ) ^ k)
      atTop (𝓝 0) := by
  have hg : Tendsto (fun k : ℕ => 2 ^ k * n) atTop atTop := by
    apply tendsto_atTop_mono (fun k => ?_) tendsto_id
    exact (Nat.lt_two_pow_self.le).trans (Nat.le_mul_of_pos_right _ hn)
  have hbasin : Tendsto (fun k : ℕ => 2 ^ k * n) atTop
      (atTop ⊓ 𝓟 {v : ℕ | ∃ K, iterate K v = n}) := by
    refine tendsto_inf.mpr ⟨hg, tendsto_principal.mpr ?_⟩
    exact Filter.Eventually.of_forall (fun k => ⟨k, iterate_dyadic n k⟩)
  have hlim := ((fixed_basin_green_ratio_tendsto_zero n).comp hbasin).const_mul (n : ℝ)
  convert hlim using 1
  · ext k
    change potential (2 ^ k * n) / (2 : ℝ) ^ k =
      (n : ℝ) * (potential (2 ^ k * n) / (2 ^ k * n : ℕ))
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  · simp

theorem inverseRowMass_hasSum {n : ℕ} (hn : 0 < n) :
    HasSum (inverseRowMass n) (potential n) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (inverseRowMass_nonneg n) _).mpr
  have ht := (tendsto_const_nhds (x := potential n)).sub
    (dyadic_potential_remainder_tendsto_zero hn)
  convert ht using 1
  · ext k
    linarith [dyadic_row_telescope hn k]
  · simp

theorem inverseRowMass_tsum {n : ℕ} (hn : 0 < n) :
    ∑' a : ℕ, inverseRowMass n a = potential n := (inverseRowMass_hasSum hn).tsum_eq

end CollatzCylinderPacking.Arithmetic.InverseDoob
