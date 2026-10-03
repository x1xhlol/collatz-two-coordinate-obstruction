import CanonicalCylinderRecursion
import NativeSyracuseClockBridge
import ShortcutOddEndpoints
import UniformOrbitCorrection

set_option autoImplicit false
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.Correction CollatzCanonical.NativeTao
open CollatzCanonical.UniformCorrection Erdos1135

noncomputable section

theorem canonicalRho_even_forward {k : ℕ} (hk : 0 < k) {m : ℕ}
    (hm : m % 2 = 0) :
    (1 / 2 : ℝ) * canonicalRho k m ≤ canonicalRho k (step m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have he : 2 * step m = m := step_even hm
  have h := canonicalRho_successor_recursion d (step m)
  rw [he] at h
  have hn : 0 ≤ (if step m % 3 = 2 then canonicalRho d (oddPredecessor (step m)) else 0) := by
    split_ifs
    · exact canonicalRho_nonneg _ _
    · exact le_rfl
  linarith

theorem canonicalRho_odd_forward (k : ℕ) {m : ℕ} (hm : m % 2 = 1) :
    (3 / 2 : ℝ) * canonicalRho k m ≤ canonicalRho (k + 1) (step m) := by
  have he := step_odd hm
  have hu : step m % 3 = 2 := by omega
  have hp : oddPredecessor (step m) = m := by unfold oddPredecessor; omega
  have h := canonicalRho_successor_recursion k (step m)
  rw [if_pos hu, hp] at h
  linarith [canonicalRho_nonneg (k + 1) (2 * step m)]

/-- The actual shortcut path propagates a cylinder at the exact accumulated odd depth. -/
theorem canonicalRho_forward_path {k : ℕ} (hk : 0 < k) (A u : ℕ) :
    (3 : ℝ) ^ oddCount A u * (1 / 2 : ℝ) ^ A * canonicalRho k u ≤
      canonicalRho (k + oddCount A u) (iterate A u) := by
  induction A with
  | zero => simp [oddCount, iterate]
  | succ A ih =>
    have hd : 0 < k + oddCount A u := by omega
    by_cases he : iterate A u % 2 = 0
    · have h := canonicalRho_even_forward hd he
      simp only [oddCount, he, Nat.add_zero, iterate, pow_succ]
      nlinarith
    · have ho : iterate A u % 2 = 1 := by omega
      have h := canonicalRho_odd_forward (k + oddCount A u) ho
      simp only [oddCount, ho, iterate, pow_succ]
      rw [Nat.add_assoc] at h
      nlinarith

/-- Normalizing by the actual endpoints exposes the reciprocal correction product. -/
theorem normalized_canonicalRho_forward_path {k : ℕ} (hk : 0 < k)
    {u : ℕ} (hu : 0 < u) (A : ℕ) :
    pathWeight A u * (canonicalRho k u / (u : ℝ)) ≤
      canonicalRho (k + oddCount A u) (iterate A u) / (iterate A u : ℝ) := by
  have hp : (0 : ℝ) < iterate A u := by exact_mod_cast iterate_pos A hu
  apply (le_div_iff₀ hp).mpr
  have h := canonicalRho_forward_path hk A u
  rw [hitting_path_weight hu rfl] at h
  convert h using 1
  ring

/-- A single positive constant controls propagation along every injective positive orbit. -/
theorem exists_uniform_cylinder_path_survival :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℕ, 0 < u →
      Function.Injective (fun i => iterate i u) → ∀ k A : ℕ, 0 < k →
      c * (canonicalRho k u / (u : ℝ)) ≤
        canonicalRho (k + oddCount A u) (iterate A u) / (iterate A u : ℝ) := by
  obtain ⟨P, hP, hbound⟩ := exists_uniform_finite_path_product_bound
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  refine ⟨P⁻¹, inv_pos.mpr hPpos, ?_⟩
  intro u hu hinj k A hk
  have hpc : pathCorrection A u ≤ P :=
    (hbound A (fun i => iterate i u) hu (fun _ _ => rfl) hinj.injOn).2
  have hw : P⁻¹ ≤ pathWeight A u := by
    unfold pathWeight
    exact inv_anti₀ (lt_of_lt_of_le zero_lt_one (one_le_pathCorrection A u)) hpc
  exact (mul_le_mul_of_nonneg_right hw
    (div_nonneg (canonicalRho_nonneg k u) (Nat.cast_nonneg u))).trans
      (normalized_canonicalRho_forward_path hk hu A)

/-- The same bound at Syracuse depth uses the native clock and native odd count. -/
theorem exists_uniform_syracuse_cylinder_survival :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℕ, Odd u →
      Function.Injective (fun i => iterate i u) → ∀ k j : ℕ, 0 < k →
      c * (canonicalRho k u / (u : ℝ)) ≤
        canonicalRho (k + j) ((Tao.syracuse^[j]) u) / ((Tao.syracuse^[j]) u : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := exists_uniform_cylinder_path_survival
  refine ⟨c, hc, ?_⟩
  intro u hu hinj k j hk
  have hup : 0 < u := by obtain ⟨t, ht⟩ := hu; omega
  have h := hbound u hup hinj k (Tao.taoTupleWeight (Tao.syracuseValuationPNatList j u hu)) hk
  simpa only [syracuse_shortcut_oddCount, syracuse_shortcut_landing] using h

#print axioms canonicalRho_forward_path
#print axioms exists_uniform_syracuse_cylinder_survival
end
end CollatzCanonical.PeriodicCensusFloor
