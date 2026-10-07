import FinitePathCylinder
import ActualTransitionAtom

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open CollatzCanonical.DirichletAbelian

def ValidPrefix (n k : ℕ) (x : ℕ → ℕ) : Prop :=
  x 0 = n ∧ (∀ i ≤ k, 0 < x i ∧ x i % 3 ≠ 0) ∧
    ∀ i < k, ∃ a : ℕ, (2 ^ a * x i) % 3 = 2 ∧ x (i + 1) = inverseEndpoint (x i) a

theorem ValidPrefix.restrict {n k l : ℕ} {x : ℕ → ℕ} (h : ValidPrefix n l x)
    (hkl : k ≤ l) : ValidPrefix n k x :=
  ⟨h.1, fun i hi => h.2.1 i (hi.trans hkl), fun i hi => h.2.2 i (hi.trans_le hkl)⟩

theorem ValidPrefix.ancestor {n k : ℕ} {x : ℕ → ℕ} (h : ValidPrefix n k x)
    {i : ℕ} (hi : i ≤ k) : ∃ A, iterate A (x i) = n := by
  induction i with
  | zero => exact ⟨0, h.1⟩
  | succ i ih =>
    obtain ⟨A, hA⟩ := ih (by omega)
    obtain ⟨a, ha, hx⟩ := h.2.2 i (by omega)
    refine ⟨a + 1 + A, ?_⟩
    rw [iterate_add, hx, (inverseEndpoint_block ha).2.1, hA]

theorem pathLaw_validPrefix_cylinder {n : ℕ} (hnp : Nonperiodic n)
    (k : ℕ) (x : ℕ → ℕ) (h : ValidPrefix n k x) :
    pathLaw n (prefixSet k x) =
      ENNReal.ofReal (firstHitWeight n (x k) * actualFirstHitDensity (x k) /
        actualFirstHitDensity n) := by
  induction k with
  | zero =>
    have hp := (actual_weighted_density_positive_iff_unit (h.2.1 0 le_rfl).1).mpr
      (h.2.1 0 le_rfl).2
    rw [h.1] at hp
    rw [pathLaw_prefix_zero x h.1, h.1, firstHitWeight_self, one_mul, div_self hp.ne',
      ENNReal.ofReal_one]
  | succ k ih =>
    have hk := h.2.1 k (by omega)
    have hD := (actual_weighted_density_positive_iff_unit hk.1).mpr hk.2
    obtain ⟨A, hA⟩ := h.ancestor (show k ≤ k + 1 by omega)
    have hnpk := nonperiodic_ancestor hnp hA
    obtain ⟨a, ha, hx⟩ := h.2.2 k (by omega)
    have htrans : transitionPMF (x k) (x (k + 1)) =
        ENNReal.ofReal (firstHitWeight (x k) (x (k + 1)) *
          actualFirstHitDensity (x (k + 1)) / actualFirstHitDensity (x k)) := by
      rw [hx]
      exact transitionPMF_nonperiodic_atom hk.1 hk.2 hnpk ha
    have hstep : iterate (a + 1) (x (k + 1)) = x k := by
      rw [hx]
      exact (inverseEndpoint_block ha).2.1
    have hfactor := firstHitWeight_through_nonperiodic hnp hA hstep
    rw [pathLaw_prefix_succ, ih (h.restrict (by omega)), htrans,
      ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (firstHitWeight_bounds _ _).1
        (actualFirstHitDensity_nonneg _)) (actualFirstHitDensity_nonneg _))]
    congr 1
    rw [hfactor]
    field_simp

theorem pathLaw_validPrefix_source_limit {n : ℕ} (hnp : Nonperiodic n)
    (k : ℕ) (x : ℕ → ℕ) (h : ValidPrefix n k x) :
    Tendsto (fun t : ℝ => (2 / actualFirstHitDensity n) *
      (logarithmicCumulative
        (fun q => if q % 2 = 1 then suffixSourceWeight n (x k) q else 0) t / t))
      atTop (𝓝 (pathLaw n (prefixSet k x)).toReal) := by
  rw [pathLaw_validPrefix_cylinder hnp k x h, ENNReal.toReal_ofReal]
  · obtain ⟨A, hA⟩ := h.ancestor le_rfl
    exact normalized_suffixSourceWeight_mean hnp hA
  · exact div_nonneg (mul_nonneg (firstHitWeight_bounds _ _).1
      (actualFirstHitDensity_nonneg _)) (actualFirstHitDensity_nonneg _)

end CollatzCylinderPacking.Arithmetic.InverseDoob
