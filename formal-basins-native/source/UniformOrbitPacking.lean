import OrbitPackingActualRecurrence
import OrbitPackingParameters

/-! Uniform power packing for every finite path of distinct positive shortcut states. -/

set_option autoImplicit false

namespace CollatzUniformOrbitPacking

open CollatzCylinderPacking CollatzOrbitPackingFiniteRecurrence
open CollatzCanonical.PackingParameters

/-- The packing constant depends only on the exponent, uniformly over all
positive seeds, finite path lengths, and natural cutoffs. -/
theorem uniform_finite_distinct_orbit_packing (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N L X : ℕ, 0 < N →
      Set.InjOn (fun i => iterate i N) (Finset.range L) →
      (prefixCount N L X : ℝ) ≤ K * (X : ℝ) ^ b := by
  obtain ⟨ρ, hρ, hρq, he, _, hc⟩ := exists_packing_parameters b hbβ hb1
  have hρ1 : ρ < 1 := hρq.trans threshold_mem.2
  exact CollatzOrbitPackingActualRecurrence.uniform_finite_distinct_packing_of_parameters
    ρ b (ρ * Real.log 3 / Real.log 2) hρ.le hρ1 (beta_pos.trans hbβ) hc he.symm rfl

noncomputable def realPrefixCount (N L : ℕ) (X : ℝ) : ℕ :=
  ((Finset.range L).filter (fun i => (iterate i N : ℝ) ≤ X)).card

theorem realPrefixCount_eq_floor (N L : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    realPrefixCount N L X = prefixCount N L (Nat.floor X) := by
  unfold realPrefixCount prefixCount
  congr 1
  apply Finset.filter_congr
  intro i _
  exact (Nat.le_floor_iff hX).symm

/-- Taking integer parts gives the same constant at every nonnegative real cutoff. -/
theorem uniform_real_cutoff_packing (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N L : ℕ, 0 < N →
      Set.InjOn (fun i => iterate i N) (Finset.range L) →
      ∀ X : ℝ, 0 ≤ X → (realPrefixCount N L X : ℝ) ≤ K * X ^ b := by
  obtain ⟨K, hK, hbound⟩ := uniform_finite_distinct_orbit_packing b hbβ hb1
  refine ⟨K, hK, ?_⟩
  intro N L hN hinj X hX
  rw [realPrefixCount_eq_floor N L X hX]
  apply (hbound N L (Nat.floor X) hN hinj).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hX) (beta_pos.trans hbβ).le) hK

/-- Every finite path satisfying the shortcut transition rule has the same
power bound.  The path need not be part of an infinite distinct orbit. -/
theorem uniform_finite_path_packing (b : ℝ) (hbβ : beta < b) (hb1 : b < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℕ) (x : ℕ → ℕ), 0 < x 0 →
      (∀ i, i + 1 < L → x (i + 1) = step (x i)) →
      Set.InjOn x (Finset.range L) →
      ∀ X : ℝ, 0 ≤ X →
        (((Finset.range L).filter (fun i => (x i : ℝ) ≤ X)).card : ℝ) ≤ K * X ^ b := by
  obtain ⟨K, hK, hbound⟩ := uniform_real_cutoff_packing b hbβ hb1
  refine ⟨K, hK, ?_⟩
  intro L x hx hpath hinj X hX
  have hiter : ∀ i, i < L → x i = iterate i (x 0) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [hpath i hi, ih (by omega)]
      rfl
  have hdistinct : Set.InjOn (fun i => iterate i (x 0)) (Finset.range L) := by
    intro i hi j hj he
    apply hinj hi hj
    rw [hiter i (Finset.mem_range.mp hi), hiter j (Finset.mem_range.mp hj)]
    exact he
  have hcount : ((Finset.range L).filter (fun i => (x i : ℝ) ≤ X)).card =
      realPrefixCount (x 0) L X := by
    unfold realPrefixCount
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [hiter i (Finset.mem_range.mp hi)]
  rw [hcount]
  exact hbound (x 0) L hx hdistinct X hX

#print axioms uniform_finite_distinct_orbit_packing
#print axioms uniform_real_cutoff_packing
#print axioms uniform_finite_path_packing

end CollatzUniformOrbitPacking
