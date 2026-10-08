import AsymptoticSubspaceEscape

set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace CollatzResearch

/-- Replace the first coordinate by its difference from the sum of the tails. -/
def trapCoordinateShear (t : ℕ) :
    (Fin (t + 1) → ℚ) ≃ₗ[ℚ] (Fin (t + 1) → ℚ) where
  toFun x := Fin.cases (x 0 - ∑ i : Fin t, x i.succ) (fun i => x i.succ)
  invFun x := Fin.cases (x 0 + ∑ i : Fin t, x i.succ) (fun i => x i.succ)
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib]
      ring
    · simp
  map_smul' a x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [Finset.mul_sum, mul_sub]

@[simp] theorem trapCoordinateShear_zero (t : ℕ) (x : Fin (t + 1) → ℚ) :
    trapCoordinateShear t x 0 = x 0 - ∑ i : Fin t, x i.succ := rfl

@[simp] theorem trapCoordinateShear_succ (t : ℕ) (x : Fin (t + 1) → ℚ)
    (i : Fin t) :
    trapCoordinateShear t x i.succ = x i.succ := rfl

@[simp] theorem trapCoordinateShear_symm_zero (t : ℕ) (x : Fin (t + 1) → ℚ) :
    (trapCoordinateShear t).symm x 0 = x 0 + ∑ i : Fin t, x i.succ := rfl

@[simp] theorem trapCoordinateShear_symm_succ (t : ℕ) (x : Fin (t + 1) → ℚ)
    (i : Fin t) :
    (trapCoordinateShear t).symm x i.succ = x i.succ := rfl

/-- The first-coordinate residual and ordered tails exclude every fixed finite
family of proper rational subspaces for the original, unsheared vector. -/
theorem eventually_avoids_finite_subspaces_of_trap_ratios {t : ℕ}
    (x : ℕ → Fin (t + 1) → ℚ)
    (hb : ∀ᶠ n in atTop, x n 0 - ∑ i : Fin t, x n i.succ ≠ 0)
    (hx : ∀ i : Fin t, ∀ᶠ n in atTop, x n i.succ ≠ 0)
    (hbsmall : ∀ i : Fin t,
      Tendsto
        (fun n => ((x n 0 - ∑ j : Fin t, x n j.succ : ℚ) : ℝ) /
          (x n i.succ : ℝ)) atTop (𝓝 0))
    (hsep : ∀ i j : Fin t, i < j →
      Tendsto (fun n => (x n i.succ : ℝ) / (x n j.succ : ℝ)) atTop (𝓝 0))
    (T : Finset (Submodule ℚ (Fin (t + 1) → ℚ)))
    (hT : ∀ W ∈ T, W ≠ ⊤) :
    ∀ᶠ n in atTop, ∀ W ∈ T, x n ∉ W := by
  apply eventually_avoids_finite_subspaces_of_separated_equiv
    x (trapCoordinateShear t) ?_ ?_ T hT
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hb
    · simpa using hx j
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro h
        exact False.elim ((lt_irrefl _) h)
      · intro _
        simpa using hbsmall b
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro h
        exact False.elim (Fin.not_lt_zero _ h)
      · intro h
        simpa using hsep a b (Fin.succ_lt_succ_iff.mp h)

end CollatzResearch

#print axioms CollatzResearch.trapCoordinateShear
#print axioms CollatzResearch.eventually_avoids_finite_subspaces_of_trap_ratios
