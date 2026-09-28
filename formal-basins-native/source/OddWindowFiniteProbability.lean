import OddWindowNormalization
import OddTargetFirstPassageTransport

set_option autoImplicit false

open scoped BigOperators
open CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.DirichletAbelian

noncomputable def oddWindowIndices (s t : ℝ) : Finset ℕ :=
  (Finset.Ico ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter (fun n => (n + 1) % 2 = 1)

noncomputable def oddWindowProbability (s t : ℝ)
    (i : {n : ℕ // n ∈ oddWindowIndices s t}) : ℝ :=
  (1 / (i.1 + 1 : ℕ) : ℝ) / oddWindowMass s t

theorem oddWindowNumerator_eq_sum (w : ℕ → ℝ) {s t : ℝ} (hst : s ≤ t) :
    oddWindowNumerator w s t = ∑ n ∈ oddWindowIndices s t, w (n + 1) / (n + 1 : ℕ) := by
  have hfloor := Nat.floor_mono (Real.exp_le_exp.mpr hst)
  unfold oddWindowNumerator oddLogarithmicCumulative logarithmicCumulative oddWindowIndices
  rw [← Finset.sum_Ico_eq_sub _ hfloor, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  split_ifs <;> simp

theorem oddWindowMass_eq_sum {s t : ℝ} (hst : s ≤ t) :
    oddWindowMass s t = ∑ n ∈ oddWindowIndices s t, (1 : ℝ) / (n + 1 : ℕ) :=
  oddWindowNumerator_eq_sum (fun _ => 1) hst

theorem oddWindowProbability_nonneg {s t : ℝ} (hmass : 0 < oddWindowMass s t)
    (i : {n : ℕ // n ∈ oddWindowIndices s t}) : 0 ≤ oddWindowProbability s t i := by
  unfold oddWindowProbability
  positivity

theorem oddWindowProbability_mass {s t : ℝ} (hst : s ≤ t)
    (hmass : 0 < oddWindowMass s t) :
    ∑ i, oddWindowProbability s t i = 1 := by
  classical
  unfold oddWindowProbability
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have he : (∑ i : {n : ℕ // n ∈ oddWindowIndices s t}, (1 : ℝ) / (i.1 + 1 : ℕ)) =
      oddWindowMass s t := by
    rw [oddWindowMass_eq_sum hst]
    exact Finset.sum_coe_sort _ (fun n => (1 : ℝ) / (n + 1 : ℕ))
  simp only [← div_eq_mul_inv]
  rw [he, div_self hmass.ne']

theorem finiteMean_oddWindowProbability (w : ℕ → ℝ) {s t : ℝ} (hst : s ≤ t) :
    finiteMean (oddWindowProbability s t) (fun i => w (i.1 + 1)) =
      oddWindowExpectation w s t := by
  classical
  unfold finiteMean oddWindowProbability oddWindowExpectation
  have he (i : {n : ℕ // n ∈ oddWindowIndices s t}) :
      (1 / (i.1 + 1 : ℕ) : ℝ) / oddWindowMass s t * w (i.1 + 1) =
        (w (i.1 + 1) / (i.1 + 1 : ℕ)) * (oddWindowMass s t)⁻¹ := by ring
  simp_rw [he]
  have hs : (∑ i : {n : ℕ // n ∈ oddWindowIndices s t},
      w (i.1 + 1) / (i.1 + 1 : ℕ)) = oddWindowNumerator w s t := by
    rw [oddWindowNumerator_eq_sum w hst]
    exact Finset.sum_coe_sort _ (fun n => w (n + 1) / (n + 1 : ℕ))
  rw [← Finset.sum_mul, hs, div_eq_mul_inv]

#print axioms oddWindowNumerator_eq_sum
#print axioms oddWindowProbability_mass
#print axioms finiteMean_oddWindowProbability

end CollatzCanonical.DirichletAbelian
