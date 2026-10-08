import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace CollatzResearch

theorem eventually_sum_ne_zero_of_separated_coordinates {d : ℕ}
    (x : ℕ → Fin d → ℝ)
    (hx : ∀ i, ∀ᶠ n in atTop, x n i ≠ 0)
    (hsep : ∀ i j, i < j → Tendsto (fun n => x n i / x n j) atTop (𝓝 0))
    (a : Fin d → ℝ) (ha : a ≠ 0) :
    ∀ᶠ n in atTop, ∑ i, a i * x n i ≠ 0 := by
  classical
  let s := Finset.univ.filter (fun i => a i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact ⟨i, by simpa [s] using hi⟩
  let j := s.max' hs
  have hj : a j ≠ 0 := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hterms : ∀ i : Fin d,
      Tendsto (fun n => a i * (x n i / x n j)) atTop
        (𝓝 (if i = j then a j else 0)) := by
    intro i
    by_cases hij : i = j
    · subst i
      apply tendsto_const_nhds.congr'
      filter_upwards [hx j] with n hn
      simp [hn]
    · by_cases hlt : i < j
      · simpa [hij] using tendsto_const_nhds.mul (hsep i j hlt)
      · have hai : a i = 0 := by
          by_contra hne
          have him : i ∈ s := by simp [s, hne]
          have hle : i ≤ j := s.le_max' i him
          exact hij (le_antisymm hle (le_of_not_gt hlt))
        simp [hai, hij]
  have hlim : Tendsto (fun n => (∑ i, a i * x n i) / x n j)
      atTop (𝓝 (a j)) := by
    simpa only [Finset.sum_div, mul_div_assoc, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using tendsto_finsetSum Finset.univ (fun i _ => hterms i)
  filter_upwards [hlim.eventually_ne hj] with n hn hzero
  exact hn (by rw [hzero, zero_div])

theorem eventually_linearMap_ne_zero_of_separated_coordinates {d : ℕ}
    (x : ℕ → Fin d → ℚ)
    (hx : ∀ i, ∀ᶠ n in atTop, x n i ≠ 0)
    (hsep : ∀ i j, i < j →
      Tendsto (fun n => (x n i : ℝ) / (x n j : ℝ)) atTop (𝓝 0))
    (f : (Fin d → ℚ) →ₗ[ℚ] ℚ) (hf : f ≠ 0) :
    ∀ᶠ n in atTop, f (x n) ≠ 0 := by
  classical
  let a : Fin d → ℚ := fun i => f (fun j => if i = j then 1 else 0)
  have ha : a ≠ 0 := by
    intro h
    apply hf
    apply LinearMap.ext
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ]
    change (∑ i, y i • a i) = 0
    simp [h]
  have haR : (fun i => (a i : ℝ)) ≠ 0 := by
    intro h
    apply ha
    ext i
    have hi : (a i : ℝ) = 0 := by simpa using congrFun h i
    exact_mod_cast hi
  have hxR : ∀ i, ∀ᶠ n in atTop, (x n i : ℝ) ≠ 0 := by
    intro i
    filter_upwards [hx i] with n hn
    exact_mod_cast hn
  have h := eventually_sum_ne_zero_of_separated_coordinates
    (fun n i => (x n i : ℝ)) hxR hsep (fun i => (a i : ℝ)) haR
  filter_upwards [h] with n hn hzero
  apply hn
  have heq : (∑ i, a i * x n i) = 0 := by
    rw [LinearMap.pi_apply_eq_sum_univ] at hzero
    change (∑ i, x n i * a i) = 0 at hzero
    simpa only [mul_comm] using hzero
  exact_mod_cast heq

theorem eventually_not_mem_of_separated_coordinates {d : ℕ}
    (x : ℕ → Fin d → ℚ)
    (hx : ∀ i, ∀ᶠ n in atTop, x n i ≠ 0)
    (hsep : ∀ i j, i < j →
      Tendsto (fun n => (x n i : ℝ) / (x n j : ℝ)) atTop (𝓝 0))
    (W : Submodule ℚ (Fin d → ℚ)) (hW : W ≠ ⊤) :
    ∀ᶠ n in atTop, x n ∉ W := by
  obtain ⟨f, hf, hker⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hW)
  filter_upwards [eventually_linearMap_ne_zero_of_separated_coordinates x hx hsep f hf]
    with n hn hmem
  exact hn (hker hmem)

theorem eventually_avoids_finite_subspaces_of_separated_coordinates {d : ℕ}
    (x : ℕ → Fin d → ℚ)
    (hx : ∀ i, ∀ᶠ n in atTop, x n i ≠ 0)
    (hsep : ∀ i j, i < j →
      Tendsto (fun n => (x n i : ℝ) / (x n j : ℝ)) atTop (𝓝 0))
    (T : Finset (Submodule ℚ (Fin d → ℚ))) (hT : ∀ W ∈ T, W ≠ ⊤) :
    ∀ᶠ n in atTop, ∀ W ∈ T, x n ∉ W := by
  rw [Filter.eventually_all_finset]
  exact fun W hW => eventually_not_mem_of_separated_coordinates x hx hsep W (hT W hW)

theorem eventually_avoids_finite_subspaces_of_separated_equiv {d : ℕ}
    (x : ℕ → Fin d → ℚ) (e : (Fin d → ℚ) ≃ₗ[ℚ] (Fin d → ℚ))
    (hx : ∀ i, ∀ᶠ n in atTop, e (x n) i ≠ 0)
    (hsep : ∀ i j, i < j →
      Tendsto (fun n => (e (x n) i : ℝ) / (e (x n) j : ℝ)) atTop (𝓝 0))
    (T : Finset (Submodule ℚ (Fin d → ℚ))) (hT : ∀ W ∈ T, W ≠ ⊤) :
    ∀ᶠ n in atTop, ∀ W ∈ T, x n ∉ W := by
  rw [Filter.eventually_all_finset]
  intro W hW
  have hmap : W.map e.toLinearMap ≠ ⊤ := by simpa using hT W hW
  filter_upwards [eventually_not_mem_of_separated_coordinates
    (fun n => e (x n)) hx hsep (W.map e.toLinearMap) hmap] with n hn hmem
  exact hn (Submodule.mem_map.mpr ⟨x n, hmem, rfl⟩)

end CollatzResearch

#print axioms CollatzResearch.eventually_avoids_finite_subspaces_of_separated_coordinates
#print axioms CollatzResearch.eventually_avoids_finite_subspaces_of_separated_equiv
