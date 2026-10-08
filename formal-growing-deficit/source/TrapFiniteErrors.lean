import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
Finite error aggregation and elementary exponent budgets. All geometry and
asymptotic error estimates are explicit hypotheses. Blocks use indices through
`r`, and the transitions between them use indices strictly below `r`.
-/

set_option autoImplicit false
open Filter
open scoped BigOperators

namespace CollatzResearch

theorem eventually_trap_finset_abs_sublinear {ι : Type*} (s : Finset ι)
    (e : ℕ → ι → ℝ) (N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (he : ∀ i ∈ s, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |e n i| ≤ gamma * N n) :
    ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, ∑ i ∈ s, |e n i| ≤ gamma * N n := by
  intro gamma hgamma
  let d : ℝ := s.card + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hrate : 0 < gamma / d := div_pos hgamma hd
  have hall : ∀ᶠ n in atTop, ∀ i ∈ s, |e n i| ≤ gamma / d * N n :=
    (eventually_all_finset s).mpr (fun i hi => he i hi (gamma / d) hrate)
  filter_upwards [hN, hall] with n hn hen
  calc
    ∑ i ∈ s, |e n i| ≤ ∑ _i ∈ s, gamma / d * N n :=
      Finset.sum_le_sum (fun i hi => hen i hi)
    _ = (s.card : ℝ) * (gamma / d) * N n := by simp; ring
    _ ≤ gamma * N n := by
      apply mul_le_mul_of_nonneg_right _ hn
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hd).mpr
      dsimp [d]
      nlinarith

theorem eventually_trap_sum_abs_sublinear {r : ℕ}
    (e : ℕ → Fin r → ℝ) (N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (he : ∀ i : Fin r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |e n i| ≤ gamma * N n) :
    ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, ∑ i : Fin r, |e n i| ≤ gamma * N n := by
  exact eventually_trap_finset_abs_sublinear Finset.univ e N hN (fun i _ => he i)

theorem eventually_trap_error_domination {r : ℕ}
    (e : ℕ → Fin r → ℝ) (F N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (he : ∀ i : Fin r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |e n i| ≤ gamma * N n)
    (hF : ∀ᶠ n in atTop, |F n| ≤ ∑ i : Fin r, |e n i|) :
    ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |F n| ≤ gamma * N n := by
  intro gamma hgamma
  filter_upwards [hF, eventually_trap_sum_abs_sublinear e N hN he gamma hgamma]
    with n hFn hen
  exact hFn.trans hen

theorem trap_abs_subset_sum_le_total {r : ℕ} (e : Fin r → ℝ)
    (s : Finset (Fin r)) :
    |∑ i ∈ s, e i| ≤ ∑ i : Fin r, |e i| := by
  calc
    |∑ i ∈ s, e i| ≤ ∑ i ∈ s, |e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin r, |e i| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => abs_nonneg (e i))

theorem eventually_trap_subset_sum_sublinear {r : ℕ}
    (e : ℕ → Fin r → ℝ) (s : ℕ → Finset (Fin r)) (N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (he : ∀ i : Fin r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |e n i| ≤ gamma * N n) :
    ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |∑ i ∈ s n, e n i| ≤ gamma * N n := by
  exact eventually_trap_error_domination e (fun n => ∑ i ∈ s n, e n i) N hN he
    (Eventually.of_forall fun n => trap_abs_subset_sum_le_total (e n) (s n))

theorem trap_nonneg_prefix_sum_le (f : ℕ → ℝ) {i k : ℕ} (hik : i ≤ k)
    (hf : ∀ j < k, 0 ≤ f j) :
    ∑ j ∈ Finset.range i, f j ≤ ∑ j ∈ Finset.range k, f j := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hik)
    (fun j hj _ => hf j (Finset.mem_range.mp hj))

theorem trap_nat_prefix_sum_le (f : ℕ → ℕ) {i k : ℕ} (hik : i ≤ k) :
    ∑ j ∈ Finset.range i, f j ≤ ∑ j ∈ Finset.range k, f j := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hik)
    (fun _ _ _ => Nat.zero_le _)

theorem trap_prefix_exponent_split (D : ℕ → ℕ) {i k : ℕ} (hik : i ≤ k) :
    ∑ j ∈ Finset.range k, D j =
      (∑ j ∈ Finset.range i, D j) + ∑ j ∈ Finset.range (k - i), D (i + j) := by
  simpa only [Nat.add_sub_of_le hik] using Finset.sum_range_add D i (k - i)

theorem trap_prefix_power_split (D : ℕ → ℕ) {i k : ℕ} (hik : i ≤ k) :
    (2 : ℤ) ^ (∑ j ∈ Finset.range k, D j) =
      2 ^ (∑ j ∈ Finset.range i, D j) *
        2 ^ (∑ j ∈ Finset.range (k - i), D (i + j)) := by
  rw [trap_prefix_exponent_split D hik, pow_add]

theorem trap_total_height_le_five (r N : ℕ) (h m : ℕ → ℕ) (e : ℕ → ℤ)
    (heq : ∀ i < r, (h i : ℤ) = 4 * (m i : ℤ) + e i)
    (hm : ∑ i ∈ Finset.range r, m i ≤ N)
    (he : ∑ i ∈ Finset.range r, (e i).natAbs ≤ N) :
    ∑ i ∈ Finset.range r, h i ≤ 5 * N := by
  have hpoint : ∀ i < r, h i ≤ 4 * m i + (e i).natAbs := by
    intro i hi
    have habs : e i ≤ ((e i).natAbs : ℤ) := Int.le_natAbs
    have hbound : (h i : ℤ) ≤ 4 * (m i : ℤ) + ((e i).natAbs : ℤ) := by
      rw [heq i hi]
      omega
    exact_mod_cast hbound
  have hsum := Finset.sum_le_sum (s := Finset.range r)
    (fun i hi => hpoint i (Finset.mem_range.mp hi))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  omega

theorem trap_transition_sum_le_six (r N : ℕ) (D h : ℕ → ℕ) (g : ℕ → ℤ)
    (heq : ∀ i < r, (D i : ℤ) = (h (i + 1) : ℤ) + g i)
    (hh : ∑ i ∈ Finset.range (r + 1), h i ≤ 5 * N)
    (hg : ∑ i ∈ Finset.range r, (g i).natAbs ≤ N) :
    ∑ i ∈ Finset.range r, D i ≤ 6 * N := by
  have hpoint : ∀ i < r, D i ≤ h (i + 1) + (g i).natAbs := by
    intro i hi
    have habs : g i ≤ ((g i).natAbs : ℤ) := Int.le_natAbs
    have hbound : (D i : ℤ) ≤ (h (i + 1) : ℤ) + ((g i).natAbs : ℤ) := by
      rw [heq i hi]
      omega
    exact_mod_cast hbound
  have hsum := Finset.sum_le_sum (s := Finset.range r)
    (fun i hi => hpoint i (Finset.mem_range.mp hi))
  simp only [Finset.sum_add_distrib] at hsum
  have hshift : (∑ i ∈ Finset.range r, h (i + 1)) ≤
      ∑ i ∈ Finset.range (r + 1), h i := by
    rw [Finset.sum_range_succ']
    omega
  omega

theorem trap_prefix_exponent_le_six (r N : ℕ) (D h m : ℕ → ℕ)
    (e g : ℕ → ℤ)
    (hh : ∀ i < r + 1, (h i : ℤ) = 4 * (m i : ℤ) + e i)
    (hD : ∀ i < r, (D i : ℤ) = (h (i + 1) : ℤ) + g i)
    (hm : ∑ i ∈ Finset.range (r + 1), m i ≤ N)
    (he : ∑ i ∈ Finset.range (r + 1), (e i).natAbs ≤ N)
    (hg : ∑ i ∈ Finset.range r, (g i).natAbs ≤ N)
    {k : ℕ} (hk : k ≤ r) :
    ∑ i ∈ Finset.range k, D i ≤ 6 * N := by
  exact (trap_nat_prefix_sum_le D hk).trans
    (trap_transition_sum_le_six r N D h g hD
      (trap_total_height_le_five (r + 1) N h m e hh hm he) hg)

end CollatzResearch

#print axioms CollatzResearch.eventually_trap_sum_abs_sublinear
#print axioms CollatzResearch.eventually_trap_error_domination
#print axioms CollatzResearch.trap_prefix_exponent_le_six
