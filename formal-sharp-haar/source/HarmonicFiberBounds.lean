import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

open Finset

theorem harmonic_pow_two_le (j : ℕ) :
    (∑ q ∈ range (2 ^ j), (1 : ℝ) / ((q : ℝ) + 1)) ≤ (j : ℝ) + 1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hn : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
    have htail : (∑ q ∈ range (2 ^ j),
        (1 : ℝ) / (((2 ^ j + q : ℕ) : ℝ) + 1)) ≤ 1 := by
      calc
        _ ≤ ∑ _q ∈ range (2 ^ j), (1 : ℝ) / (2 ^ j : ℕ) := by
          apply sum_le_sum
          intro q hq
          apply one_div_le_one_div_of_le hn
          simp only [Nat.cast_add]
          linarith [Nat.cast_nonneg (α := ℝ) q]
        _ = 1 := by simp
    rw [pow_succ, Nat.mul_two, sum_range_add]
    push_cast at htail ⊢
    linarith

theorem card_sq_le_harmonic_weight {ι : Type*} (s : Finset ι)
    (q : ι → ℕ) (Y : ι → ℝ) (j : ℕ)
    (hinj : Set.InjOn q (↑s : Set ι))
    (hqb : ∀ w ∈ s, q w < 2 ^ j)
    (hqY : ∀ w ∈ s, (q w : ℝ) ≤ Y w) :
    (s.card : ℝ) ^ 2 ≤ ((j : ℝ) + 1) * ∑ w ∈ s, (1 + Y w) := by
  classical
  have hY : ∀ w ∈ s, 0 < 1 + Y w := by
    intro w hw
    have := hqY w hw
    have := Nat.cast_nonneg (α := ℝ) (q w)
    linarith
  have hrecip : (∑ w ∈ s, (1 : ℝ) / (1 + Y w)) ≤ (j : ℝ) + 1 := by
    calc
      _ ≤ ∑ w ∈ s, (1 : ℝ) / ((q w : ℝ) + 1) := by
        apply sum_le_sum
        intro w hw
        apply one_div_le_one_div_of_le (by positivity)
        linarith [hqY w hw]
      _ = ∑ n ∈ s.image q, (1 : ℝ) / ((n : ℝ) + 1) :=
        (sum_image (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) hinj).symm
      _ ≤ ∑ n ∈ range (2 ^ j), (1 : ℝ) / ((n : ℝ) + 1) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨w, hw, rfl⟩ := mem_image.mp hn
          exact mem_range.mpr (hqb w hw)
        · intro n _ _
          positivity
      _ ≤ (j : ℝ) + 1 := harmonic_pow_two_le j
  have hcs := sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (r := fun _ => (1 : ℝ))
    (f := fun w => (1 : ℝ) / (1 + Y w))
    (g := fun w => 1 + Y w)
    (fun w hw => (div_pos zero_lt_one (hY w hw)).le)
    (fun w hw => (hY w hw).le)
    (fun w hw => by simp [(hY w hw).ne'])
  have hsum : 0 ≤ ∑ w ∈ s, (1 + Y w) := sum_nonneg fun w hw => (hY w hw).le
  calc
    _ ≤ (∑ w ∈ s, (1 : ℝ) / (1 + Y w)) * ∑ w ∈ s, (1 + Y w) := by
      simpa using hcs
    _ ≤ _ := mul_le_mul_of_nonneg_right hrecip hsum

theorem sum_inverse_square_Ico_le (k n : ℕ) (hk : 1 ≤ k) :
    (∑ a ∈ Ico k n, (1 : ℝ) / (a : ℝ) ^ 2) ≤ 2 / (k : ℝ) := by
  by_cases hkn : k ≤ n
  · have hp : ∀ a ∈ Ico k n, (1 : ℝ) / (a : ℝ) ^ 2 ≤
        2 * ((1 : ℝ) / a - 1 / ((a : ℝ) + 1)) := by
      intro a ha
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast hk.trans (mem_Ico.mp ha).1
      have ha0 : (0 : ℝ) < a := by linarith
      have ha2 : (0 : ℝ) < (a : ℝ) + 1 := by linarith
      have heq : 2 * ((1 : ℝ) / a - 1 / ((a : ℝ) + 1)) =
          2 / ((a : ℝ) * ((a : ℝ) + 1)) := by
        field_simp
        ring
      rw [heq]
      apply (div_le_div_iff₀ (sq_pos_of_pos ha0) (mul_pos ha0 ha2)).mpr
      nlinarith
    have ht := sum_Ico_sub (f := fun a : ℕ => (1 : ℝ) / a) hkn
    push_cast at ht
    rw [sum_sub_distrib] at ht
    calc
      _ ≤ ∑ a ∈ Ico k n, 2 * ((1 : ℝ) / a - 1 / ((a : ℝ) + 1)) :=
        sum_le_sum hp
      _ = 2 * ((1 : ℝ) / k - 1 / n) := by
        rw [← mul_sum, sum_sub_distrib]
        linarith
      _ ≤ 2 / (k : ℝ) := by
        have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
        calc
          _ ≤ 2 * ((1 : ℝ) / k) :=
            mul_le_mul_of_nonneg_left (sub_le_self _ this) (by norm_num)
          _ = _ := by ring
  · rw [Ico_eq_empty_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hkn)), sum_empty]
    positivity

theorem sum_inverse_square_le (s : Finset ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hs : ∀ a ∈ s, k ≤ a) :
    (∑ a ∈ s, (1 : ℝ) / (a : ℝ) ^ 2) ≤ 2 / (k : ℝ) := by
  have hsub : s ⊆ Ico k (s.sup id + 1) := by
    intro a ha
    exact mem_Ico.mpr ⟨hs a ha, Nat.lt_succ_of_le (le_sup (f := id) ha)⟩
  calc
    _ ≤ ∑ a ∈ Ico k (s.sup id + 1), (1 : ℝ) / (a : ℝ) ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro a _ _
      positivity
    _ ≤ _ := sum_inverse_square_Ico_le k (s.sup id + 1) hk

theorem weighted_sum_sq_le (s : Finset ℕ) (k : ℕ) (z : ℕ → ℝ)
    (hk : 1 ≤ k) (hs : ∀ a ∈ s, k ≤ a) :
    (∑ a ∈ s, z a) ^ 2 ≤ (2 / (k : ℝ)) * ∑ a ∈ s, (a : ℝ) ^ 2 * (z a) ^ 2 := by
  have hcs := sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (r := z) (f := fun a => (1 : ℝ) / (a : ℝ) ^ 2)
    (g := fun a => (a : ℝ) ^ 2 * (z a) ^ 2)
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun a ha => by
      have ha0 : (a : ℝ) ≠ 0 := by
        have : 1 ≤ a := hk.trans (hs a ha)
        positivity
      field_simp)
  exact hcs.trans (mul_le_mul_of_nonneg_right (sum_inverse_square_le s k hk hs)
    (sum_nonneg fun _ _ => by positivity))

end CollatzCylinderPacking.Arithmetic.FairEnergy
