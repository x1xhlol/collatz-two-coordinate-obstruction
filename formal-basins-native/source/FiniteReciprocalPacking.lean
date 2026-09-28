import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace CollatzCanonical.ReciprocalPacking

noncomputable def tailConstant (K b : ℝ) : ℝ :=
  K * (2 : ℝ) ^ b / (1 - (2 : ℝ) ^ (b - 1))

noncomputable def dyadicIndex (M : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (Real.log ((n : ℝ) / M) / Real.log 2)

/-- Each point above a positive cutoff belongs to its logarithmically indexed dyadic shell. -/
theorem dyadicIndex_bounds (M : ℝ) (n : ℕ) (hM : 0 < M) (hn : M ≤ (n : ℝ)) :
    (2 : ℝ) ^ dyadicIndex M n * M ≤ n ∧
      (n : ℝ) < (2 : ℝ) ^ (dyadicIndex M n + 1) * M := by
  have hx : 1 ≤ (n : ℝ) / M := (le_div_iff₀ hM).mpr (by simpa using hn)
  have hx0 : 0 < (n : ℝ) / M := lt_of_lt_of_le zero_lt_one hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : (dyadicIndex M n : ℝ) ≤ Real.log ((n : ℝ) / M) / Real.log 2 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hx) hlog2.le)
  have hhi : Real.log ((n : ℝ) / M) / Real.log 2 < ((dyadicIndex M n + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (Real.log ((n : ℝ) / M) / Real.log 2)
  have hl := Real.exp_le_exp.mpr ((le_div_iff₀ hlog2).mp hlo)
  have hh := Real.exp_lt_exp.mpr ((div_lt_iff₀ hlog2).mp hhi)
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hx0] at hl hh
  exact ⟨(le_div_iff₀ hM).mp hl, (div_lt_iff₀ hM).mp hh⟩

/-- The reciprocal budget of one dyadic shell is one term of a geometric series. -/
theorem shell_budget_identity (K b M : ℝ) (j : ℕ) (hM : 0 < M) :
    (K * ((2 : ℝ) ^ (j + 1) * M) ^ b) * (1 / ((2 : ℝ) ^ j * M)) =
      (K * (2 : ℝ) ^ b * M ^ (b - 1)) * ((2 : ℝ) ^ (b - 1)) ^ j := by
  rw [Real.mul_rpow (by positivity) hM.le, ← Real.rpow_pow_comm (by norm_num),
    Real.rpow_sub hM b 1, Real.rpow_one,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2) b 1, Real.rpow_one, div_pow, pow_succ]
  field_simp

/-- The uniform reciprocal constant is nonnegative throughout the sublinear range. -/
theorem tailConstant_nonneg (K b : ℝ) (hK : 0 ≤ K) (hb : b < 1) :
    0 ≤ tailConstant K b := by
  have hr : (2 : ℝ) ^ (b - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hb)
  exact div_nonneg (mul_nonneg hK (Real.rpow_nonneg (by norm_num) b)) (sub_nonneg.mpr hr.le)

/-- A power bound on the counting function gives a uniform reciprocal tail for every finite set. -/
theorem finite_reciprocal_tail (S : Finset ℕ) (K b : ℝ)
    (hK : 0 ≤ K) (hb : 0 < b) (hb1 : b < 1)
    (hcount : ∀ X : ℝ, 1 ≤ X →
      ((S.filter (fun n : ℕ => (n : ℝ) ≤ X)).card : ℝ) ≤ K * X ^ b) :
    ∀ M : ℝ, 1 ≤ M →
      (∑ n ∈ S.filter (fun n : ℕ => M ≤ (n : ℝ)), 1 / (n : ℝ)) ≤
        tailConstant K b * M ^ (b - 1) := by
  classical
  intro M hM
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let T := S.filter (fun n : ℕ => M ≤ (n : ℝ))
  let J := T.image (dyadicIndex M)
  let r := (2 : ℝ) ^ (b - 1)
  let C := K * (2 : ℝ) ^ b * M ^ (b - 1)
  have hr : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hb1)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg hK (Real.rpow_nonneg (by norm_num) b)) (Real.rpow_nonneg hM0.le _)
  have hsplit : (∑ n ∈ T, 1 / (n : ℝ)) =
      ∑ j ∈ J, ∑ n ∈ T.filter (fun n => dyadicIndex M n = j), 1 / (n : ℝ) :=
    (Finset.sum_fiberwise_of_maps_to
      (fun n hn => Finset.mem_image_of_mem (dyadicIndex M) hn) (fun n => 1 / (n : ℝ))).symm
  have hshell (j : ℕ) :
      (∑ n ∈ T.filter (fun n => dyadicIndex M n = j), 1 / (n : ℝ)) ≤ C * r ^ j := by
    let F := T.filter (fun n => dyadicIndex M n = j)
    have hbounds (n : ℕ) (hn : n ∈ F) :
        (2 : ℝ) ^ j * M ≤ n ∧ (n : ℝ) < (2 : ℝ) ^ (j + 1) * M := by
      have hnT := (Finset.mem_filter.mp hn).1
      have hnM := (Finset.mem_filter.mp hnT).2
      have he := (Finset.mem_filter.mp hn).2
      simpa only [he] using dyadicIndex_bounds M n hM0 hnM
    have hsub : F ⊆ S.filter (fun n : ℕ => (n : ℝ) ≤ (2 : ℝ) ^ (j + 1) * M) := by
      intro n hn
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1, (hbounds n hn).2.le⟩
    have hX : 1 ≤ (2 : ℝ) ^ (j + 1) * M := by
      have hp : 1 ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hcard : (F.card : ℝ) ≤ K * ((2 : ℝ) ^ (j + 1) * M) ^ b :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount _ hX)
    have hden : 0 < (2 : ℝ) ^ j * M := mul_pos (pow_pos (by norm_num) _) hM0
    calc
      (∑ n ∈ F, 1 / (n : ℝ)) ≤ ∑ _n ∈ F, 1 / ((2 : ℝ) ^ j * M) :=
        Finset.sum_le_sum (fun n hn => one_div_le_one_div_of_le hden (hbounds n hn).1)
      _ = (F.card : ℝ) * (1 / ((2 : ℝ) ^ j * M)) := by simp
      _ ≤ (K * ((2 : ℝ) ^ (j + 1) * M) ^ b) * (1 / ((2 : ℝ) ^ j * M)) :=
        mul_le_mul_of_nonneg_right hcard (one_div_nonneg.mpr hden.le)
      _ = C * r ^ j := shell_budget_identity K b M j hM0
  have hgeom : (∑ j ∈ J, r ^ j) ≤ (1 - r)⁻¹ := by
    have hh := (summable_geometric_of_lt_one hr hr1).sum_le_tsum J
      (fun j _ => pow_nonneg hr j)
    rwa [tsum_geometric_of_lt_one hr hr1] at hh
  calc
    (∑ n ∈ S.filter (fun n : ℕ => M ≤ (n : ℝ)), 1 / (n : ℝ)) =
        ∑ j ∈ J, ∑ n ∈ T.filter (fun n => dyadicIndex M n = j), 1 / (n : ℝ) := hsplit
    _ ≤ ∑ j ∈ J, C * r ^ j := Finset.sum_le_sum (fun j _ => hshell j)
    _ = C * ∑ j ∈ J, r ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeom hC
    _ = tailConstant K b * M ^ (b - 1) := by
      dsimp [C, r, tailConstant]
      ring

/-- Reindexing by distinct values transfers the finite-set bound to an arbitrary finite family. -/
theorem finite_indexed_reciprocal_tail {ι : Type*} (I : Finset ι) (x : ι → ℕ)
    (K b : ℝ) (hK : 0 ≤ K) (hb : 0 < b) (hb1 : b < 1)
    (hinj : Set.InjOn x I)
    (hcount : ∀ X : ℝ, 1 ≤ X →
      ((I.filter (fun i => (x i : ℝ) ≤ X)).card : ℝ) ≤ K * X ^ b) :
    ∀ M : ℝ, 1 ≤ M →
      (∑ i ∈ I.filter (fun i => M ≤ (x i : ℝ)), 1 / (x i : ℝ)) ≤
        tailConstant K b * M ^ (b - 1) := by
  classical
  have hcount' : ∀ X : ℝ, 1 ≤ X →
      (((I.image x).filter (fun n : ℕ => (n : ℝ) ≤ X)).card : ℝ) ≤ K * X ^ b := by
    intro X hX
    rw [Finset.filter_image, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    exact hcount X hX
  intro M hM
  have ht := finite_reciprocal_tail (I.image x) K b hK hb hb1 hcount' M hM
  rw [Finset.filter_image, Finset.sum_image (hinj.mono (Finset.filter_subset _ _))] at ht
  exact ht

end CollatzCanonical.ReciprocalPacking
