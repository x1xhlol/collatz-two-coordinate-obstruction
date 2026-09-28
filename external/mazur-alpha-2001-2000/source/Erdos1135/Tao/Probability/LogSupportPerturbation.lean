import Erdos1135.Tao.Probability.LogWindow

/-!
# Normalized Logarithmic Support Perturbation

This neutral leaf compares logarithmic probabilities on two finite supports.
The error is controlled by the weighted symmetric difference and the smaller
normalizing mass. No Syracuse map or Tao window endpoint policy appears here.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

local instance logSupportPerturbationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Weighted symmetric-difference mass, written as the sum of the two
directed differences. -/
noncomputable def logFinsetSymmDiffMass (S T : Finset ℕ) : ℝ :=
  logFinsetMass (S \ T) + logFinsetMass (T \ S)

/-- Logarithmic finite-set mass is monotone under support inclusion. -/
theorem logFinsetMass_mono {S T : Finset ℕ} (hST : S ⊆ T) :
    logFinsetMass S ≤ logFinsetMass T := by
  unfold logFinsetMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hST fun n _hn _hnot =>
    logNatWeight_nonneg n

/-- Splitting a finite support into its directed difference and intersection
preserves its logarithmic mass. -/
theorem logFinsetMass_sdiff_add_inter (S T : Finset ℕ) :
    logFinsetMass (S \ T) + logFinsetMass (S ∩ T) =
      logFinsetMass S := by
  unfold logFinsetMass
  rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S T),
    Finset.sdiff_union_inter]

/-- The discrepancy of two unnormalized support masses is bounded by their
weighted symmetric difference. -/
theorem abs_logFinsetMass_sub_le_symmDiffMass (S T : Finset ℕ) :
    |logFinsetMass S - logFinsetMass T| ≤
      logFinsetSymmDiffMass S T := by
  have hS := logFinsetMass_sdiff_add_inter S T
  have hT := logFinsetMass_sdiff_add_inter T S
  have hcommon : logFinsetMass (T ∩ S) = logFinsetMass (S ∩ T) := by
    rw [Finset.inter_comm]
  have hleft := logFinsetMass_nonneg (S \ T)
  have hright := logFinsetMass_nonneg (T \ S)
  rw [abs_le]
  constructor <;>
    simp only [logFinsetSymmDiffMass] <;>
    nlinarith

/-- Restricting both supports by one ambient event cannot increase their
weighted symmetric-difference mass. -/
theorem logFinsetSymmDiffMass_filter_le
    (S T : Finset ℕ) (E : Set ℕ) :
    logFinsetSymmDiffMass
        (S.filter fun n => n ∈ E) (T.filter fun n => n ∈ E) ≤
      logFinsetSymmDiffMass S T := by
  classical
  have hleft :
      (S.filter fun n => n ∈ E) \ (T.filter fun n => n ∈ E) ⊆ S \ T := by
    intro n hn
    simp only [Finset.mem_sdiff, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1.1, fun hnT => hn.2 ⟨hnT, hn.1.2⟩⟩
  have hright :
      (T.filter fun n => n ∈ E) \ (S.filter fun n => n ∈ E) ⊆ T \ S := by
    intro n hn
    simp only [Finset.mem_sdiff, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1.1, fun hnS => hn.2 ⟨hnS, hn.1.2⟩⟩
  exact add_le_add (logFinsetMass_mono hleft) (logFinsetMass_mono hright)

/-- Event numerators on two finite supports differ by at most the weighted
symmetric-difference mass of the original supports. -/
theorem abs_logFinsetEventMass_sub_le_symmDiffMass
    (S T : Finset ℕ) (E : Set ℕ) :
    |logFinsetMass (S.filter fun n => n ∈ E) -
        logFinsetMass (T.filter fun n => n ∈ E)| ≤
      logFinsetSymmDiffMass S T := by
  exact (abs_logFinsetMass_sub_le_symmDiffMass
    (S.filter fun n => n ∈ E) (T.filter fun n => n ∈ E)).trans
      (logFinsetSymmDiffMass_filter_le S T E)

private theorem abs_normalized_sub_le_two_mul_div
    {a b s t d m : ℝ}
    (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hsa : s ≤ a) (htb : t ≤ b)
    (hst : |s - t| ≤ d) (hab : |a - b| ≤ d) :
    |s / a - t / b| ≤ 2 * d / m := by
  have ha : 0 < a := hm.trans_le hma
  have hb : 0 < b := hm.trans_le hmb
  have hd : 0 ≤ d := (abs_nonneg (s - t)).trans hst
  have hstUpper : s - t ≤ d := (abs_le.mp hst).2
  have htsUpper : t - s ≤ d := by
    have := (abs_le.mp hst).1
    linarith
  have habUpper : a - b ≤ d := (abs_le.mp hab).2
  have hbaUpper : b - a ≤ d := by
    have := (abs_le.mp hab).1
    linarith
  have hforwardRewrite :
      s / a - t / b = ((s - t) * b + t * (b - a)) / (a * b) := by
    field_simp [ha.ne', hb.ne']
    ring
  have hreverseRewrite :
      t / b - s / a = ((t - s) * a + s * (a - b)) / (a * b) := by
    field_simp [ha.ne', hb.ne']
    ring
  have hforwardNumerator :
      (s - t) * b + t * (b - a) ≤ 2 * d * b := by
    calc
      (s - t) * b + t * (b - a) ≤ d * b + t * d :=
        add_le_add
          (mul_le_mul_of_nonneg_right hstUpper hb.le)
          (mul_le_mul_of_nonneg_left hbaUpper ht0)
      _ ≤ d * b + b * d :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right htb hd)
      _ = 2 * d * b := by ring
  have hreverseNumerator :
      (t - s) * a + s * (a - b) ≤ 2 * d * a := by
    calc
      (t - s) * a + s * (a - b) ≤ d * a + s * d :=
        add_le_add
          (mul_le_mul_of_nonneg_right htsUpper ha.le)
          (mul_le_mul_of_nonneg_left habUpper hs0)
      _ ≤ d * a + a * d :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hsa hd)
      _ = 2 * d * a := by ring
  have hforward : s / a - t / b ≤ 2 * d / m := by
    rw [hforwardRewrite]
    calc
      ((s - t) * b + t * (b - a)) / (a * b) ≤
          (2 * d * b) / (a * b) :=
        div_le_div_of_nonneg_right hforwardNumerator (mul_pos ha hb).le
      _ = 2 * d / a := by field_simp [ha.ne', hb.ne']
      _ ≤ 2 * d / m :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hd) hm hma
  have hreverse : t / b - s / a ≤ 2 * d / m := by
    rw [hreverseRewrite]
    calc
      ((t - s) * a + s * (a - b)) / (a * b) ≤
          (2 * d * a) / (a * b) :=
        div_le_div_of_nonneg_right hreverseNumerator (mul_pos ha hb).le
      _ = 2 * d / b := by field_simp [ha.ne', hb.ne']
      _ ≤ 2 * d / m :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hd) hm hmb
  rw [abs_le]
  constructor <;> linarith

/-- Safe normalized perturbation bound for arbitrary ambient events. The
factor `2` pays once for the event numerator and once for renormalization. -/
theorem abs_logFinsetProb_sub_le_two_symmDiffMass_div_min
    {S T : Finset ℕ}
    (hS : 0 < logFinsetMass S) (hT : 0 < logFinsetMass T)
    (E : Set ℕ) :
    |logFinsetProb S E - logFinsetProb T E| ≤
      2 * logFinsetSymmDiffMass S T /
        min (logFinsetMass S) (logFinsetMass T) := by
  classical
  let s := logFinsetMass (S.filter fun n => n ∈ E)
  let t := logFinsetMass (T.filter fun n => n ∈ E)
  let a := logFinsetMass S
  let b := logFinsetMass T
  let d := logFinsetSymmDiffMass S T
  have hm : 0 < min a b := lt_min hS hT
  have hs0 : 0 ≤ s := logFinsetMass_nonneg _
  have ht0 : 0 ≤ t := logFinsetMass_nonneg _
  have hsa : s ≤ a := logFinsetMass_mono (Finset.filter_subset _ _)
  have htb : t ≤ b := logFinsetMass_mono (Finset.filter_subset _ _)
  have hst : |s - t| ≤ d :=
    abs_logFinsetEventMass_sub_le_symmDiffMass S T E
  have hab : |a - b| ≤ d := abs_logFinsetMass_sub_le_symmDiffMass S T
  have hnormalized := abs_normalized_sub_le_two_mul_div
    hm (min_le_left _ _) (min_le_right _ _)
    hs0 ht0 hsa htb hst hab
  simpa only [logFinsetProb, s, t, a, b, d, logFinsetMass] using hnormalized

end

end Tao
end Erdos1135
