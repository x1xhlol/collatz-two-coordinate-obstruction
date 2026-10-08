import CanonicalSyracuseSeries

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCylinderPacking.Arithmetic

theorem sequenceWord_take_prefix {k n : ℕ} (hn : n ≤ k) (f : ℕ → ℕ) :
    (wordList k (sequenceWord k f)).take n = wordList n (sequenceWord n f) := by
  induction k generalizing n f with
  | zero =>
    have : n = 0 := by omega
    subst n
    rfl
  | succ k ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change (f 0 + 1) :: (wordList k (sequenceWord k (fun i => f (i + 1)))).take n =
        (f 0 + 1) :: wordList n (sequenceWord n (fun i => f (i + 1)))
      rw [ih (by omega)]

theorem sequenceWord_sum (k : ℕ) (f : ℕ → ℕ) :
    (wordList k (sequenceWord k f)).sum = ∑ i ∈ Finset.range k, (f i + 1) := by
  rw [wordList_sum, ← sum_word_coordinates]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (sequenceWord_eq_iff k f (sequenceWord k f)).mp rfl i (Finset.mem_range.mp hi)]

theorem sequenceWord_prefix_sum {k n : ℕ} (hn : n ≤ k) (f : ℕ → ℕ) :
    ((wordList k (sequenceWord k f)).take n).sum = ∑ i ∈ Finset.range n, (f i + 1) := by
  rw [sequenceWord_take_prefix hn, sequenceWord_sum]

/-- The canonical variable is the limit of the usual Syracuse series with
the cumulative positive geometric exponents written directly. -/
theorem canonical_variable_explicit_series (f : ℕ → ℕ) :
    Tendsto (fun k => ∑ j ∈ Finset.range k,
      (3 : ℤ_[3]) ^ j * (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^
        (∑ i ∈ Finset.range (j + 1), (f i + 1)))
      atTop (𝓝 (canonicalSyracuseVariable f)) := by
  have he (k : ℕ) :
      (∑ j ∈ Finset.range k,
        (3 : ℤ_[3]) ^ j * (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^
          ((wordList k (sequenceWord k f)).take (j + 1)).sum) =
      ∑ j ∈ Finset.range k,
        (3 : ℤ_[3]) ^ j * (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^
          (∑ i ∈ Finset.range (j + 1), (f i + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sequenceWord_prefix_sum (by have := Finset.mem_range.mp hj; omega)]
  simpa only [he] using canonical_variable_series_limit f

theorem canonical_truncated_tendsto (f : ℕ → ℕ) :
    Tendsto (fun k => padicTruncatedSeries (wordList k (sequenceWord k f)))
      atTop (𝓝 (canonicalSyracuseVariable f)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => canonical_series_approximation_bound k f)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- The exact affine recursion of the infinite Syracuse random variable. -/
theorem canonical_variable_affine_recursion (f : ℕ → ℕ) :
    canonicalSyracuseVariable f =
      (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (f 0 + 1) *
        (1 + 3 * canonicalSyracuseVariable (fun i => f (i + 1))) := by
  have hleft := (canonical_truncated_tendsto f).comp (tendsto_add_atTop_nat 1)
  have hright := ((canonical_truncated_tendsto (fun i => f (i + 1))).const_mul 3).const_add 1
  have hright := hright.const_mul ((↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (f 0 + 1))
  exact tendsto_nhds_unique hleft hright

#print axioms canonical_variable_explicit_series
#print axioms canonical_variable_affine_recursion

end CollatzCylinderPacking.Arithmetic
