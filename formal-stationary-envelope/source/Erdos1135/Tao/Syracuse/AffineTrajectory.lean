import Erdos1135.Tao.Syracuse.AffineEnvelope

/-!
# Syracuse Affine Trajectory Projectivity

This neutral leaf identifies prefix and tail valuation lists and applies the
exact affine formula to arbitrary trajectory segments. It contains no
Section 5 schedule, source window, or probability definitions.
-/

namespace Erdos1135
namespace Tao

/-- Every iterate of an odd source is odd. -/
theorem syracuse_iterate_odd_trajectory
    (n N : ℕ) (hN : Odd N) : Odd ((syracuse^[n]) N) := by
  induction n generalizing N with
  | zero => simpa using hN
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (syracuse N) (syracuse_odd N)

/-- Actual positive valuation lists split at an arbitrary time. -/
theorem syracuseValuationPNatList_add
    (m n N : ℕ) (hN : Odd N) :
    syracuseValuationPNatList (m + n) N hN =
      syracuseValuationPNatList m N hN ++
        syracuseValuationPNatList n ((syracuse^[m]) N)
          (syracuse_iterate_odd_trajectory m N hN) := by
  induction m generalizing N with
  | zero =>
      simp [syracuseValuationPNatList]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [syracuseValuationPNatList, List.cons_append]
      rw [ih (syracuse N) (syracuse_odd N)]
      congr 2

/-- Taking the first `m` entries recovers the first `m` valuations. -/
theorem syracuseValuationPNatList_take
    (m n N : ℕ) (hN : Odd N) :
    (syracuseValuationPNatList (m + n) N hN).take m =
      syracuseValuationPNatList m N hN := by
  rw [syracuseValuationPNatList_add]
  simp [syracuseValuationPNatList_length]

/-- Dropping the first `m` entries recovers the valuations from time `m`. -/
theorem syracuseValuationPNatList_drop
    (m n N : ℕ) (hN : Odd N) :
    (syracuseValuationPNatList (m + n) N hN).drop m =
      syracuseValuationPNatList n ((syracuse^[m]) N)
        (syracuse_iterate_odd_trajectory m N hN) := by
  rw [syracuseValuationPNatList_add]
  simp [syracuseValuationPNatList_length]

theorem syracuseValuationPNatList_take_of_le
    {r j N : ℕ} (hN : Odd N) (hj : j ≤ r) :
    (syracuseValuationPNatList r N hN).take j =
      syracuseValuationPNatList j N hN := by
  simpa [Nat.add_sub_of_le hj] using
    syracuseValuationPNatList_take j (r - j) N hN

theorem syracuseValuationPNatList_drop_of_le
    {r j N : ℕ} (hN : Odd N) (hj : j ≤ r) :
    (syracuseValuationPNatList r N hN).drop j =
      syracuseValuationPNatList (r - j) ((syracuse^[j]) N)
        (syracuse_iterate_odd_trajectory j N hN) := by
  simpa [Nat.add_sub_of_le hj] using
    syracuseValuationPNatList_drop j (r - j) N hN

/-- Tuple weight is additive across concatenation. -/
theorem taoTupleWeight_append_trajectory (xs ys : List ℕ+) :
    taoTupleWeight (xs ++ ys) = taoTupleWeight xs + taoTupleWeight ys := by
  simp [taoTupleWeight]

theorem taoTupleWeight_take_add_drop_trajectory (as : List ℕ+) (j : ℕ) :
    taoTupleWeight (as.take j) + taoTupleWeight (as.drop j) =
      taoTupleWeight as := by
  rw [← taoTupleWeight_append_trajectory, List.take_append_drop]

theorem taoTupleWeight_drop_eq_sub_take_trajectory
    (as : List ℕ+) (j : ℕ) :
    taoTupleWeight (as.drop j) =
      taoTupleWeight as - taoTupleWeight (as.take j) := by
  have h := taoTupleWeight_take_add_drop_trajectory as j
  omega

/-- The affine main term is below the actual iterate because the offset is
nonnegative. -/
theorem affineMainTerm_le_syracuse_iterate
    (n N : ℕ) (hN : Odd N) :
    (3 : ℚ) ^ n /
          (2 : ℚ) ^ taoTupleWeight (syracuseValuationPNatList n N hN) * N ≤
      ((syracuse^[n]) N : ℚ) := by
  let as := syracuseValuationPNatList n N hN
  have hlength : as.length = n :=
    syracuseValuationPNatList_length n N hN
  rw [syracuse_iterate_eq_taoAffList, taoAffList_closed]
  rw [hlength]
  exact le_add_of_nonneg_right (taoOffsetList_nonneg as)

/-- The point at time `j` is the affine image under the retained prefix. -/
theorem syracuse_iterate_eq_take_taoAffList
    {r j N : ℕ} (hN : Odd N) (hj : j ≤ r) :
    ((syracuse^[j]) N : ℚ) =
      taoAffList ((syracuseValuationPNatList r N hN).take j) (N : ℚ) := by
  rw [syracuseValuationPNatList_take_of_le hN hj]
  exact syracuse_iterate_eq_taoAffList j N hN

/-- The endpoint at time `r` is the affine image of the time-`j` point under
the actual tail valuation list. -/
theorem syracuse_iterate_eq_tail_taoAffList
    {r j N : ℕ} (hN : Odd N) (hj : j ≤ r) :
    ((syracuse^[r]) N : ℚ) =
      taoAffList ((syracuseValuationPNatList r N hN).drop j)
        (((syracuse^[j]) N : ℕ) : ℚ) := by
  have htail := syracuse_iterate_eq_taoAffList (r - j)
    ((syracuse^[j]) N) (syracuse_iterate_odd_trajectory j N hN)
  rw [syracuseValuationPNatList_drop_of_le hN hj]
  rw [← htail]
  norm_cast
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hj]

/-- Coarse affine upper envelope for any tail segment of an odd trajectory. -/
theorem syracuse_iterate_le_tail_affine_envelope
    {r j N : ℕ} (hN : Odd N) (hj : j ≤ r) :
    ((syracuse^[r]) N : ℚ) ≤
      (3 : ℚ) ^ (r - j) /
          (2 : ℚ) ^
            taoTupleWeight ((syracuseValuationPNatList r N hN).drop j) *
          ((syracuse^[j]) N) +
        (3 : ℚ) ^ (r - j) := by
  have htail := syracuse_iterate_le_affine_envelope (r - j)
    ((syracuse^[j]) N) (syracuse_iterate_odd_trajectory j N hN)
  rw [syracuseValuationPNatList_drop_of_le hN hj]
  have hiterate :
      (syracuse^[r - j]) ((syracuse^[j]) N) = (syracuse^[r]) N := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hj]
  simpa only [hiterate] using htail

/-- Real-valued form of the tail envelope for analytic consumers. -/
theorem syracuse_iterate_le_tail_affine_envelope_real
    {r j N : ℕ} (hN : Odd N) (hj : j ≤ r) :
    ((syracuse^[r]) N : ℝ) ≤
      (3 : ℝ) ^ (r - j) /
          (2 : ℝ) ^
            taoTupleWeight ((syracuseValuationPNatList r N hN).drop j) *
          ((syracuse^[j]) N) +
        (3 : ℝ) ^ (r - j) := by
  have hq := syracuse_iterate_le_tail_affine_envelope hN hj
  have hr := (Rat.cast_le (K := ℝ)).2 hq
  norm_num at hr
  exact hr

end Tao
end Erdos1135
