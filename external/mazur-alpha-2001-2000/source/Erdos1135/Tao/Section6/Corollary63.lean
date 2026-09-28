import Erdos1135.Tao.Syracuse.AffineReverse
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Section 6 Corollary 6.3 Star Surface

This module records the repaired Corollary 6.3 statement surface and the
deterministic final adapter from small congruent cleared offsets to tuple
equality.  The analytic 3-adic separation and smallness estimates remain open.
-/

namespace Erdos1135
namespace Tao

/-- Source prefix/interval weight `a_[i+1,j]`, with zero-based Lean endpoints. -/
def taoSection6IntervalWeight (as : List ℕ+) (i j : ℕ) : ℕ :=
  (((as.drop i).take (j - i)).map fun a : ℕ+ => (a : ℕ)).sum

/-- The repaired lower reference point `Q = n log_2 3 - C_A^2 log n`. -/
noncomputable def taoCor63StarQ (CA : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log 3 / Real.log 2) - CA ^ 2 * Real.log (n : ℝ)

/-- Repaired range `(6.8 star)`: `Q < l <= Q + 2 C_A log n`. -/
noncomputable def taoCor63StarLRange (CA : ℝ) (n l : ℕ) : Prop :=
  taoCor63StarQ CA n < (l : ℝ) ∧
    (l : ℝ) ≤ taoCor63StarQ CA n + 2 * CA * Real.log (n : ℝ)

/--
Inclusive repaired form of the local concentration hypothesis `(6.12)`, using
zero-based Lean endpoints: source `0 <= i < j <= k+1` is encoded by
`i < j` and `j <= as.length`.
-/
noncomputable def taoCor63StarInclusiveTypical
    (CA : ℝ) (n : ℕ) (as : List ℕ+) : Prop :=
  ∀ i j : ℕ, i < j → j ≤ as.length →
    |((taoSection6IntervalWeight as i j : ℕ) : ℝ) -
        2 * (((j - i : ℕ) : ℝ))| ≤
      CA * (Real.sqrt ((((j - i : ℕ) : ℝ)) * Real.log (n : ℝ)) +
        Real.log (n : ℝ))

/--
Cleared offset sum appearing in the proof after multiplying Tao's `F` offset by
`2^l`: `sum_j 3^(j-1) 2^(l-a_[1,j])`.
-/
def taoCor63ClearedOffsetSumFrom
    (l idx pref : ℕ) : List ℕ+ → ℕ
  | [] => 0
  | a :: as =>
      3 ^ idx * 2 ^ (l - (pref + (a : ℕ))) +
        taoCor63ClearedOffsetSumFrom l (idx + 1) (pref + (a : ℕ)) as

/-- Top-level cleared offset sum, starting at source index `j = 1`. -/
def taoCor63ClearedOffsetSum (l : ℕ) (as : List ℕ+) : ℕ :=
  taoCor63ClearedOffsetSumFrom l 0 0 as

/--
Repaired Corollary 6.3 statement in cleared-residue form.

This records the operator-directed replacement of printed `(6.8)` and
strict-range `(6.12)` by `(6.8 star)` and inclusive `(6.12)`.  It is
deliberately a `Prop` target, not a theorem.
-/
noncomputable def TaoCor63StarClearedSeparationStatement : Prop :=
  ∀ CA : ℝ, 17 ≤ CA → ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    ∀ k l : ℕ, taoCor63StarLRange CA n l →
      ∀ as bs : List ℕ+,
        as.length = k + 1 →
        bs.length = k + 1 →
        taoTupleWeight as = l →
        taoTupleWeight bs = l →
        taoCor63StarInclusiveTypical CA n as →
        taoCor63StarInclusiveTypical CA n bs →
        Nat.ModEq (3 ^ n)
          (taoCor63ClearedOffsetSum l as)
          (taoCor63ClearedOffsetSum l bs) →
        as = bs

/-- The error term appearing in repaired `(6.12)` for a prefix of length `j`. -/
noncomputable def taoCor63PrefixError (CA : ℝ) (n j : ℕ) : ℝ :=
  CA * (Real.sqrt ((j : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ))

/-- Inclusive typicality specialized to the source prefix interval `a_[1,j]`. -/
theorem taoCor63StarInclusiveTypical_prefix_abs
    {CA : ℝ} {n : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    {j : ℕ} (hj_pos : 0 < j) (hj_len : j ≤ as.length) :
    |((taoSection6IntervalWeight as 0 j : ℕ) : ℝ) - 2 * (j : ℝ)| ≤
      taoCor63PrefixError CA n j := by
  simpa [taoCor63PrefixError] using htyp 0 j hj_pos hj_len

/-- Lower prefix-weight bound obtained from repaired inclusive typicality. -/
theorem taoCor63StarInclusiveTypical_prefix_lower
    {CA : ℝ} {n : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    {j : ℕ} (hj_pos : 0 < j) (hj_len : j ≤ as.length) :
    2 * (j : ℝ) - taoCor63PrefixError CA n j ≤
      ((taoSection6IntervalWeight as 0 j : ℕ) : ℝ) := by
  have h :=
    taoCor63StarInclusiveTypical_prefix_abs
      (CA := CA) (n := n) (as := as) htyp hj_pos hj_len
  have hleft := (abs_le.mp h).1
  linarith

/-- Upper prefix-weight bound obtained from repaired inclusive typicality. -/
theorem taoCor63StarInclusiveTypical_prefix_upper
    {CA : ℝ} {n : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    {j : ℕ} (hj_pos : 0 < j) (hj_len : j ≤ as.length) :
    ((taoSection6IntervalWeight as 0 j : ℕ) : ℝ) ≤
      2 * (j : ℝ) + taoCor63PrefixError CA n j := by
  have h :=
    taoCor63StarInclusiveTypical_prefix_abs
      (CA := CA) (n := n) (as := as) htyp hj_pos hj_len
  have hright := (abs_le.mp h).2
  linarith

theorem taoSection6IntervalWeight_zero_length (as : List ℕ+) :
    taoSection6IntervalWeight as 0 as.length = taoTupleWeight as := by
  simp [taoSection6IntervalWeight, taoTupleWeight, List.map_eq_flatMap]

/-- Prefix typicality at the full source length, rewritten as tuple weight. -/
theorem taoCor63StarInclusiveTypical_total_abs
    {CA : ℝ} {n : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlen_pos : 0 < as.length) :
    |((taoTupleWeight as : ℕ) : ℝ) - 2 * (as.length : ℝ)| ≤
      taoCor63PrefixError CA n as.length := by
  have h :=
    taoCor63StarInclusiveTypical_prefix_abs
      (CA := CA) (n := n) (as := as) htyp hlen_pos le_rfl
  simpa [taoSection6IntervalWeight_zero_length as] using h

/-- Lower total-weight consequence of repaired inclusive typicality. -/
theorem taoCor63StarInclusiveTypical_total_lower
    {CA : ℝ} {n : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlen_pos : 0 < as.length) :
    2 * (as.length : ℝ) - taoCor63PrefixError CA n as.length ≤
      ((taoTupleWeight as : ℕ) : ℝ) := by
  have h :=
    taoCor63StarInclusiveTypical_prefix_lower
      (CA := CA) (n := n) (as := as) htyp hlen_pos le_rfl
  simpa [taoSection6IntervalWeight_zero_length as] using h

/-- Upper total-weight consequence of repaired inclusive typicality. -/
theorem taoCor63StarInclusiveTypical_total_upper
    {CA : ℝ} {n : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlen_pos : 0 < as.length) :
    ((taoTupleWeight as : ℕ) : ℝ) ≤
      2 * (as.length : ℝ) + taoCor63PrefixError CA n as.length := by
  have h :=
    taoCor63StarInclusiveTypical_prefix_upper
      (CA := CA) (n := n) (as := as) htyp hlen_pos le_rfl
  simpa [taoSection6IntervalWeight_zero_length as] using h

/-- Total-weight absolute estimate after fixing the source length and weight. -/
theorem taoCor63StarInclusiveTypical_weight_abs_of_length
    {CA : ℝ} {n k l : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlen : as.length = k + 1)
    (hweight : taoTupleWeight as = l) :
    |(l : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)| ≤
      taoCor63PrefixError CA n (k + 1) := by
  have hlen_pos : 0 < as.length := by
    omega
  have h :=
    taoCor63StarInclusiveTypical_total_abs
      (CA := CA) (n := n) (as := as) htyp hlen_pos
  simpa [hlen, hweight] using h

/-- Lower total-weight estimate after fixing the source length and weight. -/
theorem taoCor63StarInclusiveTypical_weight_lower_of_length
    {CA : ℝ} {n k l : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlen : as.length = k + 1)
    (hweight : taoTupleWeight as = l) :
    2 * ((k + 1 : ℕ) : ℝ) - taoCor63PrefixError CA n (k + 1) ≤
      (l : ℝ) := by
  have hlen_pos : 0 < as.length := by
    omega
  have h :=
    taoCor63StarInclusiveTypical_total_lower
      (CA := CA) (n := n) (as := as) htyp hlen_pos
  simpa [hlen, hweight] using h

/-- Upper total-weight estimate after fixing the source length and weight. -/
theorem taoCor63StarInclusiveTypical_weight_upper_of_length
    {CA : ℝ} {n k l : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlen : as.length = k + 1)
    (hweight : taoTupleWeight as = l) :
    (l : ℝ) ≤
      2 * ((k + 1 : ℕ) : ℝ) + taoCor63PrefixError CA n (k + 1) := by
  have hlen_pos : 0 < as.length := by
    omega
  have h :=
    taoCor63StarInclusiveTypical_total_upper
      (CA := CA) (n := n) (as := as) htyp hlen_pos
  simpa [hlen, hweight] using h

/-- The zero-based prefix interval weight is the tuple weight of `as.take j`. -/
theorem taoSection6IntervalWeight_zero_eq_tupleWeight_take
    (as : List ℕ+) (j : ℕ) :
    taoSection6IntervalWeight as 0 j = taoTupleWeight (as.take j) := by
  simp [taoSection6IntervalWeight, taoTupleWeight, Function.comp_def,
    ← List.map_eq_flatMap]

/-- Tuple weight is monotone under taking a prefix. -/
theorem taoTupleWeight_take_le (as : List ℕ+) (j : ℕ) :
    taoTupleWeight (as.take j) ≤ taoTupleWeight as := by
  induction as generalizing j with
  | nil =>
      simp [taoTupleWeight]
  | cons a as ih =>
      cases j with
      | zero =>
          simp [taoTupleWeight]
      | succ j =>
          exact Nat.add_le_add_left (ih j) (a : ℕ)

/-- Prefix interval weights are bounded by total tuple weight. -/
theorem taoSection6IntervalWeight_zero_le_tupleWeight
    (as : List ℕ+) (j : ℕ) :
    taoSection6IntervalWeight as 0 j ≤ taoTupleWeight as := by
  rw [taoSection6IntervalWeight_zero_eq_tupleWeight_take]
  exact taoTupleWeight_take_le as j

/-- Prefix interval weights are bounded by a named total weight. -/
theorem taoSection6IntervalWeight_zero_le_of_weight
    {as : List ℕ+} {j l : ℕ}
    (hweight : taoTupleWeight as = l) :
    taoSection6IntervalWeight as 0 j ≤ l := by
  simpa [hweight] using taoSection6IntervalWeight_zero_le_tupleWeight as j

/--
Cast the natural exponent `l - a_[1,j]` to a real subtraction, using the total
weight equality to justify the natural subtraction.
-/
theorem taoCor63PrefixExponent_natCast_sub_of_weight
    {as : List ℕ+} {j l : ℕ}
    (hweight : taoTupleWeight as = l) :
    (((l - taoSection6IntervalWeight as 0 j : ℕ) : ℕ) : ℝ) =
      (l : ℝ) - ((taoSection6IntervalWeight as 0 j : ℕ) : ℝ) := by
  have hle :
      taoSection6IntervalWeight as 0 j ≤ l :=
    taoSection6IntervalWeight_zero_le_of_weight hweight
  simpa using
    (Nat.cast_sub hle :
      (((l - taoSection6IntervalWeight as 0 j : ℕ) : ℕ) : ℝ) =
        (l : ℝ) - ((taoSection6IntervalWeight as 0 j : ℕ) : ℝ))

/-- Real prefix-exponent upper bound from the lower prefix-weight estimate. -/
theorem taoCor63StarPrefixExponent_upper
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n as)
    {j : ℕ} (hj_pos : 0 < j) (hj_len : j ≤ as.length) :
    (l : ℝ) - ((taoSection6IntervalWeight as 0 j : ℕ) : ℝ) ≤
      (l : ℝ) - (2 * (j : ℝ) - taoCor63PrefixError CA n j) := by
  have hprefix :=
    taoCor63StarInclusiveTypical_prefix_lower
      (CA := CA) (n := n) (as := as) htyp hj_pos hj_len
  exact sub_le_sub_left hprefix (l : ℝ)

/--
Natural prefix-exponent upper bound after casting `l - a_[1,j]` to `ℝ`.
-/
theorem taoCor63StarNatPrefixExponent_upper
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    {j : ℕ} (hj_pos : 0 < j) (hj_len : j ≤ as.length) :
    (((l - taoSection6IntervalWeight as 0 j : ℕ) : ℕ) : ℝ) ≤
      (l : ℝ) - (2 * (j : ℝ) - taoCor63PrefixError CA n j) := by
  rw [taoCor63PrefixExponent_natCast_sub_of_weight hweight]
  exact taoCor63StarPrefixExponent_upper
    (CA := CA) (n := n) (l := l) (as := as) htyp hj_pos hj_len

/-- The `idx`th cleared summand `3^idx * 2^(l-a_[1,idx+1])`. -/
def taoCor63ClearedSummand
    (l idx : ℕ) (as : List ℕ+) : ℕ :=
  3 ^ idx * 2 ^ (l - taoSection6IntervalWeight as 0 (idx + 1))

/-- Real cast of a cleared summand as a product of real powers. -/
theorem taoCor63ClearedSummand_real_cast
    (l idx : ℕ) (as : List ℕ+) :
    (taoCor63ClearedSummand l idx as : ℝ) =
      (3 : ℝ) ^ idx *
        (2 : ℝ) ^
          (((l - taoSection6IntervalWeight as 0 (idx + 1) : ℕ) : ℕ) : ℝ) := by
  simp [taoCor63ClearedSummand, Nat.cast_mul, Nat.cast_pow,
    Real.rpow_natCast]

/--
Pointwise real-power envelope for one cleared summand, before collecting the
`(3 / 4)^idx` geometric factor.
-/
theorem taoCor63ClearedSummand_real_le_prefixEnvelope
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    {idx : ℕ} (hidx : idx < as.length) :
    (taoCor63ClearedSummand l idx as : ℝ) ≤
      (3 : ℝ) ^ idx *
        (2 : ℝ) ^ ((l : ℝ) -
          (2 * ((idx + 1 : ℕ) : ℝ) -
            taoCor63PrefixError CA n (idx + 1))) := by
  have hidx_pos : 0 < idx + 1 := Nat.succ_pos idx
  have hidx_len : idx + 1 ≤ as.length := Nat.succ_le_of_lt hidx
  have hexp :
      (((l - taoSection6IntervalWeight as 0 (idx + 1) : ℕ) : ℕ) : ℝ) ≤
        (l : ℝ) -
          (2 * ((idx + 1 : ℕ) : ℝ) -
            taoCor63PrefixError CA n (idx + 1)) :=
    taoCor63StarNatPrefixExponent_upper
      (CA := CA) (n := n) (l := l) (as := as) hweight htyp
      hidx_pos hidx_len
  have hpow :
      (2 : ℝ) ^
          (((l - taoSection6IntervalWeight as 0 (idx + 1) : ℕ) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((l : ℝ) -
          (2 * ((idx + 1 : ℕ) : ℝ) -
            taoCor63PrefixError CA n (idx + 1))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [taoCor63ClearedSummand_real_cast]
  exact mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) idx)

/-- Rewrite the one-summand prefix envelope as a geometric `(3 / 4)^idx` term. -/
theorem taoCor63PrefixEnvelope_eq_geometric
    (l idx : ℕ) (E : ℝ) :
    (3 : ℝ) ^ idx *
        (2 : ℝ) ^ ((l : ℝ) -
          (2 * ((idx + 1 : ℕ) : ℝ) - E)) =
      (2 : ℝ) ^ ((l : ℝ) - 2 + E) * (3 / 4 : ℝ) ^ idx := by
  have h2pos : 0 < (2 : ℝ) := by norm_num
  have hratio :
      (3 / 4 : ℝ) ^ idx =
        (3 : ℝ) ^ idx / (2 : ℝ) ^ (((2 * idx : ℕ) : ℕ) : ℝ) := by
    have hden :
        (4 : ℝ) ^ idx =
          (2 : ℝ) ^ (((2 * idx : ℕ) : ℕ) : ℝ) := by
      calc
        (4 : ℝ) ^ idx = ((2 : ℝ) ^ 2) ^ idx := by norm_num
        _ = (2 : ℝ) ^ (2 * idx) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (((2 * idx : ℕ) : ℕ) : ℝ) := by
          simpa using (Real.rpow_natCast (2 : ℝ) (2 * idx)).symm
    rw [div_pow]
    rw [hden]
  have hexp :
      (l : ℝ) - (2 * (((idx + 1 : ℕ) : ℕ) : ℝ) - E) =
        (l : ℝ) - 2 + E - (((2 * idx : ℕ) : ℕ) : ℝ) := by
    norm_num
    ring
  rw [hratio, hexp]
  rw [Real.rpow_sub h2pos]
  ring

/-- Pointwise cleared-summand envelope with the geometric factor exposed. -/
theorem taoCor63ClearedSummand_real_le_geometricEnvelope
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    {idx : ℕ} (hidx : idx < as.length) :
    (taoCor63ClearedSummand l idx as : ℝ) ≤
      (2 : ℝ) ^ ((l : ℝ) - 2 + taoCor63PrefixError CA n (idx + 1)) *
        (3 / 4 : ℝ) ^ idx := by
  have hprefix :=
    taoCor63ClearedSummand_real_le_prefixEnvelope
      (CA := CA) (n := n) (l := l) (as := as)
      hweight htyp hidx
  rw [taoCor63PrefixEnvelope_eq_geometric
    (l := l) (idx := idx) (E := taoCor63PrefixError CA n (idx + 1))] at hprefix
  exact hprefix

/--
The recursive list of cleared summands beginning at global index `idx` and
with already accumulated source prefix `pref`.
-/
def taoCor63ClearedSummandsFrom
    (l idx pref : ℕ) : List ℕ+ → List ℕ
  | [] => []
  | a :: as =>
      3 ^ idx * 2 ^ (l - (pref + (a : ℕ))) ::
        taoCor63ClearedSummandsFrom l (idx + 1) (pref + (a : ℕ)) as

/-- The recursive cleared offset sum is the sum of its cleared summands. -/
theorem taoCor63ClearedOffsetSumFrom_eq_summandsFrom_sum
    (l idx pref : ℕ) (as : List ℕ+) :
    taoCor63ClearedOffsetSumFrom l idx pref as =
      (taoCor63ClearedSummandsFrom l idx pref as).sum := by
  induction as generalizing idx pref with
  | nil =>
      simp [taoCor63ClearedOffsetSumFrom, taoCor63ClearedSummandsFrom]
  | cons a as ih =>
      simp [taoCor63ClearedOffsetSumFrom, taoCor63ClearedSummandsFrom, ih]

/-- The `loc`th summand of a recursive cleared offset sum state. -/
def taoCor63ClearedSummandFrom
    (l idx pref loc : ℕ) (as : List ℕ+) : ℕ :=
  3 ^ (idx + loc) *
    2 ^ (l - (pref + taoSection6IntervalWeight as 0 (loc + 1)))

/-- The first interval weight of a cons list is the head weight. -/
theorem taoSection6IntervalWeight_cons_zero_one
    (a : ℕ+) (as : List ℕ+) :
    taoSection6IntervalWeight (a :: as) 0 1 = (a : ℕ) := by
  simp [taoSection6IntervalWeight]

/-- Prefix interval weights of a cons list split into head plus tail prefix. -/
theorem taoSection6IntervalWeight_cons_zero_succ_succ
    (a : ℕ+) (as : List ℕ+) (loc : ℕ) :
    taoSection6IntervalWeight (a :: as) 0 (loc + 2) =
      (a : ℕ) + taoSection6IntervalWeight as 0 (loc + 1) := by
  simp [taoSection6IntervalWeight, Nat.add_comm]

/-- Zeroth named recursive summand for a cons list. -/
theorem taoCor63ClearedSummandFrom_cons_zero
    (l idx pref : ℕ) (a : ℕ+) (as : List ℕ+) :
    taoCor63ClearedSummandFrom l idx pref 0 (a :: as) =
      3 ^ idx * 2 ^ (l - (pref + (a : ℕ))) := by
  simp [taoCor63ClearedSummandFrom,
    taoSection6IntervalWeight_cons_zero_one]

/-- Successor named recursive summand for a cons list. -/
theorem taoCor63ClearedSummandFrom_cons_succ
    (l idx pref loc : ℕ) (a : ℕ+) (as : List ℕ+) :
    taoCor63ClearedSummandFrom l idx pref (loc + 1) (a :: as) =
      taoCor63ClearedSummandFrom l (idx + 1) (pref + (a : ℕ)) loc as := by
  simp [taoCor63ClearedSummandFrom,
    taoSection6IntervalWeight_cons_zero_succ_succ,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Recursive cleared offset sums as finite sums over local source positions. -/
theorem taoCor63ClearedOffsetSumFrom_eq_range_sumFrom
    (l idx pref : ℕ) (as : List ℕ+) :
    taoCor63ClearedOffsetSumFrom l idx pref as =
      ∑ loc ∈ Finset.range as.length,
        taoCor63ClearedSummandFrom l idx pref loc as := by
  induction as generalizing idx pref with
  | nil =>
      simp [taoCor63ClearedOffsetSumFrom]
  | cons a as ih =>
      rw [taoCor63ClearedOffsetSumFrom]
      rw [show (a :: as).length = 1 + as.length by
        simp [Nat.add_comm]]
      rw [Finset.sum_range_add]
      simp only [Finset.range_one, Finset.sum_singleton]
      rw [taoCor63ClearedSummandFrom_cons_zero]
      rw [ih (idx + 1) (pref + (a : ℕ))]
      congr 1
      apply Finset.sum_congr rfl
      intro loc hloc
      rw [show 1 + loc = loc + 1 by omega]
      rw [taoCor63ClearedSummandFrom_cons_succ]

/-- Top-level named recursive summands agree with the named cleared summand. -/
theorem taoCor63ClearedSummandFrom_zero_eq_summand
    (l idx : ℕ) (as : List ℕ+) :
    taoCor63ClearedSummandFrom l 0 0 idx as =
      taoCor63ClearedSummand l idx as := by
  simp [taoCor63ClearedSummandFrom, taoCor63ClearedSummand]

/-- Top-level cleared offset sum as a finite range sum of named summands. -/
theorem taoCor63ClearedOffsetSum_eq_range_sum
    (l : ℕ) (as : List ℕ+) :
    taoCor63ClearedOffsetSum l as =
      ∑ idx ∈ Finset.range as.length,
        taoCor63ClearedSummand l idx as := by
  rw [taoCor63ClearedOffsetSum,
    taoCor63ClearedOffsetSumFrom_eq_range_sumFrom]
  apply Finset.sum_congr rfl
  intro idx hidx
  rw [taoCor63ClearedSummandFrom_zero_eq_summand]

/-- Finite-sum envelope obtained by summing the pointwise geometric envelopes. -/
theorem taoCor63ClearedOffsetSum_real_le_geometricEnvelopeSum
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as) :
    (taoCor63ClearedOffsetSum l as : ℝ) ≤
      ∑ idx ∈ Finset.range as.length,
        (2 : ℝ) ^ ((l : ℝ) - 2 + taoCor63PrefixError CA n (idx + 1)) *
          (3 / 4 : ℝ) ^ idx := by
  rw [taoCor63ClearedOffsetSum_eq_range_sum]
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum fun idx hidx =>
    taoCor63ClearedSummand_real_le_geometricEnvelope
      (CA := CA) (n := n) (l := l) (as := as)
      hweight htyp (by simpa using hidx)

/-- The finite real envelope obtained after bounding each cleared summand. -/
noncomputable def taoCor63GeometricEnvelopeSum
    (CA : ℝ) (n l : ℕ) (as : List ℕ+) : ℝ :=
  ∑ idx ∈ Finset.range as.length,
    (2 : ℝ) ^ ((l : ℝ) - 2 + taoCor63PrefixError CA n (idx + 1)) *
      (3 / 4 : ℝ) ^ idx

/-- The cleared offset sum is bounded by the named finite real envelope. -/
theorem taoCor63ClearedOffsetSum_real_le_geometricEnvelopeSum_def
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as) :
    (taoCor63ClearedOffsetSum l as : ℝ) ≤
      taoCor63GeometricEnvelopeSum CA n l as := by
  simpa [taoCor63GeometricEnvelopeSum] using
    taoCor63ClearedOffsetSum_real_le_geometricEnvelopeSum
      (CA := CA) (n := n) (l := l) (as := as) hweight htyp

/-- Convert a strict real-envelope bound into the natural smallness conclusion. -/
theorem taoCor63ClearedOffsetSum_lt_of_geometricEnvelopeSum_lt
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (henv : taoCor63GeometricEnvelopeSum CA n l as < (3 ^ n : ℝ)) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  have hle :=
    taoCor63ClearedOffsetSum_real_le_geometricEnvelopeSum_def
      (CA := CA) (n := n) (l := l) (as := as) hweight htyp
  have hreal : (taoCor63ClearedOffsetSum l as : ℝ) < (3 ^ n : ℝ) :=
    lt_of_le_of_lt hle henv
  exact_mod_cast hreal

/--
Envelope version of the one-sided Corollary 6.3 smallness target.

This is the remaining analytic obligation after the checked summand estimates:
prove the named finite real envelope is `< 3^n`.
-/
noncomputable def TaoCor63StarEnvelopeSmallnessStatement : Prop :=
  ∀ CA : ℝ, 17 ≤ CA → ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    ∀ k l : ℕ, taoCor63StarLRange CA n l →
      ∀ as : List ℕ+,
        as.length = k + 1 →
        taoTupleWeight as = l →
        taoCor63StarInclusiveTypical CA n as →
        taoCor63GeometricEnvelopeSum CA n l as < (3 ^ n : ℝ)

/-- The prefix-error weighted geometric series left after factoring out `2^(l-2)`. -/
noncomputable def taoCor63PrefixErrorGeometricSum
    (CA : ℝ) (n : ℕ) (as : List ℕ+) : ℝ :=
  ∑ idx ∈ Finset.range as.length,
    (2 : ℝ) ^ (taoCor63PrefixError CA n (idx + 1)) *
      (3 / 4 : ℝ) ^ idx

/-- Factor the common `2^(l-2)` scale out of the finite envelope. -/
theorem taoCor63GeometricEnvelopeSum_eq_pow_mul_prefixErrorGeometricSum
    (CA : ℝ) (n l : ℕ) (as : List ℕ+) :
    taoCor63GeometricEnvelopeSum CA n l as =
      (2 : ℝ) ^ ((l : ℝ) - 2) *
        taoCor63PrefixErrorGeometricSum CA n as := by
  rw [taoCor63GeometricEnvelopeSum, taoCor63PrefixErrorGeometricSum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro idx hidx
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  ring

/-- The finite geometric sum with ratio `3 / 4` is bounded by `4`. -/
theorem taoCor63GeomRatioSum_le_four (m : ℕ) :
    (∑ idx ∈ Finset.range m, (3 / 4 : ℝ) ^ idx) ≤ 4 := by
  have hgeom :=
    geom_sum_mul_of_le_one (x := (3 / 4 : ℝ))
      (n := m) (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hgeom' :
      (∑ idx ∈ Finset.range m, (3 / 4 : ℝ) ^ idx) * (1 / 4 : ℝ) =
        1 - (3 / 4 : ℝ) ^ m := by
    norm_num at hgeom ⊢
    exact hgeom
  have hpow_nonneg : 0 ≤ (3 / 4 : ℝ) ^ m :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) m
  have hmul_le :
      (∑ idx ∈ Finset.range m, (3 / 4 : ℝ) ^ idx) * (1 / 4 : ℝ) ≤ 1 := by
    rw [hgeom']
    linarith
  have hmul_le' :=
    mul_le_mul_of_nonneg_right hmul_le (by norm_num : (0 : ℝ) ≤ 4)
  simpa [mul_assoc] using hmul_le'

/-- Bound the prefix-error weighted geometric sum from a uniform power bound. -/
theorem taoCor63PrefixErrorGeometricSum_le_mul_geom_of_pow_le
    {CA B : ℝ} {n : ℕ} {as : List ℕ+}
    (hB : ∀ idx : ℕ, idx < as.length →
      (2 : ℝ) ^ taoCor63PrefixError CA n (idx + 1) ≤ B) :
    taoCor63PrefixErrorGeometricSum CA n as ≤
      B * ∑ idx ∈ Finset.range as.length, (3 / 4 : ℝ) ^ idx := by
  calc
    taoCor63PrefixErrorGeometricSum CA n as
        ≤ ∑ idx ∈ Finset.range as.length,
            B * (3 / 4 : ℝ) ^ idx := by
          apply Finset.sum_le_sum
          intro idx hidx
          exact mul_le_mul_of_nonneg_right
            (hB idx (by simpa using hidx))
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) idx)
    _ = B * ∑ idx ∈ Finset.range as.length, (3 / 4 : ℝ) ^ idx := by
          rw [Finset.mul_sum]

/-- Coarse `4B` bound for the prefix-error weighted geometric sum. -/
theorem taoCor63PrefixErrorGeometricSum_le_four_mul_of_pow_le
    {CA B : ℝ} {n : ℕ} {as : List ℕ+}
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ idx : ℕ, idx < as.length →
      (2 : ℝ) ^ taoCor63PrefixError CA n (idx + 1) ≤ B) :
    taoCor63PrefixErrorGeometricSum CA n as ≤ B * 4 := by
  have hweighted :=
    taoCor63PrefixErrorGeometricSum_le_mul_geom_of_pow_le
      (CA := CA) (B := B) (n := n) (as := as) hB
  have hgeom := taoCor63GeomRatioSum_le_four as.length
  exact le_trans hweighted (mul_le_mul_of_nonneg_left hgeom hB_nonneg)

/-- Bound the named finite real envelope from a uniform prefix-error power bound. -/
theorem taoCor63GeometricEnvelopeSum_le_pow_mul_four_mul_of_pow_le
    {CA B : ℝ} {n l : ℕ} {as : List ℕ+}
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ idx : ℕ, idx < as.length →
      (2 : ℝ) ^ taoCor63PrefixError CA n (idx + 1) ≤ B) :
    taoCor63GeometricEnvelopeSum CA n l as ≤
      (2 : ℝ) ^ ((l : ℝ) - 2) * (B * 4) := by
  rw [taoCor63GeometricEnvelopeSum_eq_pow_mul_prefixErrorGeometricSum]
  exact mul_le_mul_of_nonneg_left
    (taoCor63PrefixErrorGeometricSum_le_four_mul_of_pow_le
      (CA := CA) (B := B) (n := n) (as := as) hB_nonneg hB)
    (by positivity)

/--
One-sided smallness consumer from a uniform prefix-error power bound and the
final scalar comparison.
-/
theorem taoCor63ClearedOffsetSum_lt_of_prefixErrorPow_bound
    {CA B : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ idx : ℕ, idx < as.length →
      (2 : ℝ) ^ taoCor63PrefixError CA n (idx + 1) ≤ B)
    (hfinal :
      (2 : ℝ) ^ ((l : ℝ) - 2) * (B * 4) < (3 ^ n : ℝ)) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  exact taoCor63ClearedOffsetSum_lt_of_geometricEnvelopeSum_lt
    (CA := CA) (n := n) (l := l) (as := as) hweight htyp
    (lt_of_le_of_lt
      (taoCor63GeometricEnvelopeSum_le_pow_mul_four_mul_of_pow_le
        (CA := CA) (B := B) (n := n) (l := l) (as := as) hB_nonneg hB)
      hfinal)

/-- A finite geometric sum with ratio in `[0,1)` is bounded by `1 / (1-r)`. -/
theorem finite_geom_sum_le_inv_one_sub
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (m : ℕ) :
    (∑ idx ∈ Finset.range m, r ^ idx) ≤ (1 - r)⁻¹ := by
  have hden_pos : 0 < 1 - r := by linarith
  have hgeom :=
    geom_sum_mul_of_le_one (x := r) (n := m) (le_of_lt hr_lt_one)
  have hpow_nonneg : 0 ≤ r ^ m := pow_nonneg hr_nonneg m
  rw [inv_eq_one_div]
  rw [le_div_iff₀ hden_pos]
  rw [hgeom]
  linarith

/-- Rewrite finite exponential decay at a natural index as a power. -/
theorem exp_neg_nat_mul_eq_pow (c : ℝ) (idx : ℕ) :
    Real.exp (-(c * (idx : ℝ))) = Real.exp (-c) ^ idx := by
  rw [show -(c * (idx : ℝ)) = (idx : ℝ) * (-c) by ring]
  rw [Real.exp_nat_mul]

/-- Finite exponential-decay sum bound. -/
theorem finite_exp_neg_mul_sum_le_inv_one_sub
    {c : ℝ} (hc_pos : 0 < c) (m : ℕ) :
    (∑ idx ∈ Finset.range m, Real.exp (-c * (idx : ℝ))) ≤
      (1 - Real.exp (-c))⁻¹ := by
  have hexp_nonneg : 0 ≤ Real.exp (-c) := le_of_lt (Real.exp_pos (-c))
  have hexp_lt_one : Real.exp (-c) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  simpa [exp_neg_nat_mul_eq_pow] using
    finite_geom_sum_le_inv_one_sub
      (r := Real.exp (-c)) hexp_nonneg hexp_lt_one m

/-- Log-linear decay implies pointwise exponential decay for the envelope terms. -/
theorem two_rpow_mul_three_four_pow_le_exp_of_log_le
    {E K c : ℝ} {idx : ℕ}
    (hlog :
      Real.log 2 * E + (idx : ℝ) * Real.log (3 / 4 : ℝ) ≤
        K - c * (idx : ℝ)) :
    (2 : ℝ) ^ E * (3 / 4 : ℝ) ^ idx ≤
      Real.exp K * Real.exp (-c * (idx : ℝ)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show (3 / 4 : ℝ) ^ idx = (3 / 4 : ℝ) ^ ((idx : ℝ)) by
    exact (Real.rpow_natCast (3 / 4 : ℝ) idx).symm]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  rw [← Real.exp_add]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Sum pointwise exponential decay over the prefix-error geometric series. -/
theorem taoCor63PrefixErrorGeometricSum_le_const_mul_exp_decay
    {CA C c : ℝ} {n : ℕ} {as : List ℕ+}
    (hC_nonneg : 0 ≤ C)
    (hc_pos : 0 < c)
    (hterm : ∀ idx : ℕ, idx < as.length →
      (2 : ℝ) ^ taoCor63PrefixError CA n (idx + 1) *
          (3 / 4 : ℝ) ^ idx ≤
        C * Real.exp (-c * (idx : ℝ))) :
    taoCor63PrefixErrorGeometricSum CA n as ≤
      C * (1 - Real.exp (-c))⁻¹ := by
  calc
    taoCor63PrefixErrorGeometricSum CA n as
        ≤ ∑ idx ∈ Finset.range as.length,
            C * Real.exp (-c * (idx : ℝ)) := by
          rw [taoCor63PrefixErrorGeometricSum]
          apply Finset.sum_le_sum
          intro idx hidx
          exact hterm idx (by simpa using hidx)
    _ = C * ∑ idx ∈ Finset.range as.length,
            Real.exp (-c * (idx : ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ C * (1 - Real.exp (-c))⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (finite_exp_neg_mul_sum_le_inv_one_sub
              (c := c) hc_pos as.length)
            hC_nonneg

/-- Exponential-decay bound from a logarithmic pointwise envelope. -/
theorem taoCor63PrefixErrorGeometricSum_le_exp_const_mul_exp_decay
    {CA K c : ℝ} {n : ℕ} {as : List ℕ+}
    (hc_pos : 0 < c)
    (hlog : ∀ idx : ℕ, idx < as.length →
      Real.log 2 * taoCor63PrefixError CA n (idx + 1) +
          (idx : ℝ) * Real.log (3 / 4 : ℝ) ≤
        K - c * (idx : ℝ)) :
    taoCor63PrefixErrorGeometricSum CA n as ≤
      Real.exp K * (1 - Real.exp (-c))⁻¹ := by
  exact taoCor63PrefixErrorGeometricSum_le_const_mul_exp_decay
    (CA := CA) (C := Real.exp K) (c := c) (n := n) (as := as)
    (le_of_lt (Real.exp_pos K)) hc_pos
    (fun idx hidx =>
      two_rpow_mul_three_four_pow_le_exp_of_log_le
        (E := taoCor63PrefixError CA n (idx + 1))
        (K := K) (c := c) (idx := idx) (hlog idx hidx))

/-- Bound the named envelope by the exponential-decay constant. -/
theorem taoCor63GeometricEnvelopeSum_le_pow_mul_exp_const_decay
    {CA K c : ℝ} {n l : ℕ} {as : List ℕ+}
    (hc_pos : 0 < c)
    (hlog : ∀ idx : ℕ, idx < as.length →
      Real.log 2 * taoCor63PrefixError CA n (idx + 1) +
          (idx : ℝ) * Real.log (3 / 4 : ℝ) ≤
        K - c * (idx : ℝ)) :
    taoCor63GeometricEnvelopeSum CA n l as ≤
      (2 : ℝ) ^ ((l : ℝ) - 2) *
        (Real.exp K * (1 - Real.exp (-c))⁻¹) := by
  rw [taoCor63GeometricEnvelopeSum_eq_pow_mul_prefixErrorGeometricSum]
  exact mul_le_mul_of_nonneg_left
    (taoCor63PrefixErrorGeometricSum_le_exp_const_mul_exp_decay
      (CA := CA) (K := K) (c := c) (n := n) (as := as)
      hc_pos hlog)
    (by positivity)

/-- Smallness consumer from a logarithmic exponential-decay bound. -/
theorem taoCor63ClearedOffsetSum_lt_of_exp_decay_log_bound
    {CA K c : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hc_pos : 0 < c)
    (hlog : ∀ idx : ℕ, idx < as.length →
      Real.log 2 * taoCor63PrefixError CA n (idx + 1) +
          (idx : ℝ) * Real.log (3 / 4 : ℝ) ≤
        K - c * (idx : ℝ))
    (hfinal :
      (2 : ℝ) ^ ((l : ℝ) - 2) *
          (Real.exp K * (1 - Real.exp (-c))⁻¹) <
        (3 ^ n : ℝ)) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  exact taoCor63ClearedOffsetSum_lt_of_geometricEnvelopeSum_lt
    (CA := CA) (n := n) (l := l) (as := as) hweight htyp
    (lt_of_le_of_lt
      (taoCor63GeometricEnvelopeSum_le_pow_mul_exp_const_decay
        (CA := CA) (K := K) (c := c) (n := n) (l := l) (as := as)
        hc_pos hlog)
      hfinal)

/-- Young inequality helper for a square-root term with linear penalty. -/
theorem young_sqrt_sub_mul_le_sq_div
    {A b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    A * Real.sqrt x - b * x ≤ A ^ 2 / (4 * b) := by
  have hb4 : 0 < 4 * b := by nlinarith
  rw [le_div_iff₀ hb4]
  have hsq : 0 ≤ (A - 2 * b * Real.sqrt x) ^ 2 := sq_nonneg _
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  ring_nf at hsq ⊢
  nlinarith

/-- Young inequality helper in epsilon form for a square-root term. -/
theorem young_sqrt_le_epsilon
    {A ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    A * Real.sqrt x ≤ (ε / 2) * x + A ^ 2 / (2 * ε) := by
  have h :=
    young_sqrt_sub_mul_le_sq_div
      (A := A) (b := ε / 2) (x := x) (by positivity) hx
  have hdiv : A ^ 2 / (4 * (ε / 2)) = A ^ 2 / (2 * ε) := by
    field_simp [hε.ne']
    ring
  linarith

/-- Positive decay rate `-log(3/4)`. -/
noncomputable def taoCor63DecayGamma : ℝ :=
  -Real.log (3 / 4 : ℝ)

/-- Standard Young constant for the Corollary 6.3 prefix-error bound. -/
noncomputable def taoCor63YoungK (CA : ℝ) (n : ℕ) : ℝ :=
  ((Real.log 2 * CA) ^ 2 * Real.log (n : ℝ)) /
      (2 * taoCor63DecayGamma) +
    (Real.log 2 * CA) * Real.log (n : ℝ) +
    taoCor63DecayGamma / 2

/-- Flexible Young constant with an explicit decay rate `c < gamma`. -/
noncomputable def taoCor63YoungFlexibleK (CA : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  ((Real.log 2 * CA) ^ 2 * Real.log (n : ℝ)) /
      (4 * (taoCor63DecayGamma - c)) +
    (Real.log 2 * CA) * Real.log (n : ℝ) +
    (taoCor63DecayGamma - c)

/-- Quarter-decay specialization of the flexible Young constant. -/
noncomputable def taoCor63YoungQuarterK (CA : ℝ) (n : ℕ) : ℝ :=
  taoCor63YoungFlexibleK CA n (taoCor63DecayGamma / 4)

theorem taoCor63DecayGamma_pos : 0 < taoCor63DecayGamma := by
  have hlogneg : Real.log (3 / 4 : ℝ) < 0 :=
    (Real.log_neg_iff (by norm_num : (0 : ℝ) < 3 / 4)).mpr
      (by norm_num : (3 / 4 : ℝ) < 1)
  simpa [taoCor63DecayGamma] using neg_pos.mpr hlogneg

/-- Generic logarithmic Young bound with decay `gamma / 2`. -/
theorem taoCor63Young_generic_log_bound
    {A L gamma : ℝ} {idx : ℕ}
    (hL : 0 < L) (hgamma : 0 < gamma) :
    A * Real.sqrt (((idx + 1 : ℕ) : ℝ) * L) + A * L -
        gamma * (idx : ℝ) ≤
      A ^ 2 * L / (2 * gamma) + A * L + gamma / 2 -
        (gamma / 2) * (idx : ℝ) := by
  have hx : 0 ≤ (((idx + 1 : ℕ) : ℝ) * L) := by positivity
  have hy :=
    young_sqrt_le_epsilon
      (A := A) (ε := gamma / L)
      (x := (((idx + 1 : ℕ) : ℝ) * L))
      (by positivity) hx
  have hmain :
      A * Real.sqrt (((idx + 1 : ℕ) : ℝ) * L) ≤
        gamma / 2 * ((idx + 1 : ℕ) : ℝ) +
          A ^ 2 * L / (2 * gamma) := by
    calc
      A * Real.sqrt (((idx + 1 : ℕ) : ℝ) * L)
          ≤ (gamma / L / 2) * (((idx + 1 : ℕ) : ℝ) * L) +
              A ^ 2 / (2 * (gamma / L)) := hy
      _ = gamma / 2 * ((idx + 1 : ℕ) : ℝ) +
            A ^ 2 * L / (2 * gamma) := by
          field_simp [hL.ne', hgamma.ne']
  have hidx : (((idx + 1 : ℕ) : ℝ)) = (idx : ℝ) + 1 := by
    norm_num
  nlinarith

/-- Generic logarithmic Young bound with flexible decay `c < gamma`. -/
theorem taoCor63Young_generic_flexible_log_bound
    {A L gamma c : ℝ} {idx : ℕ}
    (hL : 0 < L) (hcgamma : c < gamma) :
    A * Real.sqrt (((idx + 1 : ℕ) : ℝ) * L) + A * L -
        gamma * (idx : ℝ) ≤
      A ^ 2 * L / (4 * (gamma - c)) + A * L + (gamma - c) -
        c * (idx : ℝ) := by
  have hbeta : 0 < gamma - c := by linarith
  have hx : 0 ≤ (((idx + 1 : ℕ) : ℝ) * L) := by positivity
  have hy :=
    young_sqrt_sub_mul_le_sq_div
      (A := A) (b := (gamma - c) / L)
      (x := (((idx + 1 : ℕ) : ℝ) * L))
      (by positivity) hx
  have hmain :
      A * Real.sqrt (((idx + 1 : ℕ) : ℝ) * L) -
          (gamma - c) * ((idx + 1 : ℕ) : ℝ) ≤
        A ^ 2 * L / (4 * (gamma - c)) := by
    calc
      A * Real.sqrt (((idx + 1 : ℕ) : ℝ) * L) -
          (gamma - c) * ((idx + 1 : ℕ) : ℝ)
          = A * Real.sqrt (((idx + 1 : ℕ) : ℝ) * L) -
              ((gamma - c) / L) *
                (((idx + 1 : ℕ) : ℝ) * L) := by
              field_simp [hL.ne']
      _ ≤ A ^ 2 / (4 * ((gamma - c) / L)) := hy
      _ = A ^ 2 * L / (4 * (gamma - c)) := by
              field_simp [hL.ne', hbeta.ne']
  have hidx : (((idx + 1 : ℕ) : ℝ)) = (idx : ℝ) + 1 := by
    norm_num
  nlinarith

/-- Pointwise log-bound for prefix errors using the standard Young constant. -/
theorem taoCor63PrefixError_log_bound_young
    {CA : ℝ} {n idx : ℕ}
    (hlogn : 0 < Real.log (n : ℝ)) :
    Real.log 2 * taoCor63PrefixError CA n (idx + 1) +
        (idx : ℝ) * Real.log (3 / 4 : ℝ) ≤
      taoCor63YoungK CA n -
        (taoCor63DecayGamma / 2) * (idx : ℝ) := by
  have hgeneric :=
    taoCor63Young_generic_log_bound
      (A := Real.log 2 * CA)
      (L := Real.log (n : ℝ))
      (gamma := taoCor63DecayGamma)
      (idx := idx) hlogn taoCor63DecayGamma_pos
  have hlog34 : Real.log (3 / 4 : ℝ) = -taoCor63DecayGamma := by
    simp [taoCor63DecayGamma]
  simpa [taoCor63PrefixError, taoCor63YoungK, hlog34, mul_add,
    mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using hgeneric

theorem taoCor63PrefixErrorGeometricSum_le_young_decay
    {CA : ℝ} {n : ℕ} {as : List ℕ+}
    (hlogn : 0 < Real.log (n : ℝ)) :
    taoCor63PrefixErrorGeometricSum CA n as ≤
      Real.exp (taoCor63YoungK CA n) *
        (1 - Real.exp (-(taoCor63DecayGamma / 2)))⁻¹ := by
  exact taoCor63PrefixErrorGeometricSum_le_exp_const_mul_exp_decay
    (CA := CA) (K := taoCor63YoungK CA n)
    (c := taoCor63DecayGamma / 2) (n := n) (as := as)
    (half_pos taoCor63DecayGamma_pos)
    (fun idx hidx =>
      taoCor63PrefixError_log_bound_young
        (CA := CA) (n := n) (idx := idx) hlogn)

theorem taoCor63ClearedOffsetSum_lt_of_young_decay_final
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlogn : 0 < Real.log (n : ℝ))
    (hfinal :
      (2 : ℝ) ^ ((l : ℝ) - 2) *
          (Real.exp (taoCor63YoungK CA n) *
            (1 - Real.exp (-(taoCor63DecayGamma / 2)))⁻¹) <
        (3 ^ n : ℝ)) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  exact taoCor63ClearedOffsetSum_lt_of_exp_decay_log_bound
    (CA := CA) (K := taoCor63YoungK CA n)
    (c := taoCor63DecayGamma / 2) (n := n) (l := l) (as := as)
    hweight htyp (half_pos taoCor63DecayGamma_pos)
    (fun idx hidx =>
      taoCor63PrefixError_log_bound_young
        (CA := CA) (n := n) (idx := idx) hlogn)
    hfinal

/-- Pointwise log-bound for prefix errors using a flexible decay rate. -/
theorem taoCor63PrefixError_log_bound_young_flexible
    {CA c : ℝ} {n idx : ℕ}
    (hlogn : 0 < Real.log (n : ℝ))
    (hc_lt : c < taoCor63DecayGamma) :
    Real.log 2 * taoCor63PrefixError CA n (idx + 1) +
        (idx : ℝ) * Real.log (3 / 4 : ℝ) ≤
      taoCor63YoungFlexibleK CA n c - c * (idx : ℝ) := by
  have hgeneric :=
    taoCor63Young_generic_flexible_log_bound
      (A := Real.log 2 * CA)
      (L := Real.log (n : ℝ))
      (gamma := taoCor63DecayGamma)
      (c := c)
      (idx := idx) hlogn hc_lt
  have hlog34 : Real.log (3 / 4 : ℝ) = -taoCor63DecayGamma := by
    simp [taoCor63DecayGamma]
  simpa [taoCor63PrefixError, taoCor63YoungFlexibleK, hlog34, mul_add,
    mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using hgeneric

theorem taoCor63PrefixErrorGeometricSum_le_young_flexible_decay
    {CA c : ℝ} {n : ℕ} {as : List ℕ+}
    (hlogn : 0 < Real.log (n : ℝ))
    (hc_pos : 0 < c)
    (hc_lt : c < taoCor63DecayGamma) :
    taoCor63PrefixErrorGeometricSum CA n as ≤
      Real.exp (taoCor63YoungFlexibleK CA n c) *
        (1 - Real.exp (-c))⁻¹ := by
  exact taoCor63PrefixErrorGeometricSum_le_exp_const_mul_exp_decay
    (CA := CA) (K := taoCor63YoungFlexibleK CA n c)
    (c := c) (n := n) (as := as)
    hc_pos
    (fun idx hidx =>
      taoCor63PrefixError_log_bound_young_flexible
        (CA := CA) (c := c) (n := n) (idx := idx) hlogn hc_lt)

theorem taoCor63ClearedOffsetSum_lt_of_young_flexible_decay_final
    {CA c : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlogn : 0 < Real.log (n : ℝ))
    (hc_pos : 0 < c)
    (hc_lt : c < taoCor63DecayGamma)
    (hfinal :
      (2 : ℝ) ^ ((l : ℝ) - 2) *
          (Real.exp (taoCor63YoungFlexibleK CA n c) *
            (1 - Real.exp (-c))⁻¹) <
        (3 ^ n : ℝ)) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  exact taoCor63ClearedOffsetSum_lt_of_exp_decay_log_bound
    (CA := CA) (K := taoCor63YoungFlexibleK CA n c)
    (c := c) (n := n) (l := l) (as := as)
    hweight htyp hc_pos
    (fun idx hidx =>
      taoCor63PrefixError_log_bound_young_flexible
        (CA := CA) (c := c) (n := n) (idx := idx) hlogn hc_lt)
    hfinal

theorem taoCor63DecayGamma_quarter_pos :
    0 < taoCor63DecayGamma / 4 := by
  nlinarith [taoCor63DecayGamma_pos]

theorem taoCor63DecayGamma_quarter_lt :
    taoCor63DecayGamma / 4 < taoCor63DecayGamma := by
  nlinarith [taoCor63DecayGamma_pos]

theorem taoCor63PrefixErrorGeometricSum_le_young_quarter_decay
    {CA : ℝ} {n : ℕ} {as : List ℕ+}
    (hlogn : 0 < Real.log (n : ℝ)) :
    taoCor63PrefixErrorGeometricSum CA n as ≤
      Real.exp (taoCor63YoungQuarterK CA n) *
        (1 - Real.exp (-(taoCor63DecayGamma / 4)))⁻¹ := by
  simpa [taoCor63YoungQuarterK] using
    taoCor63PrefixErrorGeometricSum_le_young_flexible_decay
      (CA := CA) (c := taoCor63DecayGamma / 4) (n := n) (as := as)
      hlogn taoCor63DecayGamma_quarter_pos taoCor63DecayGamma_quarter_lt

theorem taoCor63_log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num : (1 : ℝ) < 2)

theorem taoCor63_three_pow_eq_exp_log (n : ℕ) :
    (3 ^ n : ℝ) = Real.exp ((n : ℝ) * Real.log 3) := by
  calc
    (3 ^ n : ℝ) = (3 : ℝ) ^ ((n : ℝ)) := by
      exact (Real.rpow_natCast (3 : ℝ) n).symm
    _ = Real.exp (Real.log 3 * (n : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ = Real.exp ((n : ℝ) * Real.log 3) := by
      ring_nf

theorem taoCor63_lrange_log_two_mul_sub_two_le
    {CA : ℝ} {n l : ℕ}
    (hrange : taoCor63StarLRange CA n l) :
    Real.log 2 * ((l : ℝ) - 2) ≤
      (n : ℝ) * Real.log 3 -
        CA ^ 2 * Real.log (n : ℝ) * Real.log 2 +
        2 * CA * Real.log (n : ℝ) * Real.log 2 -
        2 * Real.log 2 := by
  have hle := hrange.2
  have hmul :
      (l : ℝ) * Real.log 2 ≤
        (taoCor63StarQ CA n + 2 * CA * Real.log (n : ℝ)) *
          Real.log 2 :=
    mul_le_mul_of_nonneg_right hle (le_of_lt taoCor63_log_two_pos)
  have hrewrite :
      (taoCor63StarQ CA n + 2 * CA * Real.log (n : ℝ)) *
          Real.log 2 =
        (n : ℝ) * Real.log 3 -
          CA ^ 2 * Real.log (n : ℝ) * Real.log 2 +
          2 * CA * Real.log (n : ℝ) * Real.log 2 := by
    rw [taoCor63StarQ]
    field_simp [ne_of_gt taoCor63_log_two_pos]
  have hmul' :
      (l : ℝ) * Real.log 2 ≤
        (n : ℝ) * Real.log 3 -
          CA ^ 2 * Real.log (n : ℝ) * Real.log 2 +
          2 * CA * Real.log (n : ℝ) * Real.log 2 := by
    simpa [hrewrite] using hmul
  nlinarith

theorem taoCor63_final_product_lt_of_exponent_lt
    {K D c : ℝ} {n l : ℕ}
    (hconst : (1 - Real.exp (-c))⁻¹ ≤ Real.exp D)
    (hexp :
      Real.log 2 * ((l : ℝ) - 2) + K + D <
        (n : ℝ) * Real.log 3) :
    (2 : ℝ) ^ ((l : ℝ) - 2) *
        (Real.exp K * (1 - Real.exp (-c))⁻¹) <
      (3 ^ n : ℝ) := by
  have hpow :
      (2 : ℝ) ^ ((l : ℝ) - 2) =
        Real.exp (Real.log 2 * ((l : ℝ) - 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hinner :
      Real.exp K * (1 - Real.exp (-c))⁻¹ ≤
        Real.exp K * Real.exp D :=
    mul_le_mul_of_nonneg_left hconst (le_of_lt (Real.exp_pos K))
  have hprod :
      (2 : ℝ) ^ ((l : ℝ) - 2) *
          (Real.exp K * (1 - Real.exp (-c))⁻¹) ≤
        Real.exp (Real.log 2 * ((l : ℝ) - 2) + K + D) := by
    calc
      (2 : ℝ) ^ ((l : ℝ) - 2) *
          (Real.exp K * (1 - Real.exp (-c))⁻¹)
          = Real.exp (Real.log 2 * ((l : ℝ) - 2)) *
              (Real.exp K * (1 - Real.exp (-c))⁻¹) := by
            rw [hpow]
      _ ≤ Real.exp (Real.log 2 * ((l : ℝ) - 2)) *
            (Real.exp K * Real.exp D) := by
            exact mul_le_mul_of_nonneg_left hinner
              (le_of_lt (Real.exp_pos _))
      _ = Real.exp (Real.log 2 * ((l : ℝ) - 2) + K + D) := by
            rw [← Real.exp_add, ← Real.exp_add]
            ring_nf
  have htarget :
      Real.exp (Real.log 2 * ((l : ℝ) - 2) + K + D) <
        (3 ^ n : ℝ) := by
    rw [taoCor63_three_pow_eq_exp_log n]
    exact Real.exp_lt_exp.mpr hexp
  exact lt_of_le_of_lt hprod htarget

theorem taoCor63_final_product_lt_of_lrange_margin
    {CA K D c : ℝ} {n l : ℕ}
    (hrange : taoCor63StarLRange CA n l)
    (hconst : (1 - Real.exp (-c))⁻¹ ≤ Real.exp D)
    (hmargin :
      -CA ^ 2 * Real.log (n : ℝ) * Real.log 2 +
          2 * CA * Real.log (n : ℝ) * Real.log 2 -
          2 * Real.log 2 + K + D < 0) :
    (2 : ℝ) ^ ((l : ℝ) - 2) *
        (Real.exp K * (1 - Real.exp (-c))⁻¹) <
      (3 ^ n : ℝ) := by
  have hl :=
    taoCor63_lrange_log_two_mul_sub_two_le
      (CA := CA) (n := n) (l := l) hrange
  have hexp :
      Real.log 2 * ((l : ℝ) - 2) + K + D <
        (n : ℝ) * Real.log 3 := by
    nlinarith
  exact taoCor63_final_product_lt_of_exponent_lt
    (K := K) (D := D) (c := c) (n := n) (l := l) hconst hexp

theorem taoCor63ClearedOffsetSum_lt_of_young_flexible_lrange_margin
    {CA c D : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlogn : 0 < Real.log (n : ℝ))
    (hc_pos : 0 < c)
    (hc_lt : c < taoCor63DecayGamma)
    (hrange : taoCor63StarLRange CA n l)
    (hconst : (1 - Real.exp (-c))⁻¹ ≤ Real.exp D)
    (hmargin :
      -CA ^ 2 * Real.log (n : ℝ) * Real.log 2 +
          2 * CA * Real.log (n : ℝ) * Real.log 2 -
          2 * Real.log 2 +
          taoCor63YoungFlexibleK CA n c + D < 0) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  exact taoCor63ClearedOffsetSum_lt_of_young_flexible_decay_final
    (CA := CA) (c := c) (n := n) (l := l) (as := as)
    hweight htyp hlogn hc_pos hc_lt
    (taoCor63_final_product_lt_of_lrange_margin
      (CA := CA) (K := taoCor63YoungFlexibleK CA n c) (D := D)
      (c := c) (n := n) (l := l) hrange hconst hmargin)

noncomputable def taoCor63YoungQuarterCoeff (CA : ℝ) : ℝ :=
  CA ^ 2 *
      (-Real.log 2 + (Real.log 2) ^ 2 / (3 * taoCor63DecayGamma)) +
    3 * Real.log 2 * CA

noncomputable def taoCor63YoungQuarterConst (D : ℝ) : ℝ :=
  -2 * Real.log 2 + (3 / 4) * taoCor63DecayGamma + D

theorem taoCor63_young_quarter_margin_eq
    (CA D : ℝ) (n : ℕ) :
    -CA ^ 2 * Real.log (n : ℝ) * Real.log 2 +
        2 * CA * Real.log (n : ℝ) * Real.log 2 -
        2 * Real.log 2 +
        taoCor63YoungFlexibleK CA n (taoCor63DecayGamma / 4) + D =
      Real.log (n : ℝ) * taoCor63YoungQuarterCoeff CA +
        taoCor63YoungQuarterConst D := by
  have hgamma : taoCor63DecayGamma ≠ 0 :=
    ne_of_gt taoCor63DecayGamma_pos
  unfold taoCor63YoungFlexibleK taoCor63YoungQuarterCoeff
    taoCor63YoungQuarterConst
  field_simp [hgamma]
  ring

theorem taoCor63_young_quarter_margin_lt_of_coeff_neg
    {CA D : ℝ} {n : ℕ}
    (hcoeff : taoCor63YoungQuarterCoeff CA < 0)
    (hlog :
      Real.log (n : ℝ) >
        taoCor63YoungQuarterConst D / (-taoCor63YoungQuarterCoeff CA)) :
    -CA ^ 2 * Real.log (n : ℝ) * Real.log 2 +
        2 * CA * Real.log (n : ℝ) * Real.log 2 -
        2 * Real.log 2 +
        taoCor63YoungFlexibleK CA n (taoCor63DecayGamma / 4) + D < 0 := by
  have hden_pos : 0 < -taoCor63YoungQuarterCoeff CA := by
    linarith
  have hmul :
      taoCor63YoungQuarterConst D <
        Real.log (n : ℝ) * (-taoCor63YoungQuarterCoeff CA) := by
    have hmul' :=
      (div_lt_iff₀ hden_pos).mp hlog
    nlinarith
  rw [taoCor63_young_quarter_margin_eq]
  nlinarith

theorem taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_log_bound
    {CA D : ℝ} {n l : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlogn : 0 < Real.log (n : ℝ))
    (hrange : taoCor63StarLRange CA n l)
    (hconst :
      (1 - Real.exp (-(taoCor63DecayGamma / 4)))⁻¹ ≤ Real.exp D)
    (hcoeff : taoCor63YoungQuarterCoeff CA < 0)
    (hlog :
      Real.log (n : ℝ) >
        taoCor63YoungQuarterConst D / (-taoCor63YoungQuarterCoeff CA)) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  exact
    taoCor63ClearedOffsetSum_lt_of_young_flexible_lrange_margin
      (CA := CA) (c := taoCor63DecayGamma / 4) (D := D)
      (n := n) (l := l) (as := as)
      hweight htyp hlogn taoCor63DecayGamma_quarter_pos
      taoCor63DecayGamma_quarter_lt hrange hconst
      (taoCor63_young_quarter_margin_lt_of_coeff_neg
        (CA := CA) (D := D) (n := n) hcoeff hlog)

theorem taoCor63DecayGamma_eq_log_four_thirds :
    taoCor63DecayGamma = Real.log (4 / 3 : ℝ) := by
  have hpos : (0 : ℝ) < 3 / 4 := by norm_num
  have hinv :
      Real.log ((3 / 4 : ℝ)⁻¹) = -Real.log (3 / 4 : ℝ) := by
    rw [Real.log_inv]
  have hval : ((3 / 4 : ℝ)⁻¹) = 4 / 3 := by norm_num
  rw [taoCor63DecayGamma, ← hinv, hval]

theorem taoCor63DecayGamma_gt_two_sevenths :
    (2 / 7 : ℝ) < taoCor63DecayGamma := by
  rw [taoCor63DecayGamma_eq_log_four_thirds]
  have h :=
    Real.lt_log_one_add_of_pos (show (0 : ℝ) < 1 / 3 by norm_num)
  norm_num at h
  simpa [show (1 + 1 / 3 : ℝ) = 4 / 3 by norm_num] using h

theorem taoCor63_log_two_gt_693_div_1000 :
    (693 / 1000 : ℝ) < Real.log 2 := by
  exact (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans
    Real.log_two_gt_d9

theorem taoCor63_log_two_lt_347_div_500 :
    Real.log 2 < (347 / 500 : ℝ) := by
  exact Real.log_two_lt_d9.trans
    (by norm_num : (0.6931471808 : ℝ) < 347 / 500)

theorem taoCor63_young_quarter_quadratic_coeff_lt :
    -Real.log 2 + (Real.log 2) ^ 2 / (3 * taoCor63DecayGamma) <
      -(196637 / 1500000 : ℝ) := by
  have hlog2_pos : 0 < Real.log 2 := taoCor63_log_two_pos
  have hlog2_lt : Real.log 2 < (347 / 500 : ℝ) :=
    taoCor63_log_two_lt_347_div_500
  have hlog2_gt : (693 / 1000 : ℝ) < Real.log 2 :=
    taoCor63_log_two_gt_693_div_1000
  have hgamma_gt : (2 / 7 : ℝ) < taoCor63DecayGamma :=
    taoCor63DecayGamma_gt_two_sevenths
  have hden_pos : 0 < 3 * taoCor63DecayGamma := by
    nlinarith
  have hsq :
      (Real.log 2) ^ 2 < (347 / 500 : ℝ) ^ 2 := by
    nlinarith
  have hdiv :
      (Real.log 2) ^ 2 / (3 * taoCor63DecayGamma) <
        (842863 / 1500000 : ℝ) := by
    rw [div_lt_iff₀ hden_pos]
    have hden_lower : (6 / 7 : ℝ) < 3 * taoCor63DecayGamma := by
      nlinarith
    have hscale_pos : (0 : ℝ) < 842863 / 1500000 := by norm_num
    have hscale :
        (347 / 500 : ℝ) ^ 2 =
          (842863 / 1500000 : ℝ) * (6 / 7) := by
      norm_num
    nlinarith
  nlinarith

theorem taoCor63YoungQuarterCoeff_neg_of_ge_seventeen
    {CA : ℝ} (hCA : 17 ≤ CA) :
    taoCor63YoungQuarterCoeff CA < 0 := by
  have hCA_pos : 0 < CA := by
    nlinarith
  have hCA_sq_pos : 0 < CA ^ 2 := by
    nlinarith
  have hq :
      -Real.log 2 + (Real.log 2) ^ 2 / (3 * taoCor63DecayGamma) <
        -(196637 / 1500000 : ℝ) :=
    taoCor63_young_quarter_quadratic_coeff_lt
  have hqmul :
      CA ^ 2 *
          (-Real.log 2 + (Real.log 2) ^ 2 /
            (3 * taoCor63DecayGamma)) <
        CA ^ 2 * (-(196637 / 1500000 : ℝ)) :=
    mul_lt_mul_of_pos_left hq hCA_sq_pos
  have hlog2mul :
      3 * Real.log 2 * CA <
        3 * (347 / 500 : ℝ) * CA := by
    have hleft :
        (3 * CA) * Real.log 2 <
          (3 * CA) * (347 / 500 : ℝ) :=
      mul_lt_mul_of_pos_left taoCor63_log_two_lt_347_div_500
        (by nlinarith)
    nlinarith
  have hsum :
      CA ^ 2 *
          (-Real.log 2 + (Real.log 2) ^ 2 /
            (3 * taoCor63DecayGamma)) +
        3 * Real.log 2 * CA <
      CA ^ 2 * (-(196637 / 1500000 : ℝ)) +
        3 * (347 / 500 : ℝ) * CA :=
    add_lt_add hqmul hlog2mul
  have hquad : 17 * CA ≤ CA ^ 2 := by
    nlinarith
  have hrhs_neg :
      CA ^ 2 * (-(196637 / 1500000 : ℝ)) +
        3 * (347 / 500 : ℝ) * CA < 0 := by
    nlinarith
  unfold taoCor63YoungQuarterCoeff
  nlinarith

theorem taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_log_bound_CA17
    {CA D : ℝ} {n l : ℕ} {as : List ℕ+}
    (hCA : 17 ≤ CA)
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlogn : 0 < Real.log (n : ℝ))
    (hrange : taoCor63StarLRange CA n l)
    (hconst :
      (1 - Real.exp (-(taoCor63DecayGamma / 4)))⁻¹ ≤ Real.exp D)
    (hlog :
      Real.log (n : ℝ) >
        taoCor63YoungQuarterConst D / (-taoCor63YoungQuarterCoeff CA)) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  exact
    taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_log_bound
      (CA := CA) (D := D) (n := n) (l := l) (as := as)
      hweight htyp hlogn hrange hconst
      (taoCor63YoungQuarterCoeff_neg_of_ge_seventeen hCA)
      hlog

theorem taoCor63_exp_neg_one_fourteenth_le_fifteen_sixteen :
    Real.exp (-(1 / 14 : ℝ)) ≤ (15 / 16 : ℝ) := by
  have hlog :
      Real.log (16 / 15 : ℝ) ≤ (1 / 14 : ℝ) := by
    have h :=
      Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 16 / 15 by norm_num)
    nlinarith
  have hexp :
      (16 / 15 : ℝ) ≤ Real.exp (1 / 14 : ℝ) :=
    (Real.log_le_iff_le_exp
      (show (0 : ℝ) < 16 / 15 by norm_num)).mp hlog
  have hinv :
      (Real.exp (1 / 14 : ℝ))⁻¹ ≤ ((16 / 15 : ℝ))⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) (show (0 : ℝ) < 16 / 15 by norm_num)).mpr
      hexp
  simpa [Real.exp_neg] using hinv

theorem taoCor63_exp_neg_quarter_gamma_lt_fifteen_sixteen :
    Real.exp (-(taoCor63DecayGamma / 4)) < (15 / 16 : ℝ) := by
  have hgamma :
      (2 / 7 : ℝ) < taoCor63DecayGamma :=
    taoCor63DecayGamma_gt_two_sevenths
  have hexp :
      Real.exp (-(taoCor63DecayGamma / 4)) <
        Real.exp (-(1 / 14 : ℝ)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  exact lt_of_lt_of_le hexp
    taoCor63_exp_neg_one_fourteenth_le_fifteen_sixteen

theorem taoCor63_quarter_geometric_prefactor_le_sixteen :
    (1 - Real.exp (-(taoCor63DecayGamma / 4)))⁻¹ ≤ (16 : ℝ) := by
  have hexp :
      Real.exp (-(taoCor63DecayGamma / 4)) < (15 / 16 : ℝ) :=
    taoCor63_exp_neg_quarter_gamma_lt_fifteen_sixteen
  have hbase_pos :
      0 < 1 - Real.exp (-(taoCor63DecayGamma / 4)) := by
    nlinarith
  rw [inv_le_comm₀ hbase_pos (by norm_num : (0 : ℝ) < 16)]
  nlinarith

theorem taoCor63_sixteen_le_exp_sixteen :
    (16 : ℝ) ≤ Real.exp 16 := by
  have h15 : (16 : ℝ) ≤ Real.exp 15 := by
    have hadd := Real.add_one_le_exp (15 : ℝ)
    norm_num at hadd
    exact hadd
  exact h15.trans (Real.exp_le_exp.mpr (by norm_num : (15 : ℝ) ≤ 16))

theorem taoCor63_quarter_geometric_prefactor_le_exp_sixteen :
    (1 - Real.exp (-(taoCor63DecayGamma / 4)))⁻¹ ≤ Real.exp 16 :=
  taoCor63_quarter_geometric_prefactor_le_sixteen.trans
    taoCor63_sixteen_le_exp_sixteen

theorem taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_log_bound_CA17_D16
    {CA : ℝ} {n l : ℕ} {as : List ℕ+}
    (hCA : 17 ≤ CA)
    (hweight : taoTupleWeight as = l)
    (htyp : taoCor63StarInclusiveTypical CA n as)
    (hlogn : 0 < Real.log (n : ℝ))
    (hrange : taoCor63StarLRange CA n l)
    (hlog :
      Real.log (n : ℝ) >
        taoCor63YoungQuarterConst 16 / (-taoCor63YoungQuarterCoeff CA)) :
    taoCor63ClearedOffsetSum l as < 3 ^ n := by
  exact
    taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_log_bound_CA17
      (CA := CA) (D := 16) (n := n) (l := l) (as := as)
      hCA hweight htyp hlogn hrange
      taoCor63_quarter_geometric_prefactor_le_exp_sixteen
      hlog

theorem taoCor63_exists_nat_log_gt (A : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A < Real.log (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp A)
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hexp : Real.exp A < (n : ℝ) :=
    lt_of_lt_of_le hN hNn
  have hn_pos : 0 < (n : ℝ) :=
    lt_trans (Real.exp_pos A) hexp
  exact (Real.lt_log_iff_exp_lt hn_pos).mpr hexp

theorem taoCor63_exists_nat_log_pos_and_gt (A : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < Real.log (n : ℝ) ∧ A < Real.log (n : ℝ) := by
  obtain ⟨Npos, hNpos⟩ := taoCor63_exists_nat_log_gt 0
  obtain ⟨NA, hNA⟩ := taoCor63_exists_nat_log_gt A
  refine ⟨max Npos NA, ?_⟩
  intro n hn
  have hpos_le : Npos ≤ n := le_trans (le_max_left _ _) hn
  have hA_le : NA ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨hNpos n hpos_le, hNA n hA_le⟩

theorem taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_eventually_CA17_D16
    {CA : ℝ} (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ l : ℕ, ∀ as : List ℕ+,
        taoTupleWeight as = l →
        taoCor63StarInclusiveTypical CA n as →
        taoCor63StarLRange CA n l →
        taoCor63ClearedOffsetSum l as < 3 ^ n := by
  obtain ⟨N0, hN0⟩ :=
    taoCor63_exists_nat_log_pos_and_gt
      (taoCor63YoungQuarterConst 16 /
        (-taoCor63YoungQuarterCoeff CA))
  refine ⟨N0, ?_⟩
  intro n hn l as hweight htyp hrange
  have hlogs := hN0 n hn
  exact
    taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_log_bound_CA17_D16
      (CA := CA) (n := n) (l := l) (as := as)
      hCA hweight htyp hlogs.1 hrange hlogs.2

theorem taoCor63ClearedOffsetSumFrom_eq_pow_mul_offset_reverse
    (l idx pref : ℕ) :
    ∀ as : List ℕ+, pref + taoTupleWeight as ≤ l →
      (taoCor63ClearedOffsetSumFrom l idx pref as : ℚ) =
        (3 : ℚ) ^ idx * (2 : ℚ) ^ (l - pref) * taoOffsetList as.reverse
  | [], _hbound => by
      simp [taoCor63ClearedOffsetSumFrom]
  | a :: as, hbound => by
      have htail : pref + (a : ℕ) + taoTupleWeight as ≤ l := by
        simpa [taoTupleWeight, Nat.add_assoc] using hbound
      have hprefa : pref + (a : ℕ) ≤ l := by
        omega
      have hsub : l - pref = l - (pref + (a : ℕ)) + (a : ℕ) := by
        omega
      rw [taoCor63ClearedOffsetSumFrom]
      rw [Nat.cast_add]
      push_cast
      rw [taoCor63ClearedOffsetSumFrom_eq_pow_mul_offset_reverse l (idx + 1)
        (pref + (a : ℕ)) as htail]
      rw [taoOffsetList_reverse_cons]
      rw [hsub, pow_add]
      field_simp [pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)]
      ring_nf

theorem taoCor63ClearedOffsetSum_eq_pow_mul_offset_reverse
    {l : ℕ} {as : List ℕ+} (hweight : taoTupleWeight as = l) :
    (taoCor63ClearedOffsetSum l as : ℚ) =
      (2 : ℚ) ^ l * taoOffsetList as.reverse := by
  unfold taoCor63ClearedOffsetSum
  rw [taoCor63ClearedOffsetSumFrom_eq_pow_mul_offset_reverse l 0 0 as]
  · simp
  · omega

/--
Reverse-order version of the checked Lemma 6.2 offset-injectivity spine.

This is the tuple-order adapter needed because the Corollary 6.3 proof writes
`F_{k+1}(a_{k+1}, ..., a_1)`.
-/
theorem taoLemma62_offset_injective_reverse {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (h : taoOffsetList as.reverse = taoOffsetList bs.reverse) :
    as = bs := by
  have hlenr : as.reverse.length = bs.reverse.length := by
    simpa using hlen
  have hrev : as.reverse = bs.reverse :=
    taoLemma62_offset_injective hlenr h
  exact List.reverse_injective hrev

/--
If two natural numbers are congruent modulo `m` and both lie in `[0,m)`, they
are equal.  This is the deterministic residue-to-equality step used after the
repaired Corollary 6.3 size estimate proves both cleared sums are `< 3^n`.
-/
theorem taoNatModEq_eq_of_lt {m a b : ℕ}
    (hmod : Nat.ModEq m a b) (ha : a < m) (hb : b < m) :
    a = b := by
  simpa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hmod

/--
Final Lemma 6.2 consumer after the hard Corollary 6.3 estimates have supplied
the rational cleared-offset identities.
-/
theorem taoCor63Star_eq_of_clearedOffset_eq
    {l : ℕ} {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (has :
      (taoCor63ClearedOffsetSum l as : ℚ) =
        (2 : ℚ) ^ l * taoOffsetList as.reverse)
    (hbs :
      (taoCor63ClearedOffsetSum l bs : ℚ) =
        (2 : ℚ) ^ l * taoOffsetList bs.reverse)
    (hsum : taoCor63ClearedOffsetSum l as = taoCor63ClearedOffsetSum l bs) :
    as = bs := by
  have hcast :
      (taoCor63ClearedOffsetSum l as : ℚ) =
        (taoCor63ClearedOffsetSum l bs : ℚ) := by
    exact_mod_cast hsum
  have hmul :
      (2 : ℚ) ^ l * taoOffsetList as.reverse =
        (2 : ℚ) ^ l * taoOffsetList bs.reverse := by
    rw [← has, ← hbs]
    exact hcast
  have hpow : (2 : ℚ) ^ l ≠ 0 :=
    pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)
  exact taoLemma62_offset_injective_reverse hlen
    (mul_left_cancel₀ hpow hmul)

/--
Same final consumer with the residue congruence and `< 3^n` bounds made
explicit.  The proof-producing work left for Corollary 6.3 star is then exactly
the two size bounds plus the cleared-offset rational identities.
-/
theorem taoCor63Star_eq_of_modEq_small_and_clearedOffset
    {n l : ℕ} {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (has :
      (taoCor63ClearedOffsetSum l as : ℚ) =
        (2 : ℚ) ^ l * taoOffsetList as.reverse)
    (hbs :
      (taoCor63ClearedOffsetSum l bs : ℚ) =
        (2 : ℚ) ^ l * taoOffsetList bs.reverse)
    (hmod : Nat.ModEq (3 ^ n)
      (taoCor63ClearedOffsetSum l as)
      (taoCor63ClearedOffsetSum l bs))
    (has_lt : taoCor63ClearedOffsetSum l as < 3 ^ n)
    (hbs_lt : taoCor63ClearedOffsetSum l bs < 3 ^ n) :
    as = bs := by
  exact taoCor63Star_eq_of_clearedOffset_eq hlen has hbs
    (taoNatModEq_eq_of_lt hmod has_lt hbs_lt)

theorem taoCor63Star_eq_of_modEq_small
    {n l : ℕ} {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (has_weight : taoTupleWeight as = l)
    (hbs_weight : taoTupleWeight bs = l)
    (hmod : Nat.ModEq (3 ^ n)
      (taoCor63ClearedOffsetSum l as)
      (taoCor63ClearedOffsetSum l bs))
    (has_lt : taoCor63ClearedOffsetSum l as < 3 ^ n)
    (hbs_lt : taoCor63ClearedOffsetSum l bs < 3 ^ n) :
    as = bs := by
  exact taoCor63Star_eq_of_modEq_small_and_clearedOffset
    hlen
    (taoCor63ClearedOffsetSum_eq_pow_mul_offset_reverse has_weight)
    (taoCor63ClearedOffsetSum_eq_pow_mul_offset_reverse hbs_weight)
    hmod has_lt hbs_lt

/-- A named residue-class form of the repaired Corollary 6.3 cleared offset. -/
def taoCor63ClearedOffsetZMod (n l : ℕ) (as : List ℕ+) : ZMod (3 ^ n) :=
  taoCor63ClearedOffsetSum l as

/--
Generic mathlib bridge: equality of natural residues in `ZMod m` is exactly
`Nat.ModEq m`.
-/
theorem taoNatModEq_of_zmod_natCast_eq {m a b : ℕ}
    (h : (a : ZMod m) = (b : ZMod m)) :
    Nat.ModEq m a b := by
  exact (ZMod.natCast_eq_natCast_iff a b m).mp h

/-- Cor63Star specialization of the `ZMod` equality to `Nat.ModEq` bridge. -/
theorem taoCor63NatModEq_of_clearedOffsetZMod_eq
    {n l : ℕ} {as bs : List ℕ+}
    (h : taoCor63ClearedOffsetZMod n l as =
      taoCor63ClearedOffsetZMod n l bs) :
    Nat.ModEq (3 ^ n)
      (taoCor63ClearedOffsetSum l as)
      (taoCor63ClearedOffsetSum l bs) := by
  exact taoNatModEq_of_zmod_natCast_eq
    (m := 3 ^ n)
    (a := taoCor63ClearedOffsetSum l as)
    (b := taoCor63ClearedOffsetSum l bs)
    (by simpa [taoCor63ClearedOffsetZMod] using h)

/--
Final deterministic Cor63Star consumer when the hard source work supplies
equality of cleared offset residues in `ZMod (3^n)` plus the two smallness
bounds.
-/
theorem taoCor63Star_eq_of_zmod_eq_small
    {n l : ℕ} {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (has_weight : taoTupleWeight as = l)
    (hbs_weight : taoTupleWeight bs = l)
    (hzmod : taoCor63ClearedOffsetZMod n l as =
      taoCor63ClearedOffsetZMod n l bs)
    (has_lt : taoCor63ClearedOffsetSum l as < 3 ^ n)
    (hbs_lt : taoCor63ClearedOffsetSum l bs < 3 ^ n) :
    as = bs := by
  exact taoCor63Star_eq_of_modEq_small
    hlen has_weight hbs_weight
    (taoCor63NatModEq_of_clearedOffsetZMod_eq hzmod)
    has_lt hbs_lt

/-- The unit represented by `2` in `ZMod (3^n)`. -/
noncomputable def taoCor63TwoUnit (n : ℕ) : (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime 2 (Nat.Coprime.pow_right n (by decide : Nat.Coprime 2 3))

/-- The unit represented by `2^l` in `ZMod (3^n)`. -/
noncomputable def taoCor63TwoPowUnit (n l : ℕ) : (ZMod (3 ^ n))ˣ :=
  (taoCor63TwoUnit n) ^ l

theorem taoCor63TwoUnit_coe (n : ℕ) :
    (taoCor63TwoUnit n : ZMod (3 ^ n)) = 2 := by
  simp [taoCor63TwoUnit]

theorem taoCor63TwoPowUnit_coe (n l : ℕ) :
    (taoCor63TwoPowUnit n l : ZMod (3 ^ n)) = (2 : ZMod (3 ^ n)) ^ l := by
  simp [taoCor63TwoPowUnit, taoCor63TwoUnit_coe]

/--
Source-facing residue of Tao's `F_{k+1}` modulo `3^n`, after using the
ambient total weight `l`: this is `2^{-l}` times the cleared offset sum.
-/
noncomputable def taoCor63SourceOffsetZMod
    (n l : ℕ) (as : List ℕ+) : ZMod (3 ^ n) :=
  ((taoCor63TwoPowUnit n l)⁻¹ : (ZMod (3 ^ n))ˣ) *
    taoCor63ClearedOffsetZMod n l as

/--
Multiplying the source-facing residue by `2^l` recovers the cleared offset
residue.
-/
theorem taoCor63TwoPow_mul_sourceOffsetZMod
    (n l : ℕ) (as : List ℕ+) :
    (taoCor63TwoPowUnit n l : ZMod (3 ^ n)) *
      taoCor63SourceOffsetZMod n l as =
    taoCor63ClearedOffsetZMod n l as := by
  simp [taoCor63SourceOffsetZMod]

/--
If the source-facing `F` residues are equal modulo `3^n`, then the cleared
offset residues are equal modulo `3^n`.
-/
theorem taoCor63ClearedOffsetZMod_eq_of_sourceOffsetZMod_eq
    {n l : ℕ} {as bs : List ℕ+}
    (h : taoCor63SourceOffsetZMod n l as =
      taoCor63SourceOffsetZMod n l bs) :
    taoCor63ClearedOffsetZMod n l as =
      taoCor63ClearedOffsetZMod n l bs := by
  calc
    taoCor63ClearedOffsetZMod n l as =
        (taoCor63TwoPowUnit n l : ZMod (3 ^ n)) *
          taoCor63SourceOffsetZMod n l as := by
          rw [taoCor63TwoPow_mul_sourceOffsetZMod]
    _ = (taoCor63TwoPowUnit n l : ZMod (3 ^ n)) *
          taoCor63SourceOffsetZMod n l bs := by
          rw [h]
    _ = taoCor63ClearedOffsetZMod n l bs := by
          rw [taoCor63TwoPow_mul_sourceOffsetZMod]

/--
End-to-end deterministic consumer from source-facing residue equality and the
two smallness bounds.
-/
theorem taoCor63Star_eq_of_sourceOffsetZMod_eq_small
    {n l : ℕ} {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (has_weight : taoTupleWeight as = l)
    (hbs_weight : taoTupleWeight bs = l)
    (hsource : taoCor63SourceOffsetZMod n l as =
      taoCor63SourceOffsetZMod n l bs)
    (has_lt : taoCor63ClearedOffsetSum l as < 3 ^ n)
    (hbs_lt : taoCor63ClearedOffsetSum l bs < 3 ^ n) :
    as = bs := by
  exact taoCor63Star_eq_of_zmod_eq_small
    hlen has_weight hbs_weight
    (taoCor63ClearedOffsetZMod_eq_of_sourceOffsetZMod_eq hsource)
    has_lt hbs_lt

/--
One-sided repaired Corollary 6.3 smallness target.

This is the formal version of the source proof's estimate after `(6.14)`,
ending with each natural-number side being `< 3^n`.
-/
noncomputable def TaoCor63StarSmallnessStatement : Prop :=
  ∀ CA : ℝ, 17 ≤ CA → ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    ∀ k l : ℕ, taoCor63StarLRange CA n l →
      ∀ as : List ℕ+,
        as.length = k + 1 →
        taoTupleWeight as = l →
        taoCor63StarInclusiveTypical CA n as →
        taoCor63ClearedOffsetSum l as < 3 ^ n

theorem TaoCor63StarSmallnessStatement.of_geometricEnvelope
    (henv : TaoCor63StarEnvelopeSmallnessStatement) :
    TaoCor63StarSmallnessStatement := by
  intro CA hCA
  refine ⟨Classical.choose (henv CA hCA), ?_⟩
  intro n hn k l hrange as hlen hweight htyp
  exact taoCor63ClearedOffsetSum_lt_of_geometricEnvelopeSum_lt
    (CA := CA) (n := n) (l := l) (as := as) hweight htyp
    (Classical.choose_spec (henv CA hCA) n hn k l hrange as hlen hweight htyp)

theorem TaoCor63StarSmallnessStatement.from_quarter_route :
    TaoCor63StarSmallnessStatement := by
  intro CA hCA
  obtain ⟨N0, hN0⟩ :=
    taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_eventually_CA17_D16
      (CA := CA) hCA
  refine ⟨N0, ?_⟩
  intro n hn k l hrange as _hlen hweight htyp
  exact hN0 n hn l as hweight htyp hrange

/--
Consumer showing that the one-sided smallness target plus source-facing residue
equality gives the repaired Corollary 6.3 deterministic separation endpoint.
-/
theorem taoCor63Star_eq_of_sourceOffsetZMod_eq_of_smallness
    (hsmall : TaoCor63StarSmallnessStatement)
    {CA : ℝ} (hCA : 17 ≤ CA)
    {n : ℕ} (hn : Classical.choose (hsmall CA hCA) ≤ n)
    {k l : ℕ} (hrange : taoCor63StarLRange CA n l)
    {as bs : List ℕ+}
    (has_len : as.length = k + 1)
    (hbs_len : bs.length = k + 1)
    (has_weight : taoTupleWeight as = l)
    (hbs_weight : taoTupleWeight bs = l)
    (has_typical : taoCor63StarInclusiveTypical CA n as)
    (hbs_typical : taoCor63StarInclusiveTypical CA n bs)
    (hsource : taoCor63SourceOffsetZMod n l as =
      taoCor63SourceOffsetZMod n l bs) :
    as = bs := by
  classical
  let N0 := Classical.choose (hsmall CA hCA)
  have hsmall_at := Classical.choose_spec (hsmall CA hCA)
  have hn' : N0 ≤ n := hn
  have has_lt : taoCor63ClearedOffsetSum l as < 3 ^ n :=
    hsmall_at n hn' k l hrange as has_len has_weight has_typical
  have hbs_lt : taoCor63ClearedOffsetSum l bs < 3 ^ n :=
    hsmall_at n hn' k l hrange bs hbs_len hbs_weight hbs_typical
  exact taoCor63Star_eq_of_sourceOffsetZMod_eq_small
    (has_len.trans hbs_len.symm) has_weight hbs_weight hsource has_lt hbs_lt

theorem TaoCor63StarClearedSeparationStatement.of_smallness
    (hsmall : TaoCor63StarSmallnessStatement) :
    TaoCor63StarClearedSeparationStatement := by
  intro CA hCA
  refine ⟨Classical.choose (hsmall CA hCA), ?_⟩
  intro n hn k l hrange as bs has_len hbs_len has_weight hbs_weight
    has_typical hbs_typical hmod
  have hsmall_at := Classical.choose_spec (hsmall CA hCA)
  have has_lt : taoCor63ClearedOffsetSum l as < 3 ^ n :=
    hsmall_at n hn k l hrange as has_len has_weight has_typical
  have hbs_lt : taoCor63ClearedOffsetSum l bs < 3 ^ n :=
    hsmall_at n hn k l hrange bs hbs_len hbs_weight hbs_typical
  have hlen : as.length = bs.length := by
    omega
  exact
    taoCor63Star_eq_of_modEq_small
      (n := n) (l := l) (as := as) (bs := bs)
      hlen has_weight hbs_weight hmod has_lt hbs_lt

theorem TaoCor63StarClearedSeparationStatement.from_quarter_route :
    TaoCor63StarClearedSeparationStatement :=
  TaoCor63StarClearedSeparationStatement.of_smallness
    TaoCor63StarSmallnessStatement.from_quarter_route

/--
Complete repaired Corollary 6.3 source-residue separation statement, factored
through the one-sided smallness statement.
-/
noncomputable def TaoCor63StarSourceResidueSeparationStatement : Prop :=
  ∀ CA : ℝ, 17 ≤ CA → ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    ∀ k l : ℕ, taoCor63StarLRange CA n l →
      ∀ as bs : List ℕ+,
        as.length = k + 1 →
        bs.length = k + 1 →
        taoTupleWeight as = l →
        taoTupleWeight bs = l →
        taoCor63StarInclusiveTypical CA n as →
        taoCor63StarInclusiveTypical CA n bs →
        taoCor63SourceOffsetZMod n l as =
          taoCor63SourceOffsetZMod n l bs →
        as = bs

theorem TaoCor63StarSourceResidueSeparationStatement.of_smallness
    (hsmall : TaoCor63StarSmallnessStatement) :
    TaoCor63StarSourceResidueSeparationStatement := by
  intro CA hCA
  refine ⟨Classical.choose (hsmall CA hCA), ?_⟩
  intro n hn k l hrange as bs has_len hbs_len has_weight hbs_weight
    has_typical hbs_typical hsource
  exact taoCor63Star_eq_of_sourceOffsetZMod_eq_of_smallness hsmall hCA hn
    hrange has_len hbs_len has_weight hbs_weight has_typical hbs_typical hsource

theorem TaoCor63StarSourceResidueSeparationStatement.of_clearedSeparation
    (hclear : TaoCor63StarClearedSeparationStatement) :
    TaoCor63StarSourceResidueSeparationStatement := by
  intro CA hCA
  refine ⟨Classical.choose (hclear CA hCA), ?_⟩
  intro n hn k l hrange as bs has_len hbs_len has_weight hbs_weight
    has_typical hbs_typical hsource
  have hclear_at := Classical.choose_spec (hclear CA hCA)
  exact hclear_at n hn k l hrange as bs has_len hbs_len
    has_weight hbs_weight has_typical hbs_typical
    (taoCor63NatModEq_of_clearedOffsetZMod_eq
      (taoCor63ClearedOffsetZMod_eq_of_sourceOffsetZMod_eq hsource))

theorem TaoCor63StarSourceResidueSeparationStatement.from_quarter_route :
    TaoCor63StarSourceResidueSeparationStatement :=
  TaoCor63StarSourceResidueSeparationStatement.of_smallness
    TaoCor63StarSmallnessStatement.from_quarter_route

end Tao
end Erdos1135
