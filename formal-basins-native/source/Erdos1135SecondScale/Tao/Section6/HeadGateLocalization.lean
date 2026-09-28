/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.HeadGate

/-!
# Section 6 Head-Gate Range Localization

This deterministic leaf derives the repaired Corollary 6.3 star range from
Tao's crossing gate and inclusive singleton typicality.  It includes the
`k = 0` endpoint and introduces no PMF or residue map.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Adjacent prefix intervals add without any list-length hypothesis. -/
theorem taoSection6IntervalWeight_zero_add_adjacent
    (head : List ℕ+) (k : ℕ) :
    taoSection6IntervalWeight head 0 k +
        taoSection6IntervalWeight head k (k + 1) =
      taoSection6IntervalWeight head 0 (k + 1) := by
  unfold taoSection6IntervalWeight
  simp only [List.drop_zero, Nat.sub_zero, Nat.add_sub_cancel_left]
  rw [← List.sum_append, ← List.map_append]
  rw [List.take_add]

/-- A length-`k+1` head splits into its first `k` weights and the last
singleton interval. -/
theorem taoTupleWeight_eq_take_add_lastInterval
    (head : List ℕ+) {k : ℕ} (hhead : head.length = k + 1) :
    taoTupleWeight head =
      taoTupleWeight (head.take k) +
        taoSection6IntervalWeight head k (k + 1) := by
  calc
    taoTupleWeight head = taoSection6IntervalWeight head 0 (k + 1) := by
      rw [taoSection6IntervalWeight_zero_eq_tupleWeight_take]
      simp [← hhead]
    _ = taoSection6IntervalWeight head 0 k +
        taoSection6IntervalWeight head k (k + 1) := by
      exact (taoSection6IntervalWeight_zero_add_adjacent head k).symm
    _ = taoTupleWeight (head.take k) +
        taoSection6IntervalWeight head k (k + 1) := by
      rw [taoSection6IntervalWeight_zero_eq_tupleWeight_take]

/-- For `CA >= 17` and `log n >= 4`, one singleton typicality error fits
inside Tao's `2 CA log n` star window. -/
theorem taoCor63_singleton_error_le_window
    {CA x : ℝ} (hCA : 17 ≤ CA) (hx : 4 ≤ x) :
    2 + CA * (Real.sqrt x + x) ≤ 2 * CA * x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
  have hsqrt : Real.sqrt x ≤ x / 2 := by
    nlinarith
  have hCA0 : 0 ≤ CA := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsqrt hCA0
  nlinarith

/-- Tao's exact head gate forces the repaired star range once the singleton
typicality error fits in the star window. -/
theorem taoSection6HeadGate_starLRange_of_log_ge_four
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (hCA : 17 ≤ CA) (hlog : 4 ≤ Real.log (n : ℝ))
    (hgate : taoSection6HeadGate CA n k l head) :
    taoCor63StarLRange CA n l := by
  have hhead := taoSection6HeadGate_length hgate
  have htyp := taoSection6HeadGate_typical hgate
  have hcross := taoSection6HeadGate_crossing hgate
  have hweight := taoSection6HeadGate_weight hgate
  have hsingle := htyp k (k + 1) (by omega) (by omega)
  have hsingle' :
      |((taoSection6IntervalWeight head k (k + 1) : ℕ) : ℝ) - 2| ≤
        CA * (Real.sqrt (Real.log (n : ℝ)) + Real.log (n : ℝ)) := by
    simpa using hsingle
  have hsingle_upper :
      ((taoSection6IntervalWeight head k (k + 1) : ℕ) : ℝ) ≤
        2 + CA *
          (Real.sqrt (Real.log (n : ℝ)) + Real.log (n : ℝ)) := by
    have := (abs_le.mp hsingle').2
    linarith
  have hsplit := taoTupleWeight_eq_take_add_lastInterval head hhead
  have hsplit_real :
      ((taoTupleWeight head : ℕ) : ℝ) =
        ((taoTupleWeight (head.take k) : ℕ) : ℝ) +
          ((taoSection6IntervalWeight head k (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  have hscalar := taoCor63_singleton_error_le_window hCA hlog
  unfold taoCor63StarLRange
  constructor
  · simpa [hweight] using hcross.2
  · rw [hweight] at hsplit_real
    linarith

/-- Explicit endpoint canary: localization includes the repaired singleton
interval `(0,1)` when `k = 0`. -/
theorem taoSection6HeadGate_zero_starLRange_of_log_ge_four
    {CA : ℝ} {n l : ℕ} {head : List ℕ+}
    (hCA : 17 ≤ CA) (hlog : 4 ≤ Real.log (n : ℝ))
    (hgate : taoSection6HeadGate CA n 0 l head) :
    taoCor63StarLRange CA n l :=
  taoSection6HeadGate_starLRange_of_log_ge_four hCA hlog hgate

/-- Eventual range localization for every head gate. -/
theorem exists_taoSection6HeadGate_starLRange
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ Nlog : ℕ, ∀ n : ℕ, Nlog ≤ n →
      ∀ k l : ℕ, ∀ head : List ℕ+,
        taoSection6HeadGate CA n k l head →
          taoCor63StarLRange CA n l := by
  obtain ⟨Nlog, hNlog⟩ := taoCor63_exists_nat_log_gt 4
  refine ⟨Nlog, ?_⟩
  intro n hn k l head hgate
  exact taoSection6HeadGate_starLRange_of_log_ge_four
    hCA (le_of_lt (hNlog n hn)) hgate

end

end Tao
end Erdos1135SecondScale
