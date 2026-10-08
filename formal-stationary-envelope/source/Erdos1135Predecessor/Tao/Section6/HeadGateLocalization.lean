/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.HeadGate

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoSection6IntervalWeight_zero_add_adjacent
    (head : List ℕ+) (k : ℕ) :
    taoSection6IntervalWeight head 0 k +
        taoSection6IntervalWeight head k (k + 1) =
      taoSection6IntervalWeight head 0 (k + 1) := by
  unfold taoSection6IntervalWeight
  simp only [List.drop_zero, Nat.sub_zero, Nat.add_sub_cancel_left]
  rw [← List.sum_append, ← List.map_append]
  rw [List.take_add]

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

end

end Tao

end Erdos1135Predecessor
