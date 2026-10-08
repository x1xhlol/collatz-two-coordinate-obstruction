/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.Corollary63

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection6GlobalTypical
    (CA : ℝ) (n : ℕ) (full : List ℕ+) : Prop :=
  full.length = n ∧ taoCor63StarInclusiveTypical CA n full

theorem taoSection6GlobalTypical_length
    {CA : ℝ} {n : ℕ} {full : List ℕ+}
    (h : taoSection6GlobalTypical CA n full) :
    full.length = n :=
  h.1

theorem taoSection6GlobalTypical_typical
    {CA : ℝ} {n : ℕ} {full : List ℕ+}
    (h : taoSection6GlobalTypical CA n full) :
    taoCor63StarInclusiveTypical CA n full :=
  h.2

theorem taoSection6IntervalWeight_take_of_le
    (full : List ℕ+) {r i j : ℕ} (hj : j ≤ r) :
    taoSection6IntervalWeight (full.take r) i j =
      taoSection6IntervalWeight full i j := by
  unfold taoSection6IntervalWeight
  rw [List.drop_take, List.take_take]
  rw [Nat.min_eq_left (Nat.sub_le_sub_right hj i)]

theorem taoCor63StarInclusiveTypical_take
    {CA : ℝ} {n r : ℕ} {full : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n full) :
    taoCor63StarInclusiveTypical CA n (full.take r) := by
  intro i j hij hj
  have hjr : j ≤ r := hj.trans (List.length_take_le r full)
  have hjfull : j ≤ full.length := hj.trans (List.length_take_le' r full)
  simpa [taoSection6IntervalWeight_take_of_le full hjr] using
    htyp i j hij hjfull

theorem taoSection6GlobalTypical_take_typical
    {CA : ℝ} {n r : ℕ} {full : List ℕ+}
    (hglobal : taoSection6GlobalTypical CA n full) :
    taoCor63StarInclusiveTypical CA n (full.take r) :=
  taoCor63StarInclusiveTypical_take (taoSection6GlobalTypical_typical hglobal)

theorem taoSection6GlobalTypical_take_length
    {CA : ℝ} {n r : ℕ} {full : List ℕ+}
    (hglobal : taoSection6GlobalTypical CA n full) (hr : r ≤ n) :
    (full.take r).length = r := by
  simp [List.length_take, taoSection6GlobalTypical_length hglobal,
    Nat.min_eq_left hr]

end

end Tao

end Erdos1135Predecessor
