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

noncomputable def taoSection6HeadGate
    (CA : ℝ) (n k l : ℕ) (head : List ℕ+) : Prop :=
  head.length = k + 1 ∧
    taoCor63StarInclusiveTypical CA n head ∧
    ((taoTupleWeight (head.take k) : ℕ) : ℝ) ≤ taoCor63StarQ CA n ∧
    taoCor63StarQ CA n < ((taoTupleWeight head : ℕ) : ℝ) ∧
    taoTupleWeight head = l

theorem taoSection6HeadGate_length
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (h : taoSection6HeadGate CA n k l head) :
    head.length = k + 1 :=
  h.1

theorem taoSection6HeadGate_typical
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (h : taoSection6HeadGate CA n k l head) :
    taoCor63StarInclusiveTypical CA n head :=
  h.2.1

theorem taoSection6HeadGate_crossing
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (h : taoSection6HeadGate CA n k l head) :
    ((taoTupleWeight (head.take k) : ℕ) : ℝ) ≤ taoCor63StarQ CA n ∧
      taoCor63StarQ CA n < ((taoTupleWeight head : ℕ) : ℝ) :=
  ⟨h.2.2.1, h.2.2.2.1⟩

theorem taoSection6HeadGate_weight
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (h : taoSection6HeadGate CA n k l head) :
    taoTupleWeight head = l :=
  h.2.2.2.2

end

end Tao

end Erdos1135Predecessor
