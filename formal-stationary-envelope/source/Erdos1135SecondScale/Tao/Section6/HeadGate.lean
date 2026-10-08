/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.Corollary63

/-!
# Section 6 Fixed Head Gate

This deterministic leaf records Tao's head-only event `E_k ∩ B_k ∩ C_{k,l}`.
It contains no tail, PMF, residue map, Fourier declaration, or star-range
hypothesis.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Tao's exact fixed-head gate: source length, inclusive typicality, the two
sides of the stopping crossing, and exact total weight. -/
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
end Erdos1135SecondScale
