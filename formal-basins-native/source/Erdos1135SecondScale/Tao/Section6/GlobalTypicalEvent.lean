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
# Section 6 Global Typical Event

This leaf records Tao's repaired global event `E`: exact source length together
with inclusive concentration on every zero-based half-open interval.  It also
proves that the global event restricts to each head prefix.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Repaired global Section 6 event, including exact source length. -/
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

/-- Interval weight is unchanged by taking any prefix that retains the right
endpoint. -/
theorem taoSection6IntervalWeight_take_of_le
    (full : List ℕ+) {r i j : ℕ} (hj : j ≤ r) :
    taoSection6IntervalWeight (full.take r) i j =
      taoSection6IntervalWeight full i j := by
  unfold taoSection6IntervalWeight
  rw [List.drop_take, List.take_take]
  rw [Nat.min_eq_left (Nat.sub_le_sub_right hj i)]

/-- Inclusive typicality restricts to `take r` without a separate length
hypothesis. -/
theorem taoCor63StarInclusiveTypical_take
    {CA : ℝ} {n r : ℕ} {full : List ℕ+}
    (htyp : taoCor63StarInclusiveTypical CA n full) :
    taoCor63StarInclusiveTypical CA n (full.take r) := by
  intro i j hij hj
  have hjr : j ≤ r := hj.trans (List.length_take_le r full)
  have hjfull : j ≤ full.length := hj.trans (List.length_take_le' r full)
  simpa [taoSection6IntervalWeight_take_of_le full hjr] using
    htyp i j hij hjfull

/-- Global inclusive typicality restricts to every retained head prefix. -/
theorem taoSection6GlobalTypical_take_typical
    {CA : ℝ} {n r : ℕ} {full : List ℕ+}
    (hglobal : taoSection6GlobalTypical CA n full) :
    taoCor63StarInclusiveTypical CA n (full.take r) :=
  taoCor63StarInclusiveTypical_take (taoSection6GlobalTypical_typical hglobal)

/-- Exact prefix length under the global source-length field. -/
theorem taoSection6GlobalTypical_take_length
    {CA : ℝ} {n r : ℕ} {full : List ℕ+}
    (hglobal : taoSection6GlobalTypical CA n full) (hr : r ≤ n) :
    (full.take r).length = r := by
  simp [List.length_take, taoSection6GlobalTypical_length hglobal,
    Nat.min_eq_left hr]

/-- Bundled exact-length and typicality restriction for a retained prefix. -/
theorem taoSection6GlobalTypical_take_of_le
    {CA : ℝ} {n r : ℕ} {full : List ℕ+}
    (hglobal : taoSection6GlobalTypical CA n full) (hr : r ≤ n) :
    (full.take r).length = r ∧
      taoCor63StarInclusiveTypical CA n (full.take r) :=
  ⟨taoSection6GlobalTypical_take_length hglobal hr,
    taoSection6GlobalTypical_take_typical hglobal⟩

/-- Vacuous zero-prefix canary. -/
theorem taoSection6GlobalTypical_take_zero
    {CA : ℝ} {n : ℕ} {full : List ℕ+}
    (hglobal : taoSection6GlobalTypical CA n full) :
    taoCor63StarInclusiveTypical CA n (full.take 0) :=
  taoSection6GlobalTypical_take_typical hglobal

/-- The retained prefix carries its literal full interval `(0,r)`. -/
theorem taoSection6GlobalTypical_take_full_interval
    {CA : ℝ} {n r : ℕ} {full : List ℕ+}
    (hr_pos : 0 < r) (hr : r ≤ n)
    (hglobal : taoSection6GlobalTypical CA n full) :
    |((taoSection6IntervalWeight (full.take r) 0 r : ℕ) : ℝ) -
        2 * (r : ℝ)| ≤ taoCor63PrefixError CA n r := by
  exact taoCor63StarInclusiveTypical_prefix_abs
    (taoSection6GlobalTypical_take_typical hglobal) hr_pos
    (taoSection6GlobalTypical_take_length hglobal hr).ge

/-- Full-interval canary `(0,n)` for the repaired global event. -/
theorem taoSection6GlobalTypical_full_interval
    {CA : ℝ} {n : ℕ} {full : List ℕ+}
    (hn : 0 < n) (hglobal : taoSection6GlobalTypical CA n full) :
    |((taoTupleWeight full : ℕ) : ℝ) - 2 * (n : ℝ)| ≤
      taoCor63PrefixError CA n n := by
  have h := taoCor63StarInclusiveTypical_total_abs
    (taoSection6GlobalTypical_typical hglobal) (by
      rw [taoSection6GlobalTypical_length hglobal]
      exact hn)
  simpa [taoSection6GlobalTypical_length hglobal] using h

/-- Singleton canary `(0,1)` for the repaired global event. -/
theorem taoSection6GlobalTypical_first_singleton
    {CA : ℝ} {n : ℕ} {full : List ℕ+}
    (hn : 1 ≤ n) (hglobal : taoSection6GlobalTypical CA n full) :
    |((taoSection6IntervalWeight (full.take 1) 0 1 : ℕ) : ℝ) - 2| ≤
      CA * (Real.sqrt (Real.log (n : ℝ)) + Real.log (n : ℝ)) := by
  simpa [taoCor63PrefixError] using
    taoSection6GlobalTypical_take_full_interval (r := 1) (by omega) hn hglobal

end

end Tao
end Erdos1135SecondScale
