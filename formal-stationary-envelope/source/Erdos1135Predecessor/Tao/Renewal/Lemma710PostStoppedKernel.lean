/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma710KernelWindow
import Erdos1135Predecessor.Tao.Renewal.PathGrowth
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3Stopping
import Erdos1135Predecessor.Tao.Renewal.VerticalFirstPassageBasic

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma710

theorem renewalPathPoint_append_prefix_add
    (start : TaoSection7RenewalPoint) :
    ∀ (pre tail : List TaoSection7RenewalPoint) (p : ℕ),
      taoSection7RenewalPathPoint start (pre ++ tail) (pre.length + p) =
        taoSection7RenewalPathPoint
          (taoSection7RenewalPathPoint start pre pre.length) tail p
  | [], tail, p => by simp
  | h :: pre, tail, p => by
      simpa [taoSection7RenewalPathPoint, Nat.succ_add] using
        renewalPathPoint_append_prefix_add (start + h) pre tail p

theorem renewalPathPoint_take_eq_of_le
    (start : TaoSection7RenewalPoint) :
    ∀ (holds : List TaoSection7RenewalPoint) (n m : ℕ),
      n ≤ m →
        taoSection7RenewalPathPoint start (holds.take m) n =
          taoSection7RenewalPathPoint start holds n
  | holds, 0, m, _hm => by simp
  | [], n + 1, m, _hm => by simp
  | h :: hs, n + 1, 0, hm => by omega
  | h :: hs, n + 1, m + 1, hm => by
      have hn : n ≤ m := Nat.succ_le_succ_iff.mp hm
      simpa [taoSection7RenewalPathPoint] using
        renewalPathPoint_take_eq_of_le (start + h) hs n m hn

def EprimeVerticalSourceEvent
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (sourceThreshold : ℝ)
    (full : List TaoSection7RenewalPoint) : Prop :=
  sourceThreshold ≤
    (((taoSection7RenewalPathPoint start full full.length).l -
      old.cornerL : ℤ) : ℝ)

def EprimeHorizontalSourceEvent
    (start : TaoSection7RenewalPoint)
    (horizontalCenter sourceThreshold : ℝ)
    (full : List TaoSection7RenewalPoint) : Prop :=
  sourceThreshold ≤
    |(((taoSection7RenewalPathPoint start full full.length).j : ℕ) : ℝ) -
      horizontalCenter|

end TaoSection7Lemma710

end

end Tao

end Erdos1135Predecessor
