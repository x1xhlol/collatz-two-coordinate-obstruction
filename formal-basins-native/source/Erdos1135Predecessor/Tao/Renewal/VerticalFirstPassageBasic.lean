/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.RenewalPathBasic
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

def taoSection7AllHoldIncrementsLGeOne
    (holds : List TaoSection7RenewalPoint) : Prop :=
  ∀ h : TaoSection7RenewalPoint, h ∈ holds → (1 : ℤ) ≤ h.l

theorem taoSection7AllHoldIncrementsLGeOne_tail
    {h : TaoSection7RenewalPoint} {hs : List TaoSection7RenewalPoint}
    (hall : taoSection7AllHoldIncrementsLGeOne (h :: hs)) :
    taoSection7AllHoldIncrementsLGeOne hs := by
  intro h' hh'
  exact hall h' (by simp [hh'])

theorem taoSection7RenewalPathPoint_l_growth_ge_steps
    (p : TaoSection7RenewalPoint) :
    ∀ (holds : List TaoSection7RenewalPoint) (n : ℕ),
      n ≤ holds.length →
        taoSection7AllHoldIncrementsLGeOne holds →
          p.l + (n : ℤ) ≤
            (taoSection7RenewalPathPoint p holds n).l := by
  intro holds
  induction holds generalizing p with
  | nil =>
      intro n hn _hall
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      simp [taoSection7RenewalPathPoint]
  | cons h hs ih =>
      intro n hn hall
      cases n with
      | zero =>
          simp [taoSection7RenewalPathPoint]
      | succ n =>
          have hn_tail : n ≤ hs.length := by
            simpa using Nat.succ_le_succ_iff.mp hn
          have htail : taoSection7AllHoldIncrementsLGeOne hs :=
            taoSection7AllHoldIncrementsLGeOne_tail hall
          have hhead : (1 : ℤ) ≤ h.l := hall h (by simp)
          have hrec :
              (p + h).l + (n : ℤ) ≤
                (taoSection7RenewalPathPoint (p + h) hs n).l :=
            ih (p + h) n hn_tail htail
          calc
            p.l + ((n + 1 : ℕ) : ℤ) = p.l + ((n : ℤ) + 1) := by norm_num
            _ = (p.l + h.l) + (n : ℤ) + (1 - h.l) := by ring
            _ ≤ (p.l + h.l) + (n : ℤ) := by omega
            _ = (p + h).l + (n : ℤ) := by simp
            _ ≤ (taoSection7RenewalPathPoint (p + h) hs n).l := hrec

namespace TaoSection7Lemma710

structure VerticalFirstPassagePrefix
    (start : TaoSection7RenewalPoint) (s K : ℕ)
    (pre : List TaoSection7RenewalPoint) : Prop where
  K_pos : 0 < K
  length_eq : pre.length = K
  crosses :
    start.l + (s : ℤ) < (taoSection7RenewalPathPoint start pre K).l
  minimal :
    ∀ k : ℕ, k < K →
      (taoSection7RenewalPathPoint start pre k).l ≤ start.l + (s : ℤ)

end TaoSection7Lemma710

end Tao

end Erdos1135Predecessor
