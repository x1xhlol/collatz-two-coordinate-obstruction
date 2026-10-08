/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.RenewalPathBasic
import Mathlib.Tactic

/-!
# Low Vertical First-Passage Support

This module owns the generic vertical-growth predicate and Tao's finite
vertical first-passage prefix.  It deliberately has no geometry, stopping,
endpoint, or fresh-tail dependency.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Every increment in a list raises the `l` coordinate by at least one. -/
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

/-- Tao Lemma 7.10's finite vertical first-passage prefix. -/
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

theorem verticalFirstPassagePrefix_endpoint_crosses
    {start : TaoSection7RenewalPoint} {s K : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (h : VerticalFirstPassagePrefix start s K pre) :
    start.l + (s : ℤ) < (taoSection7RenewalPathPoint start pre K).l :=
  h.crosses

theorem verticalFirstPassagePrefix_before_le
    {start : TaoSection7RenewalPoint} {s K k : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (h : VerticalFirstPassagePrefix start s K pre)
    (hk : k < K) :
    (taoSection7RenewalPathPoint start pre k).l ≤ start.l + (s : ℤ) :=
  h.minimal k hk

end TaoSection7Lemma710

end Tao
end Erdos1135SecondScale
