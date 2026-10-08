/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7SourceDomain
import Erdos1135SecondScale.Tao.Renewal.QActualLimit
import Erdos1135SecondScale.Tao.Renewal.SourceListBridge

/-!
# Section 7 Source Actual Q

This module instantiates the generic actual-`Q` terminal limit at Tao's source
cutoff predicate `J = n / 2`.  It does not define source `Q_m`, prove outer
`(7.36)`, or prove Proposition 7.8.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Tao's cutoff source-white predicate transported to renewal points. -/
noncomputable def taoSection7SourceActualW
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    TaoSection7RenewalPoint → Prop :=
  taoSection7SourceWhiteRenewal
    (taoSection7SourceWhiteWCutoff n xi epsilon (n / 2))

/--
Source actual `Q` obtained by instantiating the generic terminal-one limit at
the cutoff source-white renewal predicate.
-/
noncomputable def taoSection7SourceActualQ
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    TaoSection7RenewalPoint → ℝ :=
  taoSection7ActualQFiniteLimit epsilon
    (taoSection7SourceActualW n xi epsilon)

theorem taoSection7SourceActualQ_finiteLimit
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    TaoSection7ActualQFiniteLimitStatement epsilon
      (taoSection7SourceActualW n xi epsilon)
      (taoSection7SourceActualQ n xi epsilon) :=
  taoSection7ActualQFiniteLimit_statement hepsilon
    (taoSection7SourceActualW n xi epsilon)

theorem taoSection7SourceActualQ_bounded01
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    TaoSection7QBounded01
      (taoSection7SourceActualQ n xi epsilon) :=
  taoSection7ActualQFiniteLimit_bounded01 hepsilon
    (taoSection7SourceActualW n xi epsilon)

theorem taoSection7SourceActualQ_nonneg
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (p : TaoSection7RenewalPoint) :
    0 ≤ taoSection7SourceActualQ n xi epsilon p :=
  (taoSection7SourceActualQ_bounded01
    (n := n) (xi := xi) hepsilon p).1

theorem taoSection7SourceActualQ_le_one
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (p : TaoSection7RenewalPoint) :
    taoSection7SourceActualQ n xi epsilon p ≤ 1 :=
  (taoSection7SourceActualQ_bounded01
    (n := n) (xi := xi) hepsilon p).2

theorem taoSection7SourceActualQ_fullHoldQRecursion
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (p : TaoSection7RenewalPoint) :
    taoSection7SourceActualQ n xi epsilon p =
      taoSection7FullHoldQRecursionRHS epsilon
        (taoSection7SourceActualW n xi epsilon)
        (taoSection7SourceActualQ n xi epsilon) p :=
  taoSection7ActualQFiniteLimit_fullHoldQRecursion hepsilon
    (taoSection7SourceActualW n xi epsilon) p

end Tao
end Erdos1135SecondScale
