/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7ProductPenalty
import Erdos1135SecondScale.Tao.Probability.PascalPrime
import Mathlib.Tactic

/-!
# Section 7 White-Hit Count Splits

This module isolates source-list white-hit bookkeeping for finite paths.  It
splits the recursive count from `Section7ProductPenalty` across a no-`3`
prefix followed by the first `3`, without importing renewal or `Q` machinery.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Nat-valued indicator that a source hit point is white. -/
noncomputable def taoSection7WhiteHitIndicator
    (W : ℕ → ℤ → Prop) (j : ℕ) (l : ℤ) : ℕ := by
  classical
  exact if W j l then 1 else 0

theorem taoSection7WhiteHitCountFrom_append_noThree
    (W : ℕ → ℤ → Prop) (j s : ℕ) :
    ∀ (pre rest : List ℕ),
      taoSection7NoThree pre →
        taoSection7WhiteHitCountFrom W j s (pre ++ rest) =
          taoSection7WhiteHitCountFrom W (j + pre.length) (s + pre.sum) rest := by
  intro pre
  induction pre generalizing j s with
  | nil =>
      intro rest _hpre
      simp
  | cons b pre ih =>
      intro rest hpre
      have hb : b ≠ 3 := hpre b (by simp)
      have htail : taoSection7NoThree pre := by
        intro x hx
        exact hpre x (by simp [hx])
      simp [taoSection7WhiteHitCountFrom, hb]
      rw [ih (j + 1) (s + b) rest htail]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem taoSection7WhiteHitCountFrom_cons_three
    (W : ℕ → ℤ → Prop) (j s : ℕ) (rest : List ℕ) :
    taoSection7WhiteHitCountFrom W j s (3 :: rest) =
      taoSection7WhiteHitIndicator W j (Int.ofNat (s + 3)) +
        taoSection7WhiteHitCountFrom W (j + 1) (s + 3) rest := by
  classical
  simp [taoSection7WhiteHitIndicator, taoSection7WhiteHitCountFrom]

theorem taoSection7WhiteHitCountFrom_split_first_three
    (W : ℕ → ℤ → Prop) (j s : ℕ)
    (pre rest : List ℕ) (hpre : taoSection7NoThree pre) :
    taoSection7WhiteHitCountFrom W j s (pre ++ 3 :: rest) =
      taoSection7WhiteHitIndicator W
        (j + pre.length) (Int.ofNat (s + pre.sum + 3)) +
        taoSection7WhiteHitCountFrom W
          (j + pre.length + 1) (s + pre.sum + 3) rest := by
  rw [taoSection7WhiteHitCountFrom_append_noThree W j s pre (3 :: rest) hpre]
  rw [taoSection7WhiteHitCountFrom_cons_three]

end Tao
end Erdos1135SecondScale
