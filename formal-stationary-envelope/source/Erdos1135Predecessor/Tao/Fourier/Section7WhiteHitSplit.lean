/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7ProductPenalty
import Erdos1135Predecessor.Tao.Probability.PascalPrime
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

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

end Erdos1135Predecessor
