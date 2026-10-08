/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.HoldPoint

namespace Erdos1135Predecessor

namespace Tao

def taoSection7RenewalPathPoint
    (p : TaoSection7RenewalPoint) : List TaoSection7RenewalPoint → ℕ →
      TaoSection7RenewalPoint
  | _holds, 0 => p
  | [], _n + 1 => p
  | h :: hs, n + 1 => taoSection7RenewalPathPoint (p + h) hs n

@[simp] theorem taoSection7RenewalPathPoint_zero
    (p : TaoSection7RenewalPoint) (holds : List TaoSection7RenewalPoint) :
    taoSection7RenewalPathPoint p holds 0 = p := by
  cases holds <;> rfl

@[simp] theorem taoSection7RenewalPathPoint_nil
    (p : TaoSection7RenewalPoint) (n : ℕ) :
    taoSection7RenewalPathPoint p [] n = p := by
  cases n <;> rfl

@[simp] theorem taoSection7RenewalPathPoint_cons_succ
    (p h : TaoSection7RenewalPoint) (hs : List TaoSection7RenewalPoint)
    (n : ℕ) :
    taoSection7RenewalPathPoint p (h :: hs) (n + 1) =
      taoSection7RenewalPathPoint (p + h) hs n := by
  rfl

theorem taoSection7RenewalPathPoint_drop_add
    (p : TaoSection7RenewalPoint) :
    ∀ (holds : List TaoSection7RenewalPoint) (q n : ℕ),
      taoSection7RenewalPathPoint
          (taoSection7RenewalPathPoint p holds q)
          (holds.drop q) n =
        taoSection7RenewalPathPoint p holds (q + n) := by
  intro holds q
  induction q generalizing p holds with
  | zero =>
      intro n
      simp
  | succ q ih =>
      intro n
      cases holds with
      | nil =>
          simp
      | cons h hs =>
          rw [show q + 1 + n = q + n + 1 by omega]
          simpa [taoSection7RenewalPathPoint] using
            ih (p + h) hs n

theorem taoSection7RenewalPathPoint_drop_candidate_sub
    {p : TaoSection7RenewalPoint}
    {holds : List TaoSection7RenewalPoint} {q candidate : ℕ}
    (hq : q ≤ candidate) :
    taoSection7RenewalPathPoint
        (taoSection7RenewalPathPoint p holds q)
        (holds.drop q) (candidate - q) =
      taoSection7RenewalPathPoint p holds candidate := by
  have h :=
    taoSection7RenewalPathPoint_drop_add p holds q (candidate - q)
  have hsum : q + (candidate - q) = candidate := Nat.add_sub_of_le hq
  simpa [hsum] using h

theorem taoSection7RenewalPathPoint_take_eq_of_le
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
        taoSection7RenewalPathPoint_take_eq_of_le (start + h) hs n m hn

end Tao

end Erdos1135Predecessor
