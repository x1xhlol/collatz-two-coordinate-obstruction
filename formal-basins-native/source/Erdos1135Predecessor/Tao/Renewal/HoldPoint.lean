/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.PascalPrime
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

@[ext]
structure TaoSection7RenewalPoint where
  j : ℕ+
  l : ℤ
deriving DecidableEq, Repr

namespace TaoSection7RenewalPoint

def add (p h : TaoSection7RenewalPoint) : TaoSection7RenewalPoint :=
  { j := p.j + h.j
    l := p.l + h.l }

instance : Add TaoSection7RenewalPoint where
  add := add

@[simp] theorem add_j (p h : TaoSection7RenewalPoint) :
    (p + h).j = p.j + h.j :=
  rfl

@[simp] theorem add_l (p h : TaoSection7RenewalPoint) :
    (p + h).l = p.l + h.l :=
  rfl

end TaoSection7RenewalPoint

namespace TaoSection7HoldPoint

end TaoSection7HoldPoint

def taoSection7ShiftIndex (j : ℕ+) (n : ℕ) : ℕ+ :=
  ⟨(j : ℕ) + n, Nat.add_pos_left j.2 n⟩

@[simp] theorem taoSection7ShiftIndex_one_zero (n : ℕ) :
    taoSection7ShiftIndex (1 : ℕ+) n =
      ⟨n + 1, Nat.succ_pos n⟩ := by
  apply Subtype.ext
  simp [taoSection7ShiftIndex]
  omega

end Tao

end Erdos1135Predecessor
