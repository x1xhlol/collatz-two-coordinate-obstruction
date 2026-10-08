/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.PascalPrime
import Mathlib.Tactic

/-!
# Section 7 Hold/Renewal Point Bridge

This module records deterministic finite-list bookkeeping for Tao's first
`b_j = 3` holding point and the renewal point type used by later finite
recursions.  It does not construct a `Hold` PMF or an iid renewal process.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- A source-shaped Section 7 holding-time or hit point `(j, l)`. -/
@[ext]
structure TaoSection7HoldPoint where
  j : ℕ+
  l : ℤ
deriving DecidableEq, Repr

/-- A Section 7 renewal-process point `(j, l)` in `(ℕ+ × ℤ)`. -/
@[ext]
structure TaoSection7RenewalPoint where
  j : ℕ+
  l : ℤ
deriving DecidableEq, Repr

namespace TaoSection7RenewalPoint

/-- Addition of a holding-time increment to a Section 7 lattice point. -/
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

/-- Forget that a point came from the first-Hold extraction surface. -/
def toRenewal (p : TaoSection7HoldPoint) : TaoSection7RenewalPoint :=
  { j := p.j, l := p.l }

/-- Regard a renewal point as a holding-time-shaped point. -/
def ofRenewal (p : TaoSection7RenewalPoint) : TaoSection7HoldPoint :=
  { j := p.j, l := p.l }

@[simp] theorem toRenewal_j (p : TaoSection7HoldPoint) :
    p.toRenewal.j = p.j :=
  rfl

@[simp] theorem toRenewal_l (p : TaoSection7HoldPoint) :
    p.toRenewal.l = p.l :=
  rfl

@[simp] theorem ofRenewal_j (p : TaoSection7RenewalPoint) :
    (ofRenewal p).j = p.j :=
  rfl

@[simp] theorem ofRenewal_l (p : TaoSection7RenewalPoint) :
    (ofRenewal p).l = p.l :=
  rfl

@[simp] theorem ofRenewal_toRenewal (p : TaoSection7HoldPoint) :
    ofRenewal p.toRenewal = p := by
  ext <;> rfl

@[simp] theorem toRenewal_ofRenewal (p : TaoSection7RenewalPoint) :
    (ofRenewal p).toRenewal = p := by
  ext <;> rfl

theorem toRenewal_injective :
    Function.Injective TaoSection7HoldPoint.toRenewal := by
  intro p q hpq
  exact congrArg ofRenewal hpq

@[simp] theorem toRenewal_eq_toRenewal {p q : TaoSection7HoldPoint} :
    p.toRenewal = q.toRenewal ↔ p = q := by
  constructor
  · exact fun h => toRenewal_injective h
  · intro h
    rw [h]

end TaoSection7HoldPoint

/-- Shift a positive source index by a natural prefix length. -/
def taoSection7ShiftIndex (j : ℕ+) (n : ℕ) : ℕ+ :=
  ⟨(j : ℕ) + n, Nat.add_pos_left j.2 n⟩

@[simp] theorem taoSection7ShiftIndex_zero (j : ℕ+) :
    taoSection7ShiftIndex j 0 = j := by
  exact Subtype.ext rfl

@[simp] theorem taoSection7ShiftIndex_one_zero (n : ℕ) :
    taoSection7ShiftIndex (1 : ℕ+) n =
      ⟨n + 1, Nat.succ_pos n⟩ := by
  apply Subtype.ext
  simp [taoSection7ShiftIndex]
  omega

/--
First holding-time point in a finite `b`-prefix, starting from source index
`j` and previous prefix sum `s`.
-/
def taoSection7FirstHoldFrom :
    ℕ+ → ℕ → List ℕ → Option TaoSection7HoldPoint
  | _j, _s, [] => none
  | j, s, b :: bs =>
      if b = 3 then
        some { j := j, l := Int.ofNat (s + b) }
      else
        taoSection7FirstHoldFrom (j + 1) (s + b) bs

/-- Top-level finite first holding-time point. -/
def taoSection7FirstHold (bs : List ℕ) : Option TaoSection7HoldPoint :=
  taoSection7FirstHoldFrom 1 0 bs

theorem taoSection7FirstHoldFrom_cons_hit
    (j : ℕ+) (s : ℕ) (bs : List ℕ) :
    taoSection7FirstHoldFrom j s (3 :: bs) =
      some { j := j, l := Int.ofNat (s + 3) } := by
  simp [taoSection7FirstHoldFrom]

/--
If `pre` contains no `3`, then appending `3 :: suf` makes the first holding
time exactly the source point `(j + pre.length, s + pre.sum + 3)`.
-/
theorem taoSection7FirstHoldFrom_split
    (j : ℕ+) (s : ℕ) (pre suf : List ℕ)
    (hpre : taoSection7NoThree pre) :
    taoSection7FirstHoldFrom j s (pre ++ 3 :: suf) =
      some
        { j := taoSection7ShiftIndex j pre.length
          l := Int.ofNat (s + pre.sum + 3) } := by
  induction pre generalizing j s with
  | nil =>
      rw [List.nil_append, taoSection7FirstHoldFrom_cons_hit]
      rfl
  | cons b pre ih =>
      have hb : b ≠ 3 := hpre b (by simp)
      have htail : taoSection7NoThree pre := by
        intro x hx
        exact hpre x (by simp [hx])
      simp [taoSection7FirstHoldFrom, hb]
      rw [ih (j + 1) (s + b) htail]
      congr 1
      apply TaoSection7HoldPoint.ext
      · apply Subtype.ext
        simp [taoSection7ShiftIndex]
        omega
      · simp
        omega

theorem taoSection7FirstHold_split
    (pre suf : List ℕ) (hpre : taoSection7NoThree pre) :
    taoSection7FirstHold (pre ++ 3 :: suf) =
      some
        { j := taoSection7ShiftIndex (1 : ℕ+) pre.length
          l := Int.ofNat (pre.sum + 3) } := by
  simpa [taoSection7FirstHold, Nat.zero_add] using
    taoSection7FirstHoldFrom_split (1 : ℕ+) 0 pre suf hpre

/--
Top-level first-Hold extraction with its point coerced into the renewal-recursion
point type.
-/
def taoSection7FirstHoldRenewal
    (bs : List ℕ) : Option TaoSection7RenewalPoint :=
  (taoSection7FirstHold bs).map TaoSection7HoldPoint.toRenewal

theorem taoSection7FirstHoldRenewal_split
    (pre suf : List ℕ) (hpre : taoSection7NoThree pre) :
    taoSection7FirstHoldRenewal (pre ++ 3 :: suf) =
      some
        { j := taoSection7ShiftIndex (1 : ℕ+) pre.length
          l := Int.ofNat (pre.sum + 3) } := by
  rw [taoSection7FirstHoldRenewal, taoSection7FirstHold_split pre suf hpre]
  rfl

theorem taoSection7Renewal_add_hold_toRenewal
    (p : TaoSection7RenewalPoint) (h : TaoSection7HoldPoint) :
    p + h.toRenewal =
      { j := p.j + h.j, l := p.l + h.l } := by
  rfl

end Tao
end Erdos1135SecondScale
