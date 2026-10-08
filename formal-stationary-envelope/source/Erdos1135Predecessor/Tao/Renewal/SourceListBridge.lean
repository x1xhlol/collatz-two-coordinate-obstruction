/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7WhiteHitSplit
import Erdos1135Predecessor.Tao.Renewal.QFinite
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

def taoSection7SourceBlocks : List (List ℕ) → List ℕ
  | [] => []
  | pre :: pres => pre ++ 3 :: taoSection7SourceBlocks pres

def taoSection7SourceHitPoint
    (j : ℕ+) (s : ℕ) (pre : List ℕ) : TaoSection7RenewalPoint :=
  { j := taoSection7ShiftIndex j pre.length
    l := Int.ofNat (s + pre.sum + 3) }

def taoSection7HoldIncrementOfPrefix
    (pre : List ℕ) : TaoSection7RenewalPoint :=
  { j := taoSection7ShiftIndex (1 : ℕ+) pre.length
    l := Int.ofNat (pre.sum + 3) }

def taoSection7HoldIncrementsOfPrefixes
    (pres : List (List ℕ)) : List TaoSection7RenewalPoint :=
  pres.map taoSection7HoldIncrementOfPrefix

def taoSection7SourceWhiteRenewal
    (W : ℕ → ℤ → Prop) : TaoSection7RenewalPoint → Prop :=
  fun p => W (p.j : ℕ) p.l

@[simp] theorem taoSection7SourceHitPoint_tail_eq_add
    (j : ℕ+) (s : ℕ) (pre next : List ℕ) :
    taoSection7SourceHitPoint
        (taoSection7ShiftIndex j (pre.length + 1))
        (s + pre.sum + 3) next =
      taoSection7SourceHitPoint j s pre +
        taoSection7HoldIncrementOfPrefix next := by
  ext
  · apply Subtype.ext
    change
      ((taoSection7ShiftIndex
          (taoSection7ShiftIndex j (pre.length + 1)) next.length : ℕ+) : ℕ) =
        (((taoSection7ShiftIndex j pre.length : ℕ+) +
          (taoSection7ShiftIndex (1 : ℕ+) next.length : ℕ+)) : ℕ+)
    rw [PNat.add_coe]
    simp [taoSection7ShiftIndex]
    omega
  · simp [taoSection7SourceHitPoint, taoSection7HoldIncrementOfPrefix]
    omega

theorem taoSection7WhiteHitCountFrom_blocks_eq_qvisit
    (W : ℕ → ℤ → Prop) :
    ∀ (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)),
      taoSection7NoThree pre →
        (∀ q ∈ pres, taoSection7NoThree q) →
          taoSection7WhiteHitCountFrom W (j : ℕ) s
              (taoSection7SourceBlocks (pre :: pres)) =
            taoSection7QWhiteVisitCount (taoSection7SourceWhiteRenewal W)
              (taoSection7SourceHitPoint j s pre)
              (taoSection7HoldIncrementsOfPrefixes pres) := by
  intro j s pre pres
  induction pres generalizing j s pre with
  | nil =>
      intro hpre _hpres
      simp only [taoSection7SourceBlocks, taoSection7HoldIncrementsOfPrefixes,
        List.map_nil]
      rw [taoSection7WhiteHitCountFrom_split_first_three W (j : ℕ) s pre [] hpre]
      simp [taoSection7QWhiteVisitCount, taoSection7QWhiteIndicator,
        taoSection7WhiteHitIndicator, taoSection7WhiteHitCountFrom,
        taoSection7SourceWhiteRenewal, taoSection7SourceHitPoint,
        taoSection7ShiftIndex, Nat.cast_list_sum]
  | cons next rest ih =>
      intro hpre hpres
      have hnext : taoSection7NoThree next := hpres next (by simp)
      have hrest : ∀ q ∈ rest, taoSection7NoThree q := by
        intro q hq
        exact hpres q (by simp [hq])
      rw [taoSection7SourceBlocks]
      rw [taoSection7WhiteHitCountFrom_split_first_three W (j : ℕ) s pre
        (taoSection7SourceBlocks (next :: rest)) hpre]
      have htail :
          taoSection7WhiteHitCountFrom W
              ((j : ℕ) + pre.length + 1) (s + pre.sum + 3)
              (taoSection7SourceBlocks (next :: rest)) =
            taoSection7QWhiteVisitCount (taoSection7SourceWhiteRenewal W)
              (taoSection7SourceHitPoint
                (taoSection7ShiftIndex j (pre.length + 1))
                (s + pre.sum + 3) next)
              (taoSection7HoldIncrementsOfPrefixes rest) := by
        simpa [taoSection7ShiftIndex, Nat.add_assoc] using
          ih (taoSection7ShiftIndex j (pre.length + 1))
            (s + pre.sum + 3) next hnext hrest
      rw [htail]
      rw [taoSection7SourceHitPoint_tail_eq_add]
      simp [taoSection7HoldIncrementsOfPrefixes, taoSection7QWhiteVisitCount,
        taoSection7QWhiteIndicator, taoSection7WhiteHitIndicator,
        taoSection7SourceWhiteRenewal, taoSection7SourceHitPoint,
        taoSection7ShiftIndex, Nat.cast_list_sum]
      have harg :
          (↑s + ↑pre.sum + 3 : ℤ) =
            (↑s + (List.map Nat.cast pre).sum + 3 : ℤ) := by
        rw [Nat.cast_list_sum]
      by_cases hw :
          W ((j : ℕ) + pre.length) (↑s + ↑pre.sum + 3 : ℤ)
      · have hw' :
            W ((j : ℕ) + pre.length)
              (↑s + (List.map Nat.cast pre).sum + 3 : ℤ) := by
          simpa [← harg] using hw
        simp [hw']
      · have hw' :
            ¬ W ((j : ℕ) + pre.length)
              (↑s + (List.map Nat.cast pre).sum + 3 : ℤ) := by
          intro h
          exact hw (by simpa [harg] using h)
        simp [hw']

theorem taoSection7WhiteHitCount_blocks_eq_qvisit
    (W : ℕ → ℤ → Prop)
    (pre : List ℕ) (pres : List (List ℕ))
    (hpre : taoSection7NoThree pre)
    (hpres : ∀ q ∈ pres, taoSection7NoThree q) :
    taoSection7WhiteHitCount W (taoSection7SourceBlocks (pre :: pres)) =
      taoSection7QWhiteVisitCount (taoSection7SourceWhiteRenewal W)
        (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
        (taoSection7HoldIncrementsOfPrefixes pres) := by
  simpa [taoSection7WhiteHitCount] using
    taoSection7WhiteHitCountFrom_blocks_eq_qvisit W
      (1 : ℕ+) 0 pre pres hpre hpres

theorem taoSection7WhiteHitPenalty_blocks_eq_qfinite
    (epsilon : ℝ) (W : ℕ → ℤ → Prop)
    (pre : List ℕ) (pres : List (List ℕ))
    (hpre : taoSection7NoThree pre)
    (hpres : ∀ q ∈ pres, taoSection7NoThree q) :
    taoSection7WhiteHitPenalty epsilon W (taoSection7SourceBlocks (pre :: pres)) =
      taoSection7QFinite epsilon (taoSection7SourceWhiteRenewal W)
        (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
        (taoSection7HoldIncrementsOfPrefixes pres) := by
  rw [taoSection7WhiteHitPenalty, taoSection7WhiteHitPenaltyFrom]
  rw [taoSection7QFinite_eq_exp_count]
  have hcount :
      taoSection7WhiteHitCountFrom W 1 0
          (taoSection7SourceBlocks (pre :: pres)) =
        taoSection7QWhiteVisitCount (taoSection7SourceWhiteRenewal W)
          (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
          (taoSection7HoldIncrementsOfPrefixes pres) := by
    simpa [taoSection7WhiteHitCount] using
      taoSection7WhiteHitCount_blocks_eq_qvisit W pre pres hpre hpres
  rw [hcount]

end Tao

end Erdos1135Predecessor
