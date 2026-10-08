import Erdos1135.Tao.Fourier.Section7WhiteHitSplit
import Erdos1135.Tao.Renewal.QFinite
import Mathlib.Tactic

/-!
# Section 7 Source-List Bridge

This module connects finite source-list white-hit counts to the deterministic
point-domain `Q` recursion.  It works with finite decompositions into no-`3`
blocks terminated by `3`, and keeps cancellation and weighted Hold consumers in
later modules.
-/

namespace Erdos1135
namespace Tao

/-- Concatenate no-`3` blocks, each terminated by a `3` hit. -/
def taoSection7SourceBlocks : List (List ℕ) → List ℕ
  | [] => []
  | pre :: pres => pre ++ 3 :: taoSection7SourceBlocks pres

/-- The source hit point produced by a no-`3` prefix followed by `3`. -/
def taoSection7SourceHitPoint
    (j : ℕ+) (s : ℕ) (pre : List ℕ) : TaoSection7RenewalPoint :=
  { j := taoSection7ShiftIndex j pre.length
    l := Int.ofNat (s + pre.sum + 3) }

/-- The renewal increment produced by one no-`3` block followed by `3`. -/
def taoSection7HoldIncrementOfPrefix
    (pre : List ℕ) : TaoSection7RenewalPoint :=
  { j := taoSection7ShiftIndex (1 : ℕ+) pre.length
    l := Int.ofNat (pre.sum + 3) }

/-- Renewal increments associated to a finite block decomposition. -/
def taoSection7HoldIncrementsOfPrefixes
    (pres : List (List ℕ)) : List TaoSection7RenewalPoint :=
  pres.map taoSection7HoldIncrementOfPrefix

@[simp] theorem taoSection7HoldIncrementsOfPrefixes_length
    (pres : List (List ℕ)) :
    (taoSection7HoldIncrementsOfPrefixes pres).length = pres.length := by
  simp [taoSection7HoldIncrementsOfPrefixes]

theorem taoSection7HoldIncrementsOfPrefixes_take
    (n : ℕ) (pres : List (List ℕ)) :
    (taoSection7HoldIncrementsOfPrefixes pres).take n =
      taoSection7HoldIncrementsOfPrefixes (pres.take n) := by
  simp [taoSection7HoldIncrementsOfPrefixes, List.map_take]

/-- Adapt a source white predicate to renewal points. -/
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

/--
For a source path decomposed into no-`3` blocks ending in `3`, the source
white-hit count equals the finite Q visit count beginning at the first hit
point and continuing through the later Hold increments.
-/
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

theorem taoSection7FactorProduct_blocks_le_qfinite
    {epsilon : ℝ} {W : ℕ → ℤ → Prop} {F : ℕ → ℕ → ℕ → ℝ}
    (hFnonneg : ∀ j s b, 0 ≤ F j s b)
    (hFhit :
      ∀ j s b, b = 3 ∧ W j (Int.ofNat (s + b)) →
        F j s b ≤ Real.exp (-(epsilon ^ 3)))
    (hFmiss :
      ∀ j s b, ¬ (b = 3 ∧ W j (Int.ofNat (s + b))) →
        F j s b ≤ 1)
    (pre : List ℕ) (pres : List (List ℕ))
    (hpre : taoSection7NoThree pre)
    (hpres : ∀ q ∈ pres, taoSection7NoThree q) :
    taoSection7FactorProduct F (taoSection7SourceBlocks (pre :: pres)) ≤
      taoSection7QFinite epsilon (taoSection7SourceWhiteRenewal W)
        (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
        (taoSection7HoldIncrementsOfPrefixes pres) := by
  calc
    taoSection7FactorProduct F (taoSection7SourceBlocks (pre :: pres))
        ≤ taoSection7WhiteHitPenalty epsilon W
            (taoSection7SourceBlocks (pre :: pres)) := by
          exact taoSection7FactorProduct_le_penalty hFnonneg hFhit hFmiss
            (taoSection7SourceBlocks (pre :: pres))
    _ = taoSection7QFinite epsilon (taoSection7SourceWhiteRenewal W)
          (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
          (taoSection7HoldIncrementsOfPrefixes pres) := by
          exact taoSection7WhiteHitPenalty_blocks_eq_qfinite
            epsilon W pre pres hpre hpres

end Tao
end Erdos1135
