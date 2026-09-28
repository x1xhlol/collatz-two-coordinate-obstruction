/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79FirstEntryFiberLaw
import Erdos1135Predecessor.Tao.Renewal.Lemma79R2Aggregation

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79RawHoldFirstPassageFixedTailSplitPMF_eq_holdList_map
    (N J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    lemma79RawHoldFirstPassageFixedTailSplitPMF N J entry gap =
      (taoSection7HoldListPMF N).map
        (lemma79VerticalFirstPassageFixedTailSplit J entry gap) := by
  unfold lemma79RawHoldFirstPassageFixedTailSplitPMF
  change
    (taoSection7HoldSourcePrefixListPMF N).map
        (lemma79VerticalFirstPassageFixedTailSplit J entry gap ∘
          lemma79DecodeHoldSourcePrefixes) = _
  rw [← PMF.map_comp]
  change
    ((taoSection7HoldSourcePrefixListPMF N).map
        (fun xs => xs.map fun x =>
          taoSection7HoldPointOfPrefix x.1 x.2)).map
      (lemma79VerticalFirstPassageFixedTailSplit J entry gap) = _
  rw [taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq]

theorem lemma79VerticalFirstPassageFixedTailSplit_snd_eq_global_drop
    (p J N : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ)
    (full : List TaoSection7RenewalPoint)
    (hroom :
      lemma79VerticalFirstPassageCut entry gap
          ((full.drop p).take N) + J ≤ N) :
    let K := lemma79VerticalFirstPassageCut entry gap
      ((full.drop p).take N)
    (lemma79VerticalFirstPassageFixedTailSplit J entry gap
        ((full.drop p).take N)).2 =
      (full.drop (p + K)).take J := by
  dsimp only
  unfold lemma79VerticalFirstPassageFixedTailSplit
  dsimp only
  rw [List.drop_take, List.take_take]
  rw [Nat.min_eq_left (by omega)]
  simp [List.drop_drop]

theorem lemma79_holdList_firstEntryKey_firstPassageFixedTailExpectation_of_add_le
    {origin entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C B p gap J : ℕ}
    (hpC : p < C)
    (hroom : p + (gap + 1 + J) ≤ B)
    (G : List TaoSection7RenewalPoint ×
      List TaoSection7RenewalPoint -> ENNReal) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF B)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey origin family C)
          (some (p, entry.toPoint))).indicator
            (fun full =>
              G (lemma79VerticalFirstPassageFixedTailSplit J entry gap
                ((full.drop p).take (gap + 1 + J))))) =
      (taoSection7HoldListPMF B).toOuterMeasure
          (lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey origin family C)
            (some (p, entry.toPoint))) *
        lemma79PMFENNExpectation
          (lemma79RawHoldFirstPassageFixedTailSplitPMF
            (gap + 1 + J) J entry gap) G := by
  let N := gap + 1 + J
  let future : List TaoSection7RenewalPoint -> ENNReal :=
    fun block =>
      G (lemma79VerticalFirstPassageFixedTailSplit J entry gap block)
  have hfactor :=
    lemma79_holdList_firstEntryKey_freshBlockExpectation_of_add_le
      (start := origin) (family := family) (C := C)
      (p := p) (N := N) (B := B) (entry := entry.toPoint)
      hpC (by simpa [N] using hroom) future
  have hkeyMass :=
    lemma79_holdList_firstEntryKey_mass_eq_prefixMass_of_add_le
      (start := origin) (family := family) (C := C)
      (p := p) (N := N) (B := B) (entry := entry.toPoint)
      hpC (by simpa [N] using hroom)
  have hfuture :
      lemma79PMFENNExpectation (taoSection7HoldListPMF N) future =
        lemma79PMFENNExpectation
          (lemma79RawHoldFirstPassageFixedTailSplitPMF N J entry gap) G := by
    calc
      lemma79PMFENNExpectation (taoSection7HoldListPMF N) future =
          lemma79PMFENNExpectation
            ((taoSection7HoldListPMF N).map
              (lemma79VerticalFirstPassageFixedTailSplit J entry gap)) G :=
        (lemma79PMFENNExpectation_map
          (taoSection7HoldListPMF N)
          (lemma79VerticalFirstPassageFixedTailSplit J entry gap) G).symm
      _ = _ := by
        rw [← lemma79RawHoldFirstPassageFixedTailSplitPMF_eq_holdList_map]
  rw [← hkeyMass, hfuture] at hfactor
  simpa [N, future, lemma79KeyAtom, lemma79HoldPathHeadKey] using hfactor

theorem lemma79_holdList_firstEntryKey_firstPassageFixedTailWeightedExpectation_le
    {origin entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C B p gap J : ℕ}
    (hpC : p < C)
    (hroom : p + (gap + 1 + J) ≤ B)
    (prefixWeight : List TaoSection7RenewalPoint -> ENNReal)
    (future : TaoSection7RenewalPoint ->
      List TaoSection7RenewalPoint -> ENNReal)
    (D : ENNReal)
    (hfuture : ∀ endpoint,
      lemma79PMFENNExpectation
        (taoSection7HoldListPMF J) (future endpoint) ≤ D) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF B)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey origin family C)
          (some (p, entry.toPoint))).indicator
            (fun full =>
              let pair :=
                lemma79VerticalFirstPassageFixedTailSplit J entry gap
                  ((full.drop p).take (gap + 1 + J))
              prefixWeight pair.1 *
                future
                  (taoSection7RenewalPathPoint
                    entry pair.1 pair.1.length)
                  pair.2)) ≤
      (taoSection7HoldListPMF B).toOuterMeasure
          (lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey origin family C)
            (some (p, entry.toPoint))) *
        (D * lemma79PMFENNExpectation
          (lemma79RawHoldFirstPassagePrefixPMF J entry gap)
          prefixWeight) := by
  let G : List TaoSection7RenewalPoint ×
      List TaoSection7RenewalPoint -> ENNReal :=
    fun pair =>
      prefixWeight pair.1 *
        future
          (taoSection7RenewalPathPoint entry pair.1 pair.1.length)
          pair.2
  have hexact :=
    lemma79_holdList_firstEntryKey_firstPassageFixedTailExpectation_of_add_le
      (origin := origin) (entry := entry) (family := family)
      (C := C) (B := B) (p := p) (gap := gap) (J := J)
      hpC hroom G
  have htower :=
    lemma79_rawHoldFirstPassageFixedTailSplit_weightedExpectation_le
      J entry gap prefixWeight future D hfuture
  calc
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF B)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey origin family C)
          (some (p, entry.toPoint))).indicator
            (fun full =>
              let pair :=
                lemma79VerticalFirstPassageFixedTailSplit J entry gap
                  ((full.drop p).take (gap + 1 + J))
              prefixWeight pair.1 *
                future
                  (taoSection7RenewalPathPoint
                    entry pair.1 pair.1.length)
                  pair.2)) =
        (taoSection7HoldListPMF B).toOuterMeasure
            (lemma79KeyAtom Set.univ
              (lemma79HoldPathHeadKey origin family C)
              (some (p, entry.toPoint))) *
          lemma79PMFENNExpectation
            (lemma79RawHoldFirstPassageFixedTailSplitPMF
              (gap + 1 + J) J entry gap) G := by
      simpa [G] using hexact
    _ ≤ (taoSection7HoldListPMF B).toOuterMeasure
            (lemma79KeyAtom Set.univ
              (lemma79HoldPathHeadKey origin family C)
              (some (p, entry.toPoint))) *
          (D * lemma79PMFENNExpectation
            (lemma79RawHoldFirstPassagePrefixPMF J entry gap)
            prefixWeight) :=
      mul_le_mul_left' htower _

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
