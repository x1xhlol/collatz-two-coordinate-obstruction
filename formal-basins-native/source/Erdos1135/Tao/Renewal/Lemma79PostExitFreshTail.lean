import Erdos1135.Tao.Renewal.Lemma79FirstEntryFiberLaw
import Erdos1135.Tao.Renewal.Lemma79R2Aggregation

/-!
# Lemma 7.9 Post-Exit Fresh Hold Tail

This proof leaf joins one complete semantic first-entry key to the raw
first-passage stopped-prefix/fresh-tail law.  The fresh coordinate starts after
the vertical first-exit increment; that exit is not asserted to be a stopping
transition.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The raw-source fixed-tail split is exactly the corresponding map of the
decoded iid Hold-list law. -/
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

/-- Exact nested iid law of the fixed first-entry prefix, the variable
canonical stopped prefix, and the first `J` increments after the realized
global exit clock `p + K`. -/
theorem lemma79_holdList_map_firstEntryPrefix_canonicalSplit_freshBlock
    (p J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    (taoSection7HoldListPMF (p + (gap + 1 + J))).map
        (fun full =>
          let u := full.drop p
          let K := lemma79VerticalFirstPassageCut entry gap u
          (full.take p,
            (u.take K, (full.drop (p + K)).take J))) =
      (taoSection7HoldListPMF p).bind fun keyPre =>
        (lemma77CanonicalFirstPassagePrefixPMF entry gap).bind fun stopped =>
          (taoSection7HoldListPMF J).map fun fresh =>
            (keyPre, (stopped, fresh)) := by
  let N := gap + 1 + J
  let outer : List TaoSection7RenewalPoint ->
      List TaoSection7RenewalPoint × List TaoSection7RenewalPoint :=
    fun full => (full.take p, full.drop p)
  let inner :
      List TaoSection7RenewalPoint × List TaoSection7RenewalPoint ->
        List TaoSection7RenewalPoint ×
          (List TaoSection7RenewalPoint × List TaoSection7RenewalPoint) :=
    fun pair =>
      (pair.1,
        lemma79VerticalFirstPassageFixedTailSplit J entry gap pair.2)
  let textual : List TaoSection7RenewalPoint ->
      List TaoSection7RenewalPoint ×
        (List TaoSection7RenewalPoint × List TaoSection7RenewalPoint) :=
    fun full =>
      let u := full.drop p
      let K := lemma79VerticalFirstPassageCut entry gap u
      (full.take p, (u.take K, (full.drop (p + K)).take J))
  have htext : textual = inner ∘ outer := by
    funext full
    simp [textual, inner, outer,
      lemma79VerticalFirstPassageFixedTailSplit, Function.comp_apply,
      List.drop_drop]
  calc
    (taoSection7HoldListPMF (p + (gap + 1 + J))).map textual =
        (taoSection7HoldListPMF (p + N)).map (inner ∘ outer) := by
      rw [htext]
    _ = ((taoSection7HoldListPMF (p + N)).map outer).map inner := by
      rw [PMF.map_comp]
    _ = ((taoSection7HoldListPMF p).bind fun keyPre =>
          (taoSection7HoldListPMF N).map fun block =>
            (keyPre, block)).map inner := by
      rw [show
        (taoSection7HoldListPMF (p + N)).map outer =
          (taoSection7HoldListPMF p).bind fun keyPre =>
            (taoSection7HoldListPMF N).map fun block =>
              (keyPre, block) by
        simpa [outer] using taoSection7HoldListPMF_map_take_drop_eq p N]
    _ = (taoSection7HoldListPMF p).bind fun keyPre =>
          ((taoSection7HoldListPMF N).map
            (lemma79VerticalFirstPassageFixedTailSplit J entry gap)).map
              fun pair => (keyPre, pair) := by
      rw [PMF.map_bind]
      congr
      funext keyPre
      rw [PMF.map_comp, PMF.map_comp]
      apply congrArg (fun f => (taoSection7HoldListPMF N).map f)
      funext block
      rfl
    _ = (taoSection7HoldListPMF p).bind fun keyPre =>
          (lemma79RawHoldFirstPassageFixedTailSplitPMF
            N J entry gap).map fun pair => (keyPre, pair) := by
      rw [lemma79RawHoldFirstPassageFixedTailSplitPMF_eq_holdList_map]
    _ = (taoSection7HoldListPMF p).bind fun keyPre =>
          ((lemma79RawHoldFirstPassagePrefixPMF J entry gap).bind fun stopped =>
            (taoSection7HoldListPMF J).map fun fresh =>
              (stopped, fresh)).map fun pair => (keyPre, pair) := by
      rw [lemma79_rawHoldFirstPassageFixedTailSplitPMF_eq_bind]
    _ = (taoSection7HoldListPMF p).bind fun keyPre =>
          ((lemma77CanonicalFirstPassagePrefixPMF entry gap).bind fun stopped =>
            (taoSection7HoldListPMF J).map fun fresh =>
              (stopped, fresh)).map fun pair => (keyPre, pair) := by
      rw [lemma79_rawHoldFirstPassagePrefixPMF_eq_canonical]
    _ = (taoSection7HoldListPMF p).bind fun keyPre =>
          (lemma77CanonicalFirstPassagePrefixPMF entry gap).bind fun stopped =>
            (taoSection7HoldListPMF J).map fun fresh =>
              (keyPre, (stopped, fresh)) := by
      congr
      funext keyPre
      rw [PMF.map_bind]
      congr
      funext stopped
      rw [PMF.map_comp]
      apply congrArg (fun f => (taoSection7HoldListPMF J).map f)
      funext fresh
      rfl

/-- The second coordinate of the bounded first-passage split is textually the
first `J` Hold increments after the global clock `p + K`. -/
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

/-- Exact native expectation factorization of one semantic first-entry key,
its variable first-passage prefix, and the following fresh length-`J` Hold
block inside an arbitrary longer iid master. -/
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

/-- Semantic first-entry form of the countable stopped-prefix/fresh-tail
tower.  A uniform future bound is integrated over every exact first-passage
prefix without conditioning on the semantic key. -/
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
end Erdos1135
