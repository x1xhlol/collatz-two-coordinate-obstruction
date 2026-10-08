/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79PostExitFreshTail
import Erdos1135Predecessor.Tao.Renewal.Lemma79R2MasterAtom

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79VerticalFirstPassageCut_take_gap_add_one_add_eq_of_decoded
    (entry : TaoSection7RenewalPoint) (gap J : ℕ)
    (src : List (ℕ × List ℕ))
    (hroom : gap + 1 + J ≤ src.length) :
    lemma79VerticalFirstPassageCut entry gap
        ((lemma79DecodeHoldSourcePrefixes src).take (gap + 1 + J)) =
      lemma79VerticalFirstPassageCut entry gap
        ((lemma79DecodeHoldSourcePrefixes src).take (gap + 1)) := by
  have hshortRoom : gap + 1 ≤ (src.take (gap + 1 + J)).length := by
    simp only [List.length_take]
    rw [Nat.min_eq_left hroom]
    omega
  have hcut :=
    lemma79VerticalFirstPassageCut_take_gap_add_one_eq_of_decoded
      entry gap (src.take (gap + 1 + J)) hshortRoom
  simpa [lemma79DecodeHoldSourcePrefixes, List.map_take,
    List.take_take, Nat.min_eq_left (by omega : gap + 1 ≤ gap + 1 + J)]
    using hcut.symm

theorem lemma79VerticalFirstPassageCut_take_gap_add_one_add_eq_of_holdListPMF_ne_zero
    {B p : ℕ} (entry : TaoSection7RenewalPoint) (gap J : ℕ)
    {full : List TaoSection7RenewalPoint}
    (hfull : taoSection7HoldListPMF B full ≠ 0)
    (hroom : p + (gap + 1 + J) ≤ B) :
    lemma79VerticalFirstPassageCut entry gap
        ((full.drop p).take (gap + 1 + J)) =
      lemma79VerticalFirstPassageCut entry gap
        ((full.drop p).take (gap + 1)) := by
  rcases lemma79_exists_decodedHoldSource_of_holdListPMF_ne_zero hfull with
    ⟨src, hsrc, hdecode⟩
  have hsrcLen := lemma79_decodedHoldSource_length_of_ne_zero hsrc
  have hdecodeDrop :
      lemma79DecodeHoldSourcePrefixes (src.drop p) = full.drop p := by
    simpa [lemma79DecodeHoldSourcePrefixes, List.map_drop] using
      congrArg (List.drop p) hdecode
  have htailRoom : gap + 1 + J ≤ (src.drop p).length := by
    simp only [List.length_drop]
    rw [hsrcLen]
    omega
  simpa [hdecodeDrop] using
    (lemma79VerticalFirstPassageCut_take_gap_add_one_add_eq_of_decoded
      entry gap J (src.drop p) htailRoom)

theorem lemma79FirstPassageFixedTailData_of_holdListPMF_ne_zero
    {origin entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C B p gap J : ℕ} {full : List TaoSection7RenewalPoint}
    (old : TaoSection7Triangle)
    (hfull : taoSection7HoldListPMF B full ≠ 0)
    (hkey :
      lemma79BoundedInclusiveTraceHeadKey
          (lemma79HoldPathPointAt origin full) family C =
        some (p, entry.toPoint))
    (hentry : old.Mem entry.toPoint)
    (hgap : lemma79EntryVerticalGap old entry.toPoint = gap)
    (hroom : p + (gap + 1 + J) ≤ B) :
    let block := (full.drop p).take (gap + 1 + J)
    let K := lemma79VerticalFirstPassageCut entry gap block
    let pair :=
      lemma79VerticalFirstPassageFixedTailSplit J entry gap block
    Lemma79FirstExitCertificate
        (lemma79HoldPathPointAt origin full) old p (p + K) ∧
      taoSection7RenewalPathPoint entry pair.1 pair.1.length =
        taoSection7RenewalPathPoint origin full (p + K) ∧
      pair.2 = (full.drop (p + K)).take J ∧
      K ≤ gap + 1 := by
  dsimp only
  let short := (full.drop p).take (gap + 1)
  let block := (full.drop p).take (gap + 1 + J)
  let Kshort := lemma79VerticalFirstPassageCut entry gap short
  let K := lemma79VerticalFirstPassageCut entry gap block
  let pair := lemma79VerticalFirstPassageFixedTailSplit J entry gap block
  have hroomShort :
      p + lemma79EntryVerticalGap old entry.toPoint + 1 ≤ B := by
    rw [hgap]
    omega
  have hdata :
      Kshort = lemma79HoldFirstExitCut origin full p gap ∧
        Lemma79FirstExitCertificate
          (lemma79HoldPathPointAt origin full) old p (p + Kshort) ∧
        lemma77RenewalPointOfRelativeEndpoint entry
            (lemma77CanonicalStoppedEndpoint entry gap short) =
          taoSection7RenewalPathPoint origin full (p + Kshort) ∧
        Kshort ≤ gap + 1 := by
    simpa [short, Kshort, hgap] using
      (lemma79CanonicalFirstExitData_of_holdListPMF_ne_zero
        (family := family) (C := C) old hfull hkey hentry hroomShort)
  rcases hdata with ⟨_hrawCut, hexitShort, hendpointShort, hKshortLe⟩
  have hcut : K = Kshort := by
    dsimp [K, Kshort, block, short]
    exact
      lemma79VerticalFirstPassageCut_take_gap_add_one_add_eq_of_holdListPMF_ne_zero
        entry gap J hfull hroom
  have hexit :
      Lemma79FirstExitCertificate
        (lemma79HoldPathPointAt origin full) old p (p + K) := by
    simpa [hcut] using hexitShort
  have hrelative :
      lemma77RenewalPointOfRelativeEndpoint entry
          (lemma77EndpointOfPrefix entry pair.1) =
        taoSection7RenewalPathPoint origin full (p + K) := by
    have hKshortLong : Kshort ≤ gap + 1 + J :=
      hKshortLe.trans (Nat.le_add_right (gap + 1) J)
    simpa [pair, lemma79VerticalFirstPassageFixedTailSplit,
      block, K, short, Kshort, hcut, lemma77CanonicalStoppedEndpoint,
      List.take_take, Nat.min_eq_left hKshortLe,
      Nat.min_eq_left hKshortLong] using hendpointShort
  have hendpoint :
      taoSection7RenewalPathPoint entry pair.1 pair.1.length =
        taoSection7RenewalPathPoint origin full (p + K) := by
    exact
      (lemma77RenewalPointOfRelativeEndpoint_endpointOfPrefix
        entry pair.1).symm.trans hrelative
  have hKLe : K ≤ gap + 1 := hcut.trans_le hKshortLe
  have hfresh : pair.2 = (full.drop (p + K)).take J := by
    have hKRoom : K + J ≤ gap + 1 + J :=
      Nat.add_le_add_right hKLe J
    dsimp [pair, block, K]
    exact
      lemma79VerticalFirstPassageFixedTailSplit_snd_eq_global_drop
        p J (gap + 1 + J) entry gap full
          (by simpa [K, block] using hKRoom)
  exact ⟨hexit, hendpoint, hfresh, hKLe⟩

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
