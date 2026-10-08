import Erdos1135.Tao.Renewal.Lemma79FirstEntryEndpointLaw
import Erdos1135.Tao.Renewal.Lemma79R2Pointwise
import Erdos1135.Tao.Renewal.Lemma79ClockDeath

/-!
# Lemma 7.9 Killed R=2 Common-Master Atoms

This proof leaf recovers source provenance and first-exit data on nonzero atoms
of a longer iid Hold master.  Zero-mass lists are deliberately excluded before
using positivity of decoded Hold increments.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Regard a semantic Section 7 point as the corresponding renewal point. -/
def lemma79RenewalPointOfPoint
    (p : TaoSection7Point) : TaoSection7RenewalPoint :=
  { j := p.j, l := p.l }

@[simp] theorem lemma79RenewalPointOfPoint_toPoint
    (p : TaoSection7Point) :
    (lemma79RenewalPointOfPoint p).toPoint = p := by
  rfl

/-- Every nonzero iid Hold-list atom has a nonzero raw source-prefix preimage. -/
theorem lemma79_exists_decodedHoldSource_of_holdListPMF_ne_zero
    {B : ℕ} {full : List TaoSection7RenewalPoint}
    (hfull : taoSection7HoldListPMF B full ≠ 0) :
    ∃ src : List (ℕ × List ℕ),
      taoSection7HoldSourcePrefixListPMF B src ≠ 0 ∧
        lemma79DecodeHoldSourcePrefixes src = full := by
  have hmem : full ∈ (taoSection7HoldListPMF B).support := hfull
  rw [← taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq B] at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨src, hsrc, hdecode⟩
  exact ⟨src, hsrc, by
    simpa [lemma79DecodeHoldSourcePrefixes] using hdecode⟩

/-- A nonzero raw source-list atom has the declared master length. -/
theorem lemma79_decodedHoldSource_length_of_ne_zero
    {B : ℕ} {src : List (ℕ × List ℕ)}
    (hsrc : taoSection7HoldSourcePrefixListPMF B src ≠ 0) :
    src.length = B := by
  by_contra hne
  exact hsrc
    (taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
      B src hne)

/-- A present semantic key identifies the renewal path entry point. -/
theorem lemma79HoldPathHeadKey_entry_eq
    {origin : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p : ℕ} {entryPoint : TaoSection7Point}
    (hkey :
      lemma79BoundedInclusiveTraceHeadKey
          (lemma79HoldPathPointAt origin full) family C =
        some (p, entryPoint)) :
    (taoSection7RenewalPathPoint origin full p).toPoint = entryPoint := by
  exact (lemma79BoundedInclusiveTraceHeadKey_some_spec hkey).2.1.symm

/-- The renewal path entry equals the canonical renewal lift of its semantic
head-key point. -/
theorem lemma79HoldPathHeadKey_renewalEntry_eq
    {origin : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p : ℕ} {entryPoint : TaoSection7Point}
    (hkey :
      lemma79BoundedInclusiveTraceHeadKey
          (lemma79HoldPathPointAt origin full) family C =
        some (p, entryPoint)) :
    taoSection7RenewalPathPoint origin full p =
      lemma79RenewalPointOfPoint entryPoint := by
  apply TaoSection7RenewalPoint.toPoint_injective
  rw [lemma79HoldPathHeadKey_entry_eq hkey]
  exact lemma79RenewalPointOfPoint_toPoint entryPoint |>.symm

/-- On decoded Hold support, the canonical `gap+1` block has the same
first-passage cut as the complete suffix. -/
theorem lemma79VerticalFirstPassageCut_take_gap_add_one_eq_of_decoded
    (entry : TaoSection7RenewalPoint) (gap : ℕ)
    (src : List (ℕ × List ℕ))
    (hroom : gap + 1 ≤ src.length) :
    lemma79VerticalFirstPassageCut entry gap
        ((lemma79DecodeHoldSourcePrefixes src).take (gap + 1)) =
      lemma79VerticalFirstPassageCut entry gap
        (lemma79DecodeHoldSourcePrefixes src) := by
  let full := lemma79DecodeHoldSourcePrefixes src
  let K := lemma79VerticalFirstPassageCut entry gap full
  have hcert :=
    lemma79VerticalFirstPassagePrefix_take_cut_decode_and_le
      entry gap src hroom
  have hfirst :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        entry gap K (full.take K) := by
    simpa [full, K] using hcert.1
  change lemma79VerticalFirstPassageCut entry gap
      (full.take (gap + 1)) = K
  apply lemma79VerticalFirstPassageCut_eq_of_take_eq hfirst
  rw [List.take_take]
  rw [Nat.min_eq_left hcert.2]

/-- Decoded common-master support joins the canonical stopped endpoint to the
global first-exit certificate and original Hold path.

The white endpoint produced later from this adapter is an intervening path
point; this theorem does not make it a stopping transition.
-/
theorem lemma79CanonicalFirstExitData_of_decodedHoldSource
    (origin : TaoSection7RenewalPoint)
    (old : TaoSection7Triangle)
    (p : ℕ) (src : List (ℕ × List ℕ))
    (hentry : old.Mem
      (lemma79HoldPathPointAt origin
        (lemma79DecodeHoldSourcePrefixes src) p))
    (hroom :
      p + lemma79EntryVerticalGap old
          (lemma79HoldPathPointAt origin
            (lemma79DecodeHoldSourcePrefixes src) p) + 1 ≤ src.length) :
    let full := lemma79DecodeHoldSourcePrefixes src
    let entry := taoSection7RenewalPathPoint origin full p
    let gap := lemma79EntryVerticalGap old entry.toPoint
    let block := (full.drop p).take (gap + 1)
    let K := lemma79VerticalFirstPassageCut entry gap block
    Lemma79FirstExitCertificate
        (lemma79HoldPathPointAt origin full) old p (p + K) ∧
      lemma77RenewalPointOfRelativeEndpoint entry
          (lemma77CanonicalStoppedEndpoint entry gap block) =
        taoSection7RenewalPathPoint origin full (p + K) ∧
      K ≤ gap + 1 := by
  dsimp only
  let full := lemma79DecodeHoldSourcePrefixes src
  let entry := taoSection7RenewalPathPoint origin full p
  let gap := lemma79EntryVerticalGap old entry.toPoint
  let suffix := full.drop p
  let block := suffix.take (gap + 1)
  let Kfull := lemma79VerticalFirstPassageCut entry gap suffix
  let K := lemma79VerticalFirstPassageCut entry gap block
  have hp : p ≤ src.length := by omega
  have hdecodeDrop :
      lemma79DecodeHoldSourcePrefixes (src.drop p) = suffix := by
    simp [lemma79DecodeHoldSourcePrefixes, suffix, full, List.map_drop]
  have hgapRoom : gap + 1 ≤ (src.drop p).length := by
    simp only [List.length_drop]
    have hroom' : p + gap + 1 ≤ src.length := by
      simpa [gap, entry, full, lemma79HoldPathPointAt] using hroom
    omega
  have hcertBound :=
    lemma79VerticalFirstPassagePrefix_take_cut_decode_and_le
      entry gap (src.drop p) hgapRoom
  have hfirst :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        entry gap Kfull (suffix.take Kfull) := by
    simpa [hdecodeDrop, Kfull] using hcertBound.1
  have hKfullLe : Kfull ≤ gap + 1 := by
    simpa [hdecodeDrop, Kfull] using hcertBound.2
  have hcut : K = Kfull := by
    dsimp [K, block]
    calc
      lemma79VerticalFirstPassageCut entry gap
          (suffix.take (gap + 1)) =
          lemma79VerticalFirstPassageCut entry gap
            (lemma79DecodeHoldSourcePrefixes (src.drop p)) := by
              simpa [hdecodeDrop] using
                lemma79VerticalFirstPassageCut_take_gap_add_one_eq_of_decoded
                  entry gap (src.drop p) hgapRoom
      _ = Kfull := by rw [hdecodeDrop]
  have hexit :
      Lemma79FirstExitCertificate
        (lemma79HoldPathPointAt origin full) old p (p + K) := by
    have hdecoded :=
      lemma79FirstExitCertificate_of_decodedHoldSource
        origin old p src hentry hroom
    simpa [full, entry, gap, Kfull, suffix, lemma79HoldPathPointAt,
      lemma79HoldFirstExitCut, hcut] using hdecoded
  have hblockTake : block.take K = suffix.take K := by
    dsimp [block]
    rw [List.take_take]
    simp [Nat.min_eq_left (hcut.trans_le hKfullLe)]
  have hfirstK :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        entry gap K (suffix.take K) := by
    simpa [hcut] using hfirst
  have hendpoint :
      lemma77RenewalPointOfRelativeEndpoint entry
          (lemma77CanonicalStoppedEndpoint entry gap block) =
        taoSection7RenewalPathPoint origin full (p + K) := by
    unfold lemma77CanonicalStoppedEndpoint
    rw [show lemma79VerticalFirstPassageCut entry gap block = K by rfl]
    rw [hblockTake]
    calc
      lemma77RenewalPointOfRelativeEndpoint entry
          (lemma77EndpointOfPrefix entry (suffix.take K)) =
          taoSection7RenewalPathPoint entry
            (suffix.take K) (suffix.take K).length :=
        lemma77RenewalPointOfRelativeEndpoint_endpointOfPrefix
          entry (suffix.take K)
      _ = taoSection7RenewalPathPoint entry (suffix.take K) K := by
        rw [hfirstK.length_eq]
      _ = taoSection7RenewalPathPoint entry suffix K :=
        TaoSection7Lemma710.renewalPathPoint_take_eq_of_le
          entry suffix K K le_rfl
      _ = taoSection7RenewalPathPoint origin full (p + K) := by
        dsimp [entry, suffix]
        exact taoSection7RenewalPathPoint_drop_add origin full p K
  exact ⟨hexit, hendpoint, hcut.trans_le hKfullLe⟩

/-- A nonzero Hold-list atom inherits the canonical first-exit data from a
decoded raw source preimage.  The endpoint at `p + K` is the vertical
first-exit path point, not a new stopping transition. -/
theorem lemma79CanonicalFirstExitData_of_holdListPMF_ne_zero
    {origin entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C B p : ℕ} {full : List TaoSection7RenewalPoint}
    (old : TaoSection7Triangle)
    (hfull : taoSection7HoldListPMF B full ≠ 0)
    (hkey :
      lemma79BoundedInclusiveTraceHeadKey
          (lemma79HoldPathPointAt origin full) family C =
        some (p, entry.toPoint))
    (hentry : old.Mem entry.toPoint)
    (hroom :
      p + lemma79EntryVerticalGap old entry.toPoint + 1 ≤ B) :
    let gap := lemma79EntryVerticalGap old entry.toPoint
    let block := (full.drop p).take (gap + 1)
    let K := lemma79VerticalFirstPassageCut entry gap block
    K = lemma79HoldFirstExitCut origin full p gap ∧
      Lemma79FirstExitCertificate
        (lemma79HoldPathPointAt origin full) old p (p + K) ∧
      lemma77RenewalPointOfRelativeEndpoint entry
          (lemma77CanonicalStoppedEndpoint entry gap block) =
        taoSection7RenewalPathPoint origin full (p + K) ∧
      K ≤ gap + 1 := by
  dsimp only
  rcases lemma79_exists_decodedHoldSource_of_holdListPMF_ne_zero hfull with
    ⟨src, hsrc, hdecode⟩
  have hsrcLen := lemma79_decodedHoldSource_length_of_ne_zero hsrc
  have hentryEq :
      taoSection7RenewalPathPoint origin full p = entry :=
    TaoSection7RenewalPoint.toPoint_injective
      (lemma79HoldPathHeadKey_entry_eq hkey)
  have hentrySrc : old.Mem
      (lemma79HoldPathPointAt origin
        (lemma79DecodeHoldSourcePrefixes src) p) := by
    rw [hdecode]
    simpa [lemma79HoldPathPointAt, hentryEq] using hentry
  have hroomSrc :
      p + lemma79EntryVerticalGap old
          (lemma79HoldPathPointAt origin
            (lemma79DecodeHoldSourcePrefixes src) p) + 1 ≤ src.length := by
    rw [hdecode, hsrcLen]
    simpa [lemma79HoldPathPointAt, hentryEq] using hroom
  let gap := lemma79EntryVerticalGap old entry.toPoint
  let block := (full.drop p).take (gap + 1)
  let K := lemma79VerticalFirstPassageCut entry gap block
  have hdropRoom : gap + 1 ≤ (src.drop p).length := by
    simp only [List.length_drop]
    omega
  have hdecodeDrop :
      lemma79DecodeHoldSourcePrefixes (src.drop p) = full.drop p := by
    simpa [lemma79DecodeHoldSourcePrefixes, List.map_drop] using
      congrArg (List.drop p) hdecode
  have hcutLocal :=
    lemma79VerticalFirstPassageCut_take_gap_add_one_eq_of_decoded
      entry gap (src.drop p) hdropRoom
  have hK :
      K = lemma79HoldFirstExitCut origin full p gap := by
    simpa [K, block, lemma79HoldFirstExitCut, hentryEq, hdecodeDrop]
      using hcutLocal
  have hdata :=
    lemma79CanonicalFirstExitData_of_decodedHoldSource
      origin old p src hentrySrc hroomSrc
  have hdata' :
      Lemma79FirstExitCertificate
          (lemma79HoldPathPointAt origin full) old p (p + K) ∧
        lemma77RenewalPointOfRelativeEndpoint entry
            (lemma77CanonicalStoppedEndpoint entry gap block) =
          taoSection7RenewalPathPoint origin full (p + K) ∧
        K ≤ gap + 1 := by
    simpa [hdecode, hentryEq, gap, block, K] using hdata
  exact ⟨hK, hdata'⟩

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
