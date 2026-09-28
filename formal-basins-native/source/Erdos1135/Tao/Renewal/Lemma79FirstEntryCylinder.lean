import Erdos1135.Tao.Renewal.Lemma79CutoffLocality

/-!
# Lemma 7.9 First-Entry Cylinder

This proof leaf shows that an exact first-entry key is determined by the Hold
prefix through its entry time.  It is the past-measurability input needed to
turn the countable semantic key partition into prefix cylinders before applying
the iid Hold take/drop law.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A present first-entry key at time `p` is determined by exactly the first
`p` Hold increments.

The statement includes `p = 0`: then the retained prefix is empty and the
time-zero path point is still the original start.
-/
theorem lemma79HoldPath_firstEntryKey_eq_some_iff_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p : ℕ} {entry : TaoSection7Point}
    (hpC : p < C) :
    lemma79BoundedInclusiveTraceHeadKey
        (lemma79HoldPathPointAt start full) family C =
          some (p, entry) ↔
      lemma79BoundedInclusiveTraceHeadKey
        (lemma79HoldPathPointAt start (full.take p)) family (p + 1) =
          some (p, entry) := by
  have hpath (q : ℕ) (hq : q ≤ p) :
      lemma79HoldPathPointAt start (full.take p) q =
        lemma79HoldPathPointAt start full q :=
    lemma79HoldPathPointAt_take_eq_of_le start full hq
  constructor
  · intro hkey
    have hspec :=
      lemma79BoundedInclusiveTraceHeadKey_some_spec hkey
    have hfirstTake :
        Lemma79FirstTriangleHitFromZero
          (lemma79HoldPathPointAt start (full.take p)) family p :=
      hspec.2.2.congr_of_eq_on_lt (H := p + 1) (by omega)
        (fun q hq => (hpath q (by omega)).symm)
    have hkeyTake :=
      lemma79BoundedInclusiveTraceHeadKey_eq_some_of_first_hit
        (pointAt := lemma79HoldPathPointAt start (full.take p))
        (family := family) (H := p + 1) (first := p)
        (by omega) hfirstTake
    have hentry :
        lemma79HoldPathPointAt start (full.take p) p = entry :=
      (hpath p le_rfl).trans hspec.2.1.symm
    simpa [hentry] using hkeyTake
  · intro hkey
    have hspec :=
      lemma79BoundedInclusiveTraceHeadKey_some_spec hkey
    have hfirstFull :
        Lemma79FirstTriangleHitFromZero
          (lemma79HoldPathPointAt start full) family p :=
      hspec.2.2.congr_of_eq_on_lt (H := p + 1) (by omega)
        (fun q hq => hpath q (by omega))
    have hkeyFull :=
      lemma79BoundedInclusiveTraceHeadKey_eq_some_of_first_hit
        (pointAt := lemma79HoldPathPointAt start full)
        (family := family) (H := C) (first := p)
        hpC hfirstFull
    have hentry :
        lemma79HoldPathPointAt start full p = entry :=
      (hpath p le_rfl).symm.trans hspec.2.1.symm
    simpa [hentry] using hkeyFull

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
