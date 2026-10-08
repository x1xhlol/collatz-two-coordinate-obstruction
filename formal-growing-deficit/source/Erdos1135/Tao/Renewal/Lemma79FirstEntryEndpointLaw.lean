import Erdos1135.Tao.Renewal.Lemma79FirstEntryFiberLaw
import Erdos1135.Tao.Renewal.CanonicalFirstPassageExpMoment

/-!
# Lemma 7.9 First-Entry Canonical Endpoint Law

This proof leaf specializes the countable first-entry fiber product law to the
canonical first-passage endpoint map.  Both the joint event and its first-entry
factor are unnormalized masses in `ENNReal`.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Exact canonical endpoint law on one complete semantic first-entry fiber.

The master contains exactly the `p` past increments followed by the
`gap+1` increments used by the canonical first-passage endpoint.
-/
theorem lemma79_holdList_firstEntryKey_canonicalEndpoint_jointMass_exact
    {origin entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p gap : ℕ}
    (hpC : p < C)
    (S : Set (ℕ × ℤ)) :
    (taoSection7HoldListPMF (p + (gap + 1))).toOuterMeasure
        {full |
          lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt origin full) family C =
              some (p, entry.toPoint) ∧
            lemma77CanonicalStoppedEndpoint entry gap (full.drop p) ∈ S} =
      (taoSection7HoldListPMF (p + (gap + 1))).toOuterMeasure
          {full |
            lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt origin full) family C =
              some (p, entry.toPoint)} *
        (lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure S := by
  let EndpointEvent : Set (List TaoSection7RenewalPoint) :=
    (lemma77CanonicalStoppedEndpoint entry gap) ⁻¹' S
  have hfactor :=
    lemma79_holdList_firstEntryKey_freshTail_jointMass_eq_keyMass_mul
      (start := origin) (family := family) (C := C)
      (p := p) (entry := entry.toPoint) hpC (gap + 1) EndpointEvent
  have hendpoint :
      (taoSection7HoldListPMF (gap + 1)).toOuterMeasure EndpointEvent =
        (lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure S := by
    calc
      _ = ((taoSection7HoldListPMF (gap + 1)).map
            (lemma77CanonicalStoppedEndpoint entry gap)).toOuterMeasure S :=
        (PMF.toOuterMeasure_map_apply
          (lemma77CanonicalStoppedEndpoint entry gap)
          (taoSection7HoldListPMF (gap + 1)) S).symm
      _ = _ := by
        rw [← lemma77CanonicalFirstPassageEndpointPMF_eq_holdList_map]
  simpa [EndpointEvent, hendpoint] using hfactor

/-- Exact canonical endpoint law on one complete semantic first-entry fiber
inside an arbitrary longer Hold master.

Only the explicit room inequality is required; no global master-size schedule
or positive atom-mass premise is used.
-/
theorem lemma79_holdList_firstEntryKey_canonicalEndpoint_jointMass
    {origin entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C B p gap : ℕ}
    (hpC : p < C)
    (hroom : p + (gap + 1) ≤ B)
    (S : Set (ℕ × ℤ)) :
    (taoSection7HoldListPMF B).toOuterMeasure
        {full |
          lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt origin full) family C =
              some (p, entry.toPoint) ∧
            lemma77CanonicalStoppedEndpoint entry gap
                ((full.drop p).take (gap + 1)) ∈ S} =
      (taoSection7HoldListPMF B).toOuterMeasure
          {full |
            lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt origin full) family C =
              some (p, entry.toPoint)} *
        (lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure S := by
  let EndpointEvent : Set (List TaoSection7RenewalPoint) :=
    (lemma77CanonicalStoppedEndpoint entry gap) ⁻¹' S
  have hfactor :=
    lemma79_holdList_firstEntryKey_freshBlock_jointMass_eq_keyMass_mul
      (start := origin) (family := family) (C := C)
      (p := p) (N := gap + 1) (B := B) (entry := entry.toPoint)
      hpC hroom EndpointEvent
  have hendpoint :
      (taoSection7HoldListPMF (gap + 1)).toOuterMeasure EndpointEvent =
        (lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure S := by
    calc
      _ = ((taoSection7HoldListPMF (gap + 1)).map
            (lemma77CanonicalStoppedEndpoint entry gap)).toOuterMeasure S :=
        (PMF.toOuterMeasure_map_apply
          (lemma77CanonicalStoppedEndpoint entry gap)
          (taoSection7HoldListPMF (gap + 1)) S).symm
      _ = _ := by
        rw [← lemma77CanonicalFirstPassageEndpointPMF_eq_holdList_map]
  simpa [EndpointEvent, hendpoint] using hfactor

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
