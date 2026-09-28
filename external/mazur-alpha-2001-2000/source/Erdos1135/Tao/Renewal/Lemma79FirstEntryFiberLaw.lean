import Erdos1135.Tao.Renewal.Lemma79TailExpectationCore
import Erdos1135.Tao.Renewal.Lemma79FirstEntryCylinder

/-!
# Lemma 7.9 Countable First-Entry Fiber Law

This proof leaf turns a semantic first-entry key into an exact Hold-prefix
cylinder and applies iid take/drop independence.  The resulting identities are
unnormalized and native in `ENNReal`; no conditional PMF, division by an atom
mass, or finite sample-space assumption is used.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Prefix-cylinder event representing one exact semantic first-entry key. -/
noncomputable def lemma79FirstEntryKeyPrefixEvent
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (p : ℕ) (entry : TaoSection7Point) :
    Set (List TaoSection7RenewalPoint) :=
  {pre |
    lemma79BoundedInclusiveTraceHeadKey
        (lemma79HoldPathPointAt start pre) family (p + 1) =
      some (p, entry)}

/-- Prefix/fresh-block iid split inside an arbitrary longer Hold master. -/
theorem lemma79_holdList_map_take_dropTake_eq_of_add_le
    {p N B : ℕ} (hroom : p + N ≤ B) :
    (taoSection7HoldListPMF B).map
        (fun full => (full.take p, (full.drop p).take N)) =
      (taoSection7HoldListPMF p).bind fun pre =>
        (taoSection7HoldListPMF N).map fun tail => (pre, tail) := by
  calc
    (taoSection7HoldListPMF B).map
        (fun full => (full.take p, (full.drop p).take N)) =
      ((taoSection7HoldListPMF B).map
          (fun full => full.take (p + N))).map
        (fun short => (short.take p, short.drop p)) := by
          rw [PMF.map_comp]
          apply congrArg (fun f => (taoSection7HoldListPMF B).map f)
          funext full
          apply Prod.ext
          · simp [Function.comp_apply, List.take_take]
          · exact List.take_drop
    _ = (taoSection7HoldListPMF (p + N)).map
        (fun short => (short.take p, short.drop p)) := by
          rw [taoSection7HoldListPMF_map_take_eq_of_le hroom]
    _ = _ := taoSection7HoldListPMF_map_take_drop_eq p N

/-- First-entry-cylinder/fresh-block expectation factorization inside an
arbitrary longer Hold master. -/
theorem lemma79_holdList_firstEntryKey_freshBlockExpectation_of_add_le
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p N B : ℕ} {entry : TaoSection7Point}
    (hpC : p < C) (hroom : p + N ≤ B)
    (future : List TaoSection7RenewalPoint -> ENNReal) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF B)
        (fun full =>
          {xs |
            lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt start xs) family C =
              some (p, entry)}.indicator
            (fun xs => future ((xs.drop p).take N)) full) =
      (taoSection7HoldListPMF p).toOuterMeasure
          (lemma79FirstEntryKeyPrefixEvent start family p entry) *
        lemma79PMFENNExpectation (taoSection7HoldListPMF N) future := by
  classical
  let FullEvent : Set (List TaoSection7RenewalPoint) :=
    {xs |
      lemma79BoundedInclusiveTraceHeadKey
          (lemma79HoldPathPointAt start xs) family C =
        some (p, entry)}
  let PrefixEvent :=
    lemma79FirstEntryKeyPrefixEvent start family p entry
  let split :
      List TaoSection7RenewalPoint ->
        List TaoSection7RenewalPoint × List TaoSection7RenewalPoint :=
    fun full => (full.take p, (full.drop p).take N)
  let prefixWeight : List TaoSection7RenewalPoint -> ENNReal :=
    PrefixEvent.indicator fun _ => 1
  let G :
      List TaoSection7RenewalPoint × List TaoSection7RenewalPoint -> ENNReal :=
    fun pair => prefixWeight pair.1 * future pair.2
  have hfunction :
      (fun full =>
        FullEvent.indicator
          (fun xs => future ((xs.drop p).take N)) full) =
        G ∘ split := by
    funext full
    have hiff :
        full ∈ FullEvent ↔ full.take p ∈ PrefixEvent := by
      simpa [FullEvent, PrefixEvent, lemma79FirstEntryKeyPrefixEvent] using
        (lemma79HoldPath_firstEntryKey_eq_some_iff_take
          (start := start) (full := full) (family := family)
          (C := C) (p := p) (entry := entry) hpC)
    by_cases hfull : full ∈ FullEvent
    · have hpre : full.take p ∈ PrefixEvent := hiff.mp hfull
      simp [G, split, prefixWeight, Set.indicator,
        Function.comp_apply, hfull, hpre]
    · have hpre : full.take p ∉ PrefixEvent :=
        fun h => hfull (hiff.mpr h)
      simp [G, split, prefixWeight, Set.indicator,
        Function.comp_apply, hfull, hpre]
  change lemma79PMFENNExpectation
      (taoSection7HoldListPMF B)
      (fun full =>
        FullEvent.indicator
          (fun xs => future ((xs.drop p).take N)) full) =
    (taoSection7HoldListPMF p).toOuterMeasure PrefixEvent *
      lemma79PMFENNExpectation (taoSection7HoldListPMF N) future
  rw [hfunction]
  calc
    lemma79PMFENNExpectation (taoSection7HoldListPMF B) (G ∘ split) =
        lemma79PMFENNExpectation
          ((taoSection7HoldListPMF B).map split) G :=
      (lemma79PMFENNExpectation_map
        (taoSection7HoldListPMF B) split G).symm
    _ = lemma79PMFENNExpectation
        ((taoSection7HoldListPMF p).bind fun pre =>
          (taoSection7HoldListPMF N).map fun tail => (pre, tail)) G := by
      rw [lemma79_holdList_map_take_dropTake_eq_of_add_le hroom]
    _ = ∑' pre, taoSection7HoldListPMF p pre *
        (prefixWeight pre *
          ∑' tail, taoSection7HoldListPMF N tail * future tail) := by
      simpa [G] using
        (lemma79_pmfENNExpectation_bind_pair_prefix_mul
          (taoSection7HoldListPMF p) (taoSection7HoldListPMF N)
          prefixWeight (fun _ tail => future tail))
    _ = lemma79PMFENNExpectation
        (taoSection7HoldListPMF p)
        (fun pre =>
          prefixWeight pre *
            lemma79PMFENNExpectation
              (taoSection7HoldListPMF N) future) := by
      rfl
    _ = lemma79PMFENNExpectation
          (taoSection7HoldListPMF p) prefixWeight *
        lemma79PMFENNExpectation (taoSection7HoldListPMF N) future :=
      lemma79PMFENNExpectation_mul_const
        (taoSection7HoldListPMF p) prefixWeight
        (lemma79PMFENNExpectation (taoSection7HoldListPMF N) future)
    _ = _ := by
      rw [lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure]

/-- Unnormalized joint mass of a semantic first-entry key and a fixed-length
fresh block event inside an arbitrary longer master. -/
theorem lemma79_holdList_firstEntryKey_freshBlock_jointMass_of_add_le
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p N B : ℕ} {entry : TaoSection7Point}
    (hpC : p < C) (hroom : p + N ≤ B)
    (TailEvent : Set (List TaoSection7RenewalPoint)) :
    (taoSection7HoldListPMF B).toOuterMeasure
        {full |
          lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt start full) family C =
              some (p, entry) ∧
            (full.drop p).take N ∈ TailEvent} =
      (taoSection7HoldListPMF p).toOuterMeasure
          (lemma79FirstEntryKeyPrefixEvent start family p entry) *
        (taoSection7HoldListPMF N).toOuterMeasure TailEvent := by
  classical
  let FullEvent : Set (List TaoSection7RenewalPoint) :=
    {xs |
      lemma79BoundedInclusiveTraceHeadKey
          (lemma79HoldPathPointAt start xs) family C =
        some (p, entry)}
  let JointEvent : Set (List TaoSection7RenewalPoint) :=
    {full | full ∈ FullEvent ∧ (full.drop p).take N ∈ TailEvent}
  let tailIndicator : List TaoSection7RenewalPoint -> ENNReal :=
    TailEvent.indicator fun _ => 1
  have hfactor :=
    lemma79_holdList_firstEntryKey_freshBlockExpectation_of_add_le
      (start := start) (family := family) (C := C)
      (p := p) (N := N) (B := B) (entry := entry)
      hpC hroom tailIndicator
  have hleft :
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF B)
          (fun full =>
            FullEvent.indicator
              (fun xs => tailIndicator ((xs.drop p).take N)) full) =
        (taoSection7HoldListPMF B).toOuterMeasure JointEvent := by
    calc
      _ = lemma79PMFENNExpectation
          (taoSection7HoldListPMF B)
          (JointEvent.indicator fun _ => 1) := by
            apply congrArg
              (lemma79PMFENNExpectation (taoSection7HoldListPMF B))
            funext full
            by_cases hfull : full ∈ FullEvent <;>
              by_cases htail : (full.drop p).take N ∈ TailEvent <;>
                simp [JointEvent, tailIndicator,
                  Set.indicator, hfull, htail]
      _ = _ :=
        lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure
          (taoSection7HoldListPMF B) JointEvent
  have hright :
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF N) tailIndicator =
        (taoSection7HoldListPMF N).toOuterMeasure TailEvent :=
    lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure
      (taoSection7HoldListPMF N) TailEvent
  change (taoSection7HoldListPMF B).toOuterMeasure JointEvent =
    (taoSection7HoldListPMF p).toOuterMeasure
        (lemma79FirstEntryKeyPrefixEvent start family p entry) *
      (taoSection7HoldListPMF N).toOuterMeasure TailEvent
  rw [← hleft, ← hright]
  simpa [FullEvent, tailIndicator] using hfactor

/-- Under a longer master, the semantic key mass still equals its exact prefix
cylinder mass. -/
theorem lemma79_holdList_firstEntryKey_mass_eq_prefixMass_of_add_le
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p N B : ℕ} {entry : TaoSection7Point}
    (hpC : p < C) (hroom : p + N ≤ B) :
    (taoSection7HoldListPMF B).toOuterMeasure
        {full |
          lemma79BoundedInclusiveTraceHeadKey
              (lemma79HoldPathPointAt start full) family C =
            some (p, entry)} =
      (taoSection7HoldListPMF p).toOuterMeasure
        (lemma79FirstEntryKeyPrefixEvent start family p entry) := by
  have h :=
    lemma79_holdList_firstEntryKey_freshBlock_jointMass_of_add_le
      (start := start) (family := family) (C := C)
      (p := p) (N := N) (B := B) (entry := entry)
      hpC hroom Set.univ
  have huniv :
      (taoSection7HoldListPMF N).toOuterMeasure Set.univ = 1 :=
    ((taoSection7HoldListPMF N).toOuterMeasure_apply_eq_one_iff Set.univ).2
      (Set.subset_univ _)
  rw [huniv, mul_one] at h
  simpa using h

/-- Source-facing arbitrary-master first-entry/fresh-block product law, with
the complete semantic key mass as its first factor. -/
theorem lemma79_holdList_firstEntryKey_freshBlock_jointMass_eq_keyMass_mul
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p N B : ℕ} {entry : TaoSection7Point}
    (hpC : p < C) (hroom : p + N ≤ B)
    (TailEvent : Set (List TaoSection7RenewalPoint)) :
    (taoSection7HoldListPMF B).toOuterMeasure
        {full |
          lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt start full) family C =
              some (p, entry) ∧
            (full.drop p).take N ∈ TailEvent} =
      (taoSection7HoldListPMF B).toOuterMeasure
          {full |
            lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt start full) family C =
              some (p, entry)} *
        (taoSection7HoldListPMF N).toOuterMeasure TailEvent := by
  calc
    _ = (taoSection7HoldListPMF p).toOuterMeasure
          (lemma79FirstEntryKeyPrefixEvent start family p entry) *
        (taoSection7HoldListPMF N).toOuterMeasure TailEvent :=
      lemma79_holdList_firstEntryKey_freshBlock_jointMass_of_add_le
        (start := start) (family := family) (C := C)
        (p := p) (N := N) (B := B) (entry := entry)
        hpC hroom TailEvent
    _ = _ := by
      rw [← lemma79_holdList_firstEntryKey_mass_eq_prefixMass_of_add_le
        (start := start) (family := family) (C := C)
        (p := p) (N := N) (B := B) (entry := entry) hpC hroom]

/-- Division-free first-entry-cylinder/fresh-future expectation factorization.

The complete first-entry fiber at horizon `C` is determined by `full.take p`;
the remaining `N` Hold increments retain their original iid law.
-/
theorem lemma79_holdList_firstEntryKey_freshFutureExpectation
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p : ℕ} {entry : TaoSection7Point}
    (hpC : p < C)
    (N : ℕ) (future : List TaoSection7RenewalPoint -> ENNReal) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF (p + N))
        (fun full =>
          {xs |
            lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt start xs) family C =
              some (p, entry)}.indicator
            (fun xs => future (xs.drop p)) full) =
      (taoSection7HoldListPMF p).toOuterMeasure
          (lemma79FirstEntryKeyPrefixEvent start family p entry) *
        lemma79PMFENNExpectation (taoSection7HoldListPMF N) future := by
  classical
  let FullEvent : Set (List TaoSection7RenewalPoint) :=
    {xs |
      lemma79BoundedInclusiveTraceHeadKey
          (lemma79HoldPathPointAt start xs) family C =
        some (p, entry)}
  let PrefixEvent :=
    lemma79FirstEntryKeyPrefixEvent start family p entry
  have hfunction :
      (fun full =>
        FullEvent.indicator (fun xs => future (xs.drop p)) full) =
      (fun full =>
        PrefixEvent.indicator (fun _ => future (full.drop p))
          (full.take p)) := by
    funext full
    have hiff :
        full ∈ FullEvent ↔ full.take p ∈ PrefixEvent := by
      simpa [FullEvent, PrefixEvent, lemma79FirstEntryKeyPrefixEvent] using
        (lemma79HoldPath_firstEntryKey_eq_some_iff_take
          (start := start) (full := full) (family := family)
          (C := C) (p := p) (entry := entry) hpC)
    by_cases hfull : full ∈ FullEvent
    · have hpre : full.take p ∈ PrefixEvent := hiff.mp hfull
      simp [Set.indicator, hfull, hpre]
    · have hpre : full.take p ∉ PrefixEvent :=
        fun h => hfull (hiff.mpr h)
      simp [Set.indicator, hfull, hpre]
  change lemma79PMFENNExpectation
      (taoSection7HoldListPMF (p + N))
      (fun full =>
        FullEvent.indicator (fun xs => future (xs.drop p)) full) =
    (taoSection7HoldListPMF p).toOuterMeasure PrefixEvent *
      lemma79PMFENNExpectation (taoSection7HoldListPMF N) future
  rw [hfunction]
  exact
    lemma79_holdList_prefixEvent_freshFutureExpectation_eq_outerMeasure
      p N PrefixEvent future

/-- Exact unnormalized joint mass of one first-entry key and one fresh-tail
event.  This is the countable source-law form used by the repaired `R=2`
aggregation.
-/
theorem lemma79_holdList_firstEntryKey_freshTail_jointMass
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p : ℕ} {entry : TaoSection7Point}
    (hpC : p < C)
    (N : ℕ) (TailEvent : Set (List TaoSection7RenewalPoint)) :
    (taoSection7HoldListPMF (p + N)).toOuterMeasure
        {full |
          lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt start full) family C =
              some (p, entry) ∧
            full.drop p ∈ TailEvent} =
      (taoSection7HoldListPMF p).toOuterMeasure
          (lemma79FirstEntryKeyPrefixEvent start family p entry) *
        (taoSection7HoldListPMF N).toOuterMeasure TailEvent := by
  classical
  let FullEvent : Set (List TaoSection7RenewalPoint) :=
    {xs |
      lemma79BoundedInclusiveTraceHeadKey
          (lemma79HoldPathPointAt start xs) family C =
        some (p, entry)}
  let JointEvent : Set (List TaoSection7RenewalPoint) :=
    {full | full ∈ FullEvent ∧ full.drop p ∈ TailEvent}
  let tailIndicator : List TaoSection7RenewalPoint -> ENNReal :=
    TailEvent.indicator fun _ => 1
  have hfactor :=
    lemma79_holdList_firstEntryKey_freshFutureExpectation
      (start := start) (family := family) (C := C)
      (p := p) (entry := entry) hpC N tailIndicator
  have hleft :
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF (p + N))
          (fun full =>
            FullEvent.indicator
              (fun xs => tailIndicator (xs.drop p)) full) =
        (taoSection7HoldListPMF (p + N)).toOuterMeasure JointEvent := by
    calc
      _ = lemma79PMFENNExpectation
          (taoSection7HoldListPMF (p + N))
          (JointEvent.indicator fun _ => 1) := by
            apply congrArg
              (lemma79PMFENNExpectation
                (taoSection7HoldListPMF (p + N)))
            funext full
            by_cases hfull : full ∈ FullEvent <;>
              by_cases htail : full.drop p ∈ TailEvent <;>
                simp [JointEvent, tailIndicator,
                  Set.indicator, hfull, htail]
      _ = _ :=
        lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure
          (taoSection7HoldListPMF (p + N)) JointEvent
  have hright :
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF N) tailIndicator =
        (taoSection7HoldListPMF N).toOuterMeasure TailEvent := by
    exact lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure
      (taoSection7HoldListPMF N) TailEvent
  change (taoSection7HoldListPMF (p + N)).toOuterMeasure JointEvent =
    (taoSection7HoldListPMF p).toOuterMeasure
        (lemma79FirstEntryKeyPrefixEvent start family p entry) *
      (taoSection7HoldListPMF N).toOuterMeasure TailEvent
  rw [← hleft, ← hright]
  simpa [FullEvent, tailIndicator] using hfactor

/-- The mass of a complete semantic first-entry fiber equals the mass of its
exact prefix cylinder. -/
theorem lemma79_holdList_firstEntryKey_mass_eq_prefixMass
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p : ℕ} {entry : TaoSection7Point}
    (hpC : p < C) (N : ℕ) :
    (taoSection7HoldListPMF (p + N)).toOuterMeasure
        {full |
          lemma79BoundedInclusiveTraceHeadKey
              (lemma79HoldPathPointAt start full) family C =
            some (p, entry)} =
      (taoSection7HoldListPMF p).toOuterMeasure
        (lemma79FirstEntryKeyPrefixEvent start family p entry) := by
  have h :=
    lemma79_holdList_firstEntryKey_freshTail_jointMass
      (start := start) (family := family) (C := C)
      (p := p) (entry := entry) hpC N Set.univ
  have huniv :
      (taoSection7HoldListPMF N).toOuterMeasure Set.univ = 1 :=
    ((taoSection7HoldListPMF N).toOuterMeasure_apply_eq_one_iff Set.univ).2
      (Set.subset_univ _)
  rw [huniv, mul_one] at h
  simpa using h

/-- Source-facing unnormalized first-entry-fiber/fresh-tail product law.

The first factor is the mass of the complete semantic key fiber under the same
master law as the joint event, so future-refined subsets cannot be substituted
for the key.
-/
theorem lemma79_holdList_firstEntryKey_freshTail_jointMass_eq_keyMass_mul
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C p : ℕ} {entry : TaoSection7Point}
    (hpC : p < C)
    (N : ℕ) (TailEvent : Set (List TaoSection7RenewalPoint)) :
    (taoSection7HoldListPMF (p + N)).toOuterMeasure
        {full |
          lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt start full) family C =
              some (p, entry) ∧
            full.drop p ∈ TailEvent} =
      (taoSection7HoldListPMF (p + N)).toOuterMeasure
          {full |
            lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt start full) family C =
              some (p, entry)} *
        (taoSection7HoldListPMF N).toOuterMeasure TailEvent := by
  calc
    _ = (taoSection7HoldListPMF p).toOuterMeasure
          (lemma79FirstEntryKeyPrefixEvent start family p entry) *
        (taoSection7HoldListPMF N).toOuterMeasure TailEvent :=
      lemma79_holdList_firstEntryKey_freshTail_jointMass
        (start := start) (family := family) (C := C)
        (p := p) (entry := entry) hpC N TailEvent
    _ = _ := by
      rw [← lemma79_holdList_firstEntryKey_mass_eq_prefixMass
        (start := start) (family := family) (C := C)
        (p := p) (entry := entry) hpC N]

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
