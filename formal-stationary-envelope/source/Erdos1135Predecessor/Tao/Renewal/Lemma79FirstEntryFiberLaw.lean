/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79FirstEntryCylinder
import Erdos1135Predecessor.Tao.Renewal.Lemma79TailExpectationCore

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

noncomputable def lemma79FirstEntryKeyPrefixEvent
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (p : ℕ) (entry : TaoSection7Point) :
    Set (List TaoSection7RenewalPoint) :=
  {pre |
    lemma79BoundedInclusiveTraceHeadKey
        (lemma79HoldPathPointAt start pre) family (p + 1) =
      some (p, entry)}

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

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
