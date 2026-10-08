/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79TailExpectationCore

/-!
# Lemma 7.9 Zero-Inclusive Bounded Trace

This module constructs the finite stopping trace used by the repaired Lemma
7.9 induction.  Unlike the older Case 3 source run, its first scan includes
time zero.  Later steps still use the existing strict post-exit first-hit
predicate.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A stopping prefix whose first triangle hit may occur at time zero. -/
inductive Lemma79InclusiveStoppingPrefix
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    List (ℕ × TaoSection7Triangle) -> Prop
  | nil : Lemma79InclusiveStoppingPrefix pointAt family []
  | cons {first : ℕ} {Delta : TaoSection7Triangle}
      {rest : List (ℕ × TaoSection7Triangle)}
      (first_hit : Lemma79FirstTriangleHitFromZero pointAt family first)
      (mem_family : Delta ∈ family)
      (mem : Delta.Mem (pointAt first))
      (tail :
        TaoSection7Case3StoppingTail pointAt family first Delta rest) :
      Lemma79InclusiveStoppingPrefix
        pointAt family ((first, Delta) :: rest)

/-- Exact chronological bounded maximality for a zero-inclusive stopping trace. -/
structure Lemma79BoundedInclusiveTrace
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (H : ℕ) (steps : List (ℕ × TaoSection7Triangle)) : Prop where
  trace_prefix : Lemma79InclusiveStoppingPrefix pointAt family steps
  all_stop_lt : ∀ step ∈ steps, step.1 < H
  terminal_empty :
    steps = [] ->
      ∀ t : ℕ, t < H ->
        ¬ TaoSection7Case3TriangleHit pointAt family t
  terminal_last :
    ∀ last : ℕ × TaoSection7Triangle,
      TaoSection7Case3StoppingLast? steps = some last ->
        ∀ t : ℕ, last.1 < t -> t < H ->
          ¬ TaoSection7Case3AfterTriangleHit pointAt family last.2 t

/-- Chronologically complete bounded tail after an existing stopping step. -/
structure Lemma79BoundedStoppingTail
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (q : ℕ) (old : TaoSection7Triangle)
    (endTime : ℕ) (steps : List (ℕ × TaoSection7Triangle)) : Prop where
  trace_tail : TaoSection7Case3StoppingTail pointAt family q old steps
  all_stop_lt : ∀ step ∈ steps, step.1 < endTime
  terminal_empty :
    steps = [] ->
      ∀ t : ℕ, q < t -> t < endTime ->
        ¬ TaoSection7Case3AfterTriangleHit pointAt family old t
  terminal_last :
    ∀ last : ℕ × TaoSection7Triangle,
      TaoSection7Case3StoppingLast? steps = some last ->
        ∀ t : ℕ, last.1 < t -> t < endTime ->
          ¬ TaoSection7Case3AfterTriangleHit pointAt family last.2 t

/-- A triangle selected from a triangle-hit witness. -/
private noncomputable def lemma79TriangleOfHit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {t : ℕ}
    (h : TaoSection7Case3TriangleHit pointAt family t) :
    TaoSection7Triangle :=
  Classical.choose h

private theorem lemma79TriangleOfHit_mem_family
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {t : ℕ}
    (h : TaoSection7Case3TriangleHit pointAt family t) :
    lemma79TriangleOfHit h ∈ family :=
  (Classical.choose_spec h).1

private theorem lemma79TriangleOfHit_mem
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {t : ℕ}
    (h : TaoSection7Case3TriangleHit pointAt family t) :
    (lemma79TriangleOfHit h).Mem (pointAt t) :=
  (Classical.choose_spec h).2

/-- A new triangle selected from a post-exit hit witness. -/
private noncomputable def lemma79TriangleOfAfterHit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {t : ℕ}
    (h : TaoSection7Case3AfterTriangleHit pointAt family old t) :
    TaoSection7Triangle :=
  Classical.choose (taoSection7Case3_afterTriangleHit_new_triangle h)

private theorem lemma79TriangleOfAfterHit_spec
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {t : ℕ}
    (h : TaoSection7Case3AfterTriangleHit pointAt family old t) :
    lemma79TriangleOfAfterHit h ∈ family ∧
      (lemma79TriangleOfAfterHit h).Mem (pointAt t) ∧
      lemma79TriangleOfAfterHit h ≠ old :=
  Classical.choose_spec (taoSection7Case3_afterTriangleHit_new_triangle h)

/-- Scan consecutive times for the first later post-exit hit, then continue. -/
private noncomputable def lemma79BoundedTailScan
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    (q : ℕ) -> (old : TaoSection7Triangle) ->
      (start count : ℕ) -> List (ℕ × TaoSection7Triangle)
  | _q, _old, _start, 0 => []
  | q, old, start, count + 1 =>
      if h : TaoSection7Case3AfterTriangleHit pointAt family old start then
        let Delta := lemma79TriangleOfAfterHit h
        (start, Delta) ::
          lemma79BoundedTailScan pointAt family
            start Delta (start + 1) count
      else
        lemma79BoundedTailScan pointAt family q old (start + 1) count

/-- Scan consecutive times for the first triangle hit, including `start`. -/
private noncomputable def lemma79BoundedInitialScan
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    (start count : ℕ) -> List (ℕ × TaoSection7Triangle)
  | _start, 0 => []
  | start, count + 1 =>
      if h : TaoSection7Case3TriangleHit pointAt family start then
        let Delta := lemma79TriangleOfHit h
        (start, Delta) ::
          lemma79BoundedTailScan pointAt family
            start Delta (start + 1) count
      else
        lemma79BoundedInitialScan pointAt family (start + 1) count

private theorem lemma79BoundedTailScan_congr_of_eq_on_range
    {pointAt pointAt' : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q start count : ℕ} {old : TaoSection7Triangle}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hpoint :
      ∀ t : ℕ, start ≤ t -> t < start + count ->
        pointAt t = pointAt' t) :
    lemma79BoundedTailScan pointAt family q old start count =
      lemma79BoundedTailScan pointAt' family q old start count := by
  classical
  induction count generalizing q old start with
  | zero => rfl
  | succ count ih =>
      have hstart_eq : pointAt start = pointAt' start :=
        hpoint start le_rfl (by omega)
      by_cases hhit :
          TaoSection7Case3AfterTriangleHit pointAt family old start
      · have hhit' :
            TaoSection7Case3AfterTriangleHit pointAt' family old start := by
          simpa [TaoSection7Case3AfterTriangleHit, hstart_eq] using hhit
        have hDelta := lemma79TriangleOfAfterHit_spec hhit
        have hDelta' := lemma79TriangleOfAfterHit_spec hhit'
        have hDelta_eq :
            lemma79TriangleOfAfterHit hhit =
              lemma79TriangleOfAfterHit hhit' :=
          taoSection7Triangle_eq_of_familyPairwiseDisjoint_mem
            hpair hDelta.1 hDelta'.1 hDelta.2.1
              (by simpa [hstart_eq] using hDelta'.2.1)
        simp only [lemma79BoundedTailScan, dif_pos hhit, dif_pos hhit']
        rw [hDelta_eq]
        apply congrArg
          (fun tail => (start, lemma79TriangleOfAfterHit hhit') :: tail)
        exact
          ih (q := start) (old := lemma79TriangleOfAfterHit hhit')
            (start := start + 1)
            (by
              intro t hle hlt
              exact hpoint t (by omega) (by omega))
      · have hhit' :
            ¬ TaoSection7Case3AfterTriangleHit pointAt' family old start := by
          intro hhit'
          apply hhit
          simpa [TaoSection7Case3AfterTriangleHit, hstart_eq] using hhit'
        simp only [lemma79BoundedTailScan, dif_neg hhit, dif_neg hhit']
        exact ih (q := q) (old := old) (start := start + 1)
          (by
            intro t hle hlt
            exact hpoint t (by omega) (by omega))

private theorem lemma79BoundedInitialScan_congr_of_eq_on_range
    {pointAt pointAt' : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {start count : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hpoint :
      ∀ t : ℕ, start ≤ t -> t < start + count ->
        pointAt t = pointAt' t) :
    lemma79BoundedInitialScan pointAt family start count =
      lemma79BoundedInitialScan pointAt' family start count := by
  classical
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      have hstart_eq : pointAt start = pointAt' start :=
        hpoint start le_rfl (by omega)
      by_cases hhit : TaoSection7Case3TriangleHit pointAt family start
      · have hhit' : TaoSection7Case3TriangleHit pointAt' family start := by
          simpa [TaoSection7Case3TriangleHit, hstart_eq] using hhit
        have hDelta := Classical.choose_spec hhit
        have hDelta' := Classical.choose_spec hhit'
        have hDelta_eq : lemma79TriangleOfHit hhit = lemma79TriangleOfHit hhit' :=
          taoSection7Triangle_eq_of_familyPairwiseDisjoint_mem
            hpair hDelta.1 hDelta'.1 hDelta.2
              (by simpa [hstart_eq] using hDelta'.2)
        simp only [lemma79BoundedInitialScan, dif_pos hhit, dif_pos hhit']
        rw [hDelta_eq]
        apply congrArg
          (fun tail => (start, lemma79TriangleOfHit hhit') :: tail)
        exact
          lemma79BoundedTailScan_congr_of_eq_on_range
            (q := start) (old := lemma79TriangleOfHit hhit')
            (start := start + 1) (count := count) hpair
            (by
              intro t hle hlt
              exact hpoint t (by omega) (by omega))
      · have hhit' : ¬ TaoSection7Case3TriangleHit pointAt' family start := by
          intro hhit'
          apply hhit
          simpa [TaoSection7Case3TriangleHit, hstart_eq] using hhit'
        simp only [lemma79BoundedInitialScan, dif_neg hhit, dif_neg hhit']
        exact ih (start := start + 1)
          (by
            intro t hle hlt
            exact hpoint t (by omega) (by omega))

private theorem lemma79BoundedTailScan_spec
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q start count : ℕ} {old : TaoSection7Triangle}
    (hstart : q < start)
    (hno :
      ∀ t : ℕ, q < t -> t < start ->
        ¬ TaoSection7Case3AfterTriangleHit pointAt family old t) :
    Lemma79BoundedStoppingTail pointAt family q old (start + count)
      (lemma79BoundedTailScan pointAt family q old start count) := by
  classical
  induction count generalizing q old start with
  | zero =>
      refine
        { trace_tail := TaoSection7Case3StoppingTail.nil q old
          all_stop_lt := ?_
          terminal_empty := ?_
          terminal_last := ?_ }
      · intro step hmem
        simp [lemma79BoundedTailScan] at hmem
      · intro _ t hqt ht
        simpa using hno t hqt ht
      · intro last hlast
        simp [lemma79BoundedTailScan, TaoSection7Case3StoppingLast?] at hlast
  | succ count ih =>
      rw [lemma79BoundedTailScan]
      split
      next hhit =>
        let Delta := lemma79TriangleOfAfterHit hhit
        have hDelta := lemma79TriangleOfAfterHit_spec hhit
        have hstep :
            TaoSection7Case3StoppingTransition
              pointAt family q old start Delta :=
          { first_after_exit := ⟨hstart, hhit, hno⟩
            new_mem_family := hDelta.1
            new_mem := hDelta.2.1
            new_ne_old := hDelta.2.2 }
        have htail := ih (q := start) (old := Delta)
          (start := start + 1) (Nat.lt_succ_self start)
          (by
            intro t hst ht
            omega)
        refine
          { trace_tail := TaoSection7Case3StoppingTail.cons hstep htail.trace_tail
            all_stop_lt := ?_
            terminal_empty := ?_
            terminal_last := ?_ }
        · intro step hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with hstep_eq | hmem
          · cases hstep_eq
            omega
          · have := htail.all_stop_lt step hmem
            omega
        · intro hnil
          simp at hnil
        · intro last hlast t hlt htend
          change
            TaoSection7Case3StoppingLast?
                ((start, Delta) ::
                  lemma79BoundedTailScan pointAt family
                    start Delta (start + 1) count) =
              some last at hlast
          cases hrest : lemma79BoundedTailScan pointAt family
              start Delta (start + 1) count with
          | nil =>
              rw [hrest] at htail hlast
              simp [TaoSection7Case3StoppingLast?] at hlast
              subst last
              exact htail.terminal_empty rfl t hlt (by omega)
          | cons next rest =>
              rw [hrest] at htail hlast
              exact htail.terminal_last last
                (by
                  simpa [TaoSection7Case3StoppingLast?] using hlast)
                t hlt (by omega)
      next hmiss =>
        have hno' :
            ∀ t : ℕ, q < t -> t < start + 1 ->
              ¬ TaoSection7Case3AfterTriangleHit pointAt family old t := by
          intro t hqt ht
          by_cases hEq : t = start
          · subst t
            exact hmiss
          · exact hno t hqt (by omega)
        have htail := ih (q := q) (old := old)
          (start := start + 1) (by omega) hno'
        refine
          { trace_tail := htail.trace_tail
            all_stop_lt := ?_
            terminal_empty := ?_
            terminal_last := ?_ }
        · intro step hmem
          have := htail.all_stop_lt step hmem
          omega
        · intro hnil t hqt htend
          exact htail.terminal_empty hnil t hqt (by omega)
        · intro last hlast t hlt htend
          exact htail.terminal_last last hlast t hlt (by omega)

private theorem lemma79BoundedInitialScan_spec
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {start count : ℕ}
    (hno :
      ∀ t : ℕ, t < start ->
        ¬ TaoSection7Case3TriangleHit pointAt family t) :
    Lemma79BoundedInclusiveTrace pointAt family (start + count)
      (lemma79BoundedInitialScan pointAt family start count) := by
  classical
  induction count generalizing start with
  | zero =>
      refine
        { trace_prefix := Lemma79InclusiveStoppingPrefix.nil
          all_stop_lt := ?_
          terminal_empty := ?_
          terminal_last := ?_ }
      · intro step hmem
        simp [lemma79BoundedInitialScan] at hmem
      · intro _ t ht
        simpa using hno t ht
      · intro last hlast
        simp [lemma79BoundedInitialScan, TaoSection7Case3StoppingLast?] at hlast
  | succ count ih =>
      rw [lemma79BoundedInitialScan]
      split
      next hhit =>
        let Delta := lemma79TriangleOfHit hhit
        have htail := lemma79BoundedTailScan_spec
          (pointAt := pointAt) (family := family)
          (q := start) (old := Delta) (start := start + 1)
          (count := count) (Nat.lt_succ_self start)
          (by
            intro t hst ht
            omega)
        refine
          { trace_prefix := Lemma79InclusiveStoppingPrefix.cons
              ⟨hhit, hno⟩
              (lemma79TriangleOfHit_mem_family hhit)
              (lemma79TriangleOfHit_mem hhit)
              htail.trace_tail
            all_stop_lt := ?_
            terminal_empty := ?_
            terminal_last := ?_ }
        · intro step hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with hstep_eq | hmem
          · cases hstep_eq
            omega
          · have := htail.all_stop_lt step hmem
            omega
        · intro hnil
          simp at hnil
        · intro last hlast t hlt htend
          change
            TaoSection7Case3StoppingLast?
                ((start, Delta) ::
                  lemma79BoundedTailScan pointAt family
                    start Delta (start + 1) count) =
              some last at hlast
          cases hrest : lemma79BoundedTailScan pointAt family
              start Delta (start + 1) count with
          | nil =>
              rw [hrest] at htail hlast
              simp [TaoSection7Case3StoppingLast?] at hlast
              subst last
              exact htail.terminal_empty rfl t hlt (by omega)
          | cons next rest =>
              rw [hrest] at htail hlast
              exact htail.terminal_last last
                (by
                  simpa [TaoSection7Case3StoppingLast?] using hlast)
                t hlt (by omega)
      next hmiss =>
        have hno' :
            ∀ t : ℕ, t < start + 1 ->
              ¬ TaoSection7Case3TriangleHit pointAt family t := by
          intro t ht
          by_cases hEq : t = start
          · subst t
            exact hmiss
          · exact hno t (by omega)
        have htrace := ih (start := start + 1) hno'
        refine
          { trace_prefix := htrace.trace_prefix
            all_stop_lt := ?_
            terminal_empty := ?_
            terminal_last := ?_ }
        · intro step hmem
          have := htrace.all_stop_lt step hmem
          omega
        · intro hnil t ht
          exact htrace.terminal_empty hnil t (by omega)
        · intro last hlast t hlt ht
          exact htrace.terminal_last last hlast t hlt (by omega)

/-- The canonical finite scan of times `0, ..., H-1`. -/
noncomputable def lemma79BoundedInclusiveTraceSteps
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (H : ℕ) : List (ℕ × TaoSection7Triangle) :=
  lemma79BoundedInitialScan pointAt family 0 H

/-- The canonical bounded scan satisfies the complete zero-inclusive contract. -/
theorem lemma79BoundedInclusiveTraceSteps_spec
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (H : ℕ) :
    Lemma79BoundedInclusiveTrace pointAt family H
      (lemma79BoundedInclusiveTraceSteps pointAt family H) := by
  simpa [lemma79BoundedInclusiveTraceSteps] using
    lemma79BoundedInitialScan_spec
      (pointAt := pointAt) (family := family)
      (start := 0) (count := H)
      (by
        intro t ht
        omega)

/-- The complete scan depends only on points below its horizon. -/
theorem lemma79BoundedInclusiveTraceSteps_congr_of_eq_on_lt
    {pointAt pointAt' : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hpoint : ∀ t : ℕ, t < H -> pointAt t = pointAt' t) :
    lemma79BoundedInclusiveTraceSteps pointAt family H =
      lemma79BoundedInclusiveTraceSteps pointAt' family H := by
  apply lemma79BoundedInitialScan_congr_of_eq_on_range hpair
  intro t _ht0 htH
  exact hpoint t (by simpa using htH)

/-- Triangle-independent key projected from the head of a stopping trace. -/
def lemma79InclusiveTraceHeadKey
    (pointAt : ℕ -> TaoSection7Point)
    (steps : List (ℕ × TaoSection7Triangle)) :
    Option (ℕ × TaoSection7Point) :=
  steps.head?.map fun step => (step.1, pointAt step.1)

@[simp] theorem lemma79InclusiveTraceHeadKey_nil
    (pointAt : ℕ -> TaoSection7Point) :
    lemma79InclusiveTraceHeadKey pointAt [] = none :=
  rfl

@[simp] theorem lemma79InclusiveTraceHeadKey_cons
    (pointAt : ℕ -> TaoSection7Point)
    (step : ℕ × TaoSection7Triangle)
    (rest : List (ℕ × TaoSection7Triangle)) :
    lemma79InclusiveTraceHeadKey pointAt (step :: rest) =
      some (step.1, pointAt step.1) :=
  rfl

@[simp] theorem lemma79InclusiveTraceHeadKey_eq_none_iff
    (pointAt : ℕ -> TaoSection7Point)
    (steps : List (ℕ × TaoSection7Triangle)) :
    lemma79InclusiveTraceHeadKey pointAt steps = none ↔ steps = [] := by
  cases steps <;> simp

/-- Canonical first-entry time/point key of the bounded inclusive scan. -/
noncomputable def lemma79BoundedInclusiveTraceHeadKey
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (H : ℕ) : Option (ℕ × TaoSection7Point) :=
  lemma79InclusiveTraceHeadKey pointAt
    (lemma79BoundedInclusiveTraceSteps pointAt family H)

theorem lemma79FirstTriangleHitFromZero_time_eq
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first first' : ℕ}
    (hfirst : Lemma79FirstTriangleHitFromZero pointAt family first)
    (hfirst' : Lemma79FirstTriangleHitFromZero pointAt family first') :
    first = first' := by
  by_contra hne
  by_cases hlt : first < first'
  · exact hfirst'.2 first hlt hfirst.1
  · have hgt : first' < first := by omega
    exact hfirst.2 first' hgt hfirst'.1

@[simp] theorem lemma79FirstTriangleHitFromZero_zero_iff
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} :
    Lemma79FirstTriangleHitFromZero pointAt family 0 ↔
      TaoSection7Case3TriangleHit pointAt family 0 := by
  simp [Lemma79FirstTriangleHitFromZero]

theorem Lemma79FirstTriangleHitFromZero.congr_of_eq_on_lt
    {pointAt pointAt' : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H first : ℕ}
    (hfirst_lt : first < H)
    (hpoint : ∀ t : ℕ, t < H -> pointAt t = pointAt' t)
    (hfirst : Lemma79FirstTriangleHitFromZero pointAt family first) :
    Lemma79FirstTriangleHitFromZero pointAt' family first := by
  constructor
  · rcases hfirst.1 with ⟨Delta, hDelta, hmem⟩
    exact ⟨Delta, hDelta, by
      simpa only [hpoint first hfirst_lt] using hmem⟩
  · intro s hs hhit
    apply hfirst.2 s hs
    rcases hhit with ⟨Delta, hDelta, hmem⟩
    have hsH : s < H := hs.trans hfirst_lt
    exact ⟨Delta, hDelta, by
      simpa only [hpoint s hsH] using hmem⟩

namespace Lemma79InclusiveStoppingPrefix

theorem head_first_hit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Delta : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79InclusiveStoppingPrefix pointAt family
      ((first, Delta) :: rest)) :
    Lemma79FirstTriangleHitFromZero pointAt family first := by
  cases htrace with
  | cons hfirst _ _ _ => exact hfirst

theorem head_pair_eq_of_pairwiseDisjoint
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first first' : ℕ} {Delta Gamma : TaoSection7Triangle}
    {rest rest' : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace : Lemma79InclusiveStoppingPrefix pointAt family
      ((first, Delta) :: rest))
    (htrace' : Lemma79InclusiveStoppingPrefix pointAt family
      ((first', Gamma) :: rest')) :
    (first, Delta) = (first', Gamma) := by
  cases htrace with
  | cons hfirst hDelta hDelta_mem _ =>
      cases htrace' with
      | cons hfirst' hGamma hGamma_mem _ =>
          have htime : first = first' :=
            lemma79FirstTriangleHitFromZero_time_eq hfirst hfirst'
          subst first'
          have htriangle : Delta = Gamma :=
            taoSection7Triangle_eq_of_familyPairwiseDisjoint_mem
              hpair hDelta hGamma hDelta_mem hGamma_mem
          subst Gamma
          rfl

end Lemma79InclusiveStoppingPrefix

namespace Lemma79BoundedStoppingTail

/-- Remove the first transition from a chronologically complete bounded tail. -/
theorem tail
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H q first : ℕ}
    {old Delta : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79BoundedStoppingTail pointAt family q old H
      ((first, Delta) :: rest)) :
    Lemma79BoundedStoppingTail pointAt family first Delta H rest := by
  refine
    { trace_tail := TaoSection7Case3StoppingTail.tail htrace.trace_tail
      all_stop_lt := ?_
      terminal_empty := ?_
      terminal_last := ?_ }
  · intro step hmem
    exact htrace.all_stop_lt step (by simp [hmem])
  · intro hnil t hfirst htH
    exact htrace.terminal_last (first, Delta)
      (by simp [hnil, TaoSection7Case3StoppingLast?])
      t hfirst htH
  · intro last hlast t hlast_t htH
    exact htrace.terminal_last last
      (by
        cases rest with
        | nil =>
            simp [TaoSection7Case3StoppingLast?] at hlast
        | cons next rest =>
            simpa [TaoSection7Case3StoppingLast?] using hlast)
      t hlast_t htH

/-- A complete bounded tail is unique for a pairwise-disjoint family. -/
theorem steps_eq_of_pairwiseDisjoint
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H q : ℕ}
    {old : TaoSection7Triangle}
    {steps steps' : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace : Lemma79BoundedStoppingTail pointAt family q old H steps)
    (htrace' : Lemma79BoundedStoppingTail pointAt family q old H steps') :
    steps = steps' := by
  induction steps generalizing q old steps' with
  | nil =>
      cases steps' with
      | nil => rfl
      | cons step' rest' =>
          have hstep' :=
            TaoSection7Case3StoppingTail.head_step htrace'.trace_tail
          have hlt' := htrace'.all_stop_lt step' (by simp)
          exact
            (htrace.terminal_empty rfl step'.1
              hstep'.first_after_exit.1 hlt'
              hstep'.first_after_exit.2.1).elim
  | cons step rest ih =>
      rcases step with ⟨first, Delta⟩
      cases steps' with
      | nil =>
          have hstep :=
            TaoSection7Case3StoppingTail.head_step htrace.trace_tail
          have hlt := htrace.all_stop_lt (first, Delta) (by simp)
          exact
            (htrace'.terminal_empty rfl first
              hstep.first_after_exit.1 hlt
              hstep.first_after_exit.2.1).elim
      | cons step' rest' =>
          rcases step' with ⟨first', Gamma⟩
          have hstep :=
            TaoSection7Case3StoppingTail.head_step htrace.trace_tail
          have hstep' :=
            TaoSection7Case3StoppingTail.head_step htrace'.trace_tail
          have hp : (first, Delta) = (first', Gamma) :=
            TaoSection7Case3StoppingTransition.pair_eq_of_pairwiseDisjoint
              hpair hstep hstep'
          cases hp
          have hrest : rest = rest' :=
            ih (q := first) (old := Delta)
              htrace.tail htrace'.tail
          simp [hrest]

end Lemma79BoundedStoppingTail

/-- The tail of a nonempty complete inclusive trace is bounded-complete. -/
theorem Lemma79BoundedInclusiveTrace.toBoundedStoppingTail
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H first : ℕ}
    {Delta : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79BoundedInclusiveTrace pointAt family H
      ((first, Delta) :: rest)) :
    Lemma79BoundedStoppingTail pointAt family first Delta H rest := by
  refine
    { trace_tail := ?_
      all_stop_lt := ?_
      terminal_empty := ?_
      terminal_last := ?_ }
  · cases htrace.trace_prefix with
    | cons _ _ _ htail => exact htail
  · intro step hmem
    exact htrace.all_stop_lt step (by simp [hmem])
  · intro hnil t hfirst htH
    exact htrace.terminal_last (first, Delta)
      (by simp [hnil, TaoSection7Case3StoppingLast?])
      t hfirst htH
  · intro last hlast t hlast_t htH
    exact htrace.terminal_last last
      (by
        cases rest with
        | nil =>
            simp [TaoSection7Case3StoppingLast?] at hlast
        | cons next rest =>
            simpa [TaoSection7Case3StoppingLast?] using hlast)
      t hlast_t htH

/-- Complete inclusive traces are unique for a pairwise-disjoint family. -/
theorem Lemma79BoundedInclusiveTrace.steps_eq_of_pairwiseDisjoint
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H : ℕ}
    {steps steps' : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace : Lemma79BoundedInclusiveTrace pointAt family H steps)
    (htrace' : Lemma79BoundedInclusiveTrace pointAt family H steps') :
    steps = steps' := by
  cases steps with
  | nil =>
      cases steps' with
      | nil => rfl
      | cons step' rest' =>
          have hfirst' := htrace'.trace_prefix.head_first_hit
          have hlt' := htrace'.all_stop_lt step' (by simp)
          exact (htrace.terminal_empty rfl step'.1 hlt' hfirst'.1).elim
  | cons step rest =>
      rcases step with ⟨first, Delta⟩
      cases steps' with
      | nil =>
          have hfirst := htrace.trace_prefix.head_first_hit
          have hlt := htrace.all_stop_lt (first, Delta) (by simp)
          exact (htrace'.terminal_empty rfl first hlt hfirst.1).elim
      | cons step' rest' =>
          rcases step' with ⟨first', Gamma⟩
          have hhead : (first, Delta) = (first', Gamma) :=
            htrace.trace_prefix.head_pair_eq_of_pairwiseDisjoint
              hpair htrace'.trace_prefix
          cases hhead
          have hrest : rest = rest' :=
            Lemma79BoundedStoppingTail.steps_eq_of_pairwiseDisjoint
              hpair htrace.toBoundedStoppingTail
                htrace'.toBoundedStoppingTail
          simp [hrest]

/-- Every complete inclusive trace yields the same first-entry time/point key. -/
theorem Lemma79BoundedInclusiveTrace.headKey_eq
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H : ℕ}
    {steps steps' : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79BoundedInclusiveTrace pointAt family H steps)
    (htrace' : Lemma79BoundedInclusiveTrace pointAt family H steps') :
    lemma79InclusiveTraceHeadKey pointAt steps =
      lemma79InclusiveTraceHeadKey pointAt steps' := by
  cases steps with
  | nil =>
      cases steps' with
      | nil => rfl
      | cons step rest =>
          have hfirst := htrace'.trace_prefix.head_first_hit
          have hlt := htrace'.all_stop_lt step (by simp)
          exact (htrace.terminal_empty rfl step.1 hlt hfirst.1).elim
  | cons step rest =>
      cases steps' with
      | nil =>
          have hfirst := htrace.trace_prefix.head_first_hit
          have hlt := htrace.all_stop_lt step (by simp)
          exact (htrace'.terminal_empty rfl step.1 hlt hfirst.1).elim
      | cons step' rest' =>
          have hfirst := htrace.trace_prefix.head_first_hit
          have hfirst' := htrace'.trace_prefix.head_first_hit
          have htime : step.1 = step'.1 :=
            lemma79FirstTriangleHitFromZero_time_eq hfirst hfirst'
          simp [lemma79InclusiveTraceHeadKey, htime]

/-- Semantic specification of every present bounded trace-head key. -/
theorem Lemma79BoundedInclusiveTrace.headKey_some_spec
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79BoundedInclusiveTrace pointAt family H steps)
    {key : ℕ × TaoSection7Point}
    (hkey : lemma79InclusiveTraceHeadKey pointAt steps = some key) :
    key.1 < H ∧ key.2 = pointAt key.1 ∧
      Lemma79FirstTriangleHitFromZero pointAt family key.1 := by
  cases steps with
  | nil =>
      simp at hkey
  | cons step rest =>
      have hfirst := htrace.trace_prefix.head_first_hit
      have hlt := htrace.all_stop_lt step (by simp)
      rcases key with ⟨t, p⟩
      simp only [lemma79InclusiveTraceHeadKey_cons,
        Option.some.injEq, Prod.mk.injEq] at hkey
      rcases hkey with ⟨rfl, rfl⟩
      exact ⟨hlt, rfl, hfirst⟩

/-- Semantic specification of a present canonical bounded-scan key. -/
theorem lemma79BoundedInclusiveTraceHeadKey_some_spec
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H : ℕ}
    {key : ℕ × TaoSection7Point}
    (hkey : lemma79BoundedInclusiveTraceHeadKey pointAt family H = some key) :
    key.1 < H ∧ key.2 = pointAt key.1 ∧
      Lemma79FirstTriangleHitFromZero pointAt family key.1 := by
  exact
    (lemma79BoundedInclusiveTraceSteps_spec pointAt family H).headKey_some_spec
      (by
        simpa [lemma79BoundedInclusiveTraceHeadKey] using hkey)

/-- Every bounded inclusive first hit is the canonical trace-head key. -/
theorem lemma79BoundedInclusiveTraceHeadKey_eq_some_of_first_hit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H first : ℕ}
    (hfirst_lt : first < H)
    (hfirst : Lemma79FirstTriangleHitFromZero pointAt family first) :
    lemma79BoundedInclusiveTraceHeadKey pointAt family H =
      some (first, pointAt first) := by
  let steps := lemma79BoundedInclusiveTraceSteps pointAt family H
  have htrace := lemma79BoundedInclusiveTraceSteps_spec pointAt family H
  change Lemma79BoundedInclusiveTrace pointAt family H steps at htrace
  cases hsteps : steps with
  | nil =>
      rw [hsteps] at htrace
      exact (htrace.terminal_empty rfl first hfirst_lt hfirst.1).elim
  | cons step rest =>
      rw [hsteps] at htrace
      have hhead := htrace.trace_prefix.head_first_hit
      have htime : step.1 = first :=
        lemma79FirstTriangleHitFromZero_time_eq hhead hfirst
      simp [lemma79BoundedInclusiveTraceHeadKey,
        lemma79InclusiveTraceHeadKey, steps, hsteps, htime]

theorem lemma79BoundedInclusiveTraceHeadKey_eq_some_iff
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H first : ℕ} :
    lemma79BoundedInclusiveTraceHeadKey pointAt family H =
        some (first, pointAt first) ↔
      first < H ∧
        Lemma79FirstTriangleHitFromZero pointAt family first := by
  constructor
  · intro hkey
    have hspec := lemma79BoundedInclusiveTraceHeadKey_some_spec hkey
    exact ⟨hspec.1, hspec.2.2⟩
  · rintro ⟨hfirst_lt, hfirst⟩
    exact lemma79BoundedInclusiveTraceHeadKey_eq_some_of_first_hit
      hfirst_lt hfirst

/-- The canonical key is absent exactly when no hit occurs before the bound. -/
theorem lemma79BoundedInclusiveTraceHeadKey_eq_none_iff
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (H : ℕ) :
    lemma79BoundedInclusiveTraceHeadKey pointAt family H = none ↔
      ∀ t : ℕ, t < H ->
        ¬ TaoSection7Case3TriangleHit pointAt family t := by
  let steps := lemma79BoundedInclusiveTraceSteps pointAt family H
  have htrace := lemma79BoundedInclusiveTraceSteps_spec pointAt family H
  change Lemma79BoundedInclusiveTrace pointAt family H steps at htrace
  cases hsteps : steps with
  | nil =>
      rw [hsteps] at htrace
      constructor
      · intro _
        exact htrace.terminal_empty rfl
      · intro _
        simp [lemma79BoundedInclusiveTraceHeadKey,
          lemma79InclusiveTraceHeadKey, steps, hsteps]
  | cons step rest =>
      rw [hsteps] at htrace
      have hfirst := htrace.trace_prefix.head_first_hit
      have hlt := htrace.all_stop_lt step (by simp)
      constructor
      · intro hnone
        simp [lemma79BoundedInclusiveTraceHeadKey,
          lemma79InclusiveTraceHeadKey, steps, hsteps] at hnone
      · intro hno
        exact (hno step.1 hlt hfirst.1).elim

/-- The canonical head key depends only on path points before the horizon. -/
theorem lemma79BoundedInclusiveTraceHeadKey_congr
    {pointAt pointAt' : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H : ℕ}
    (hpoint : ∀ t : ℕ, t < H -> pointAt t = pointAt' t) :
    lemma79BoundedInclusiveTraceHeadKey pointAt family H =
      lemma79BoundedInclusiveTraceHeadKey pointAt' family H := by
  let steps := lemma79BoundedInclusiveTraceSteps pointAt family H
  let steps' := lemma79BoundedInclusiveTraceSteps pointAt' family H
  have htrace := lemma79BoundedInclusiveTraceSteps_spec pointAt family H
  have htrace' := lemma79BoundedInclusiveTraceSteps_spec pointAt' family H
  change Lemma79BoundedInclusiveTrace pointAt family H steps at htrace
  change Lemma79BoundedInclusiveTrace pointAt' family H steps' at htrace'
  change lemma79InclusiveTraceHeadKey pointAt steps =
    lemma79InclusiveTraceHeadKey pointAt' steps'
  cases hsteps : steps with
  | nil =>
      rw [hsteps] at htrace
      cases hsteps' : steps' with
      | nil => simp
      | cons step' rest' =>
          rw [hsteps'] at htrace'
          have hfirst' := htrace'.trace_prefix.head_first_hit
          have hlt' := htrace'.all_stop_lt step' (by simp)
          have hfirst :
              Lemma79FirstTriangleHitFromZero pointAt family step'.1 :=
            hfirst'.congr_of_eq_on_lt hlt'
              (fun t ht => (hpoint t ht).symm)
          exact (htrace.terminal_empty rfl step'.1 hlt' hfirst.1).elim
  | cons step rest =>
      rw [hsteps] at htrace
      cases hsteps' : steps' with
      | nil =>
          rw [hsteps'] at htrace'
          have hfirst := htrace.trace_prefix.head_first_hit
          have hlt := htrace.all_stop_lt step (by simp)
          have hfirst' :
              Lemma79FirstTriangleHitFromZero pointAt' family step.1 :=
            hfirst.congr_of_eq_on_lt hlt hpoint
          exact (htrace'.terminal_empty rfl step.1 hlt hfirst'.1).elim
      | cons step' rest' =>
          rw [hsteps'] at htrace'
          have hfirst := htrace.trace_prefix.head_first_hit
          have hfirst' := htrace'.trace_prefix.head_first_hit
          have hlt := htrace.all_stop_lt step (by simp)
          have hlt' := htrace'.all_stop_lt step' (by simp)
          have hfirst'_at_pointAt :
              Lemma79FirstTriangleHitFromZero pointAt family step'.1 :=
            hfirst'.congr_of_eq_on_lt hlt'
              (fun t ht => (hpoint t ht).symm)
          have htime : step.1 = step'.1 :=
            lemma79FirstTriangleHitFromZero_time_eq hfirst hfirst'_at_pointAt
          have hpoint_eq : pointAt step.1 = pointAt' step'.1 := by
            rw [← htime]
            exact hpoint step.1 hlt
          simp only [lemma79InclusiveTraceHeadKey_cons,
            Option.some.injEq, Prod.mk.injEq]
          exact ⟨htime, hpoint_eq⟩

/-- A time-zero hit is retained as the canonical first-entry key. -/
theorem lemma79BoundedInclusiveTraceHeadKey_eq_some_zero
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H : ℕ}
    (hH : 0 < H)
    (hhit : TaoSection7Case3TriangleHit pointAt family 0) :
    lemma79BoundedInclusiveTraceHeadKey pointAt family H =
      some (0, pointAt 0) := by
  let steps := lemma79BoundedInclusiveTraceSteps pointAt family H
  have htrace := lemma79BoundedInclusiveTraceSteps_spec pointAt family H
  change Lemma79BoundedInclusiveTrace pointAt family H steps at htrace
  cases hsteps : steps with
  | nil =>
      rw [hsteps] at htrace
      exact (htrace.terminal_empty rfl 0 hH hhit).elim
  | cons step rest =>
      rw [hsteps] at htrace
      have hfirst := htrace.trace_prefix.head_first_hit
      have htime : step.1 = 0 := by
        by_contra hne
        have hpos : 0 < step.1 := by omega
        exact hfirst.2 0 hpos hhit
      simp [lemma79BoundedInclusiveTraceHeadKey,
        lemma79InclusiveTraceHeadKey, steps, hsteps, htime]

@[simp] theorem lemma79BoundedInclusiveTraceSteps_zero
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    lemma79BoundedInclusiveTraceSteps pointAt family 0 = [] :=
  rfl

@[simp] theorem lemma79BoundedInclusiveTraceHeadKey_zero
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    lemma79BoundedInclusiveTraceHeadKey pointAt family 0 = none :=
  rfl

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
