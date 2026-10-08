/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma77LocalLimit
import Erdos1135Predecessor.Tao.Renewal.Lemma79InclusiveTrace

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

def lemma79HoldPathPointAt
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (q : ℕ) : TaoSection7Point :=
  (taoSection7RenewalPathPoint start full q).toPoint

theorem lemma79HoldPathPoint_j_gt_cutoff
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint} {C q : ℕ}
    (hlen : C ≤ full.length) (hCq : C ≤ q) :
    C < ((taoSection7RenewalPathPoint start full q).j : ℕ) := by
  by_cases hq : q ≤ full.length
  · have hdelta :=
      TaoSection7Lemma77.lemma77HoldPrefixHorizontalDelta_ge_steps hq
    rw [TaoSection7Lemma77.lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta]
    have hstart : 0 < (start.j : ℕ) := start.j.2
    omega
  · have hlen_q : full.length ≤ q := by omega
    have hdelta :=
      TaoSection7Lemma77.lemma77HoldPrefixHorizontalDelta_ge_steps
        (q := full.length) (full := full) le_rfl
    have hend :
        C < ((taoSection7RenewalPathPoint start full full.length).j : ℕ) := by
      rw [TaoSection7Lemma77.lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta]
      have hstart : 0 < (start.j : ℕ) := start.j.2
      omega
    have hclamp :
        taoSection7RenewalPathPoint start full full.length =
          taoSection7RenewalPathPoint start full q := by
      have h := taoSection7RenewalPathPoint_drop_add
        start full full.length (q - full.length)
      simpa [Nat.add_sub_of_le hlen_q] using h
    rwa [← hclamp]

theorem lemma79HoldPath_noTriangleHit_ge_cutoff
    {n C : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hlen : C ≤ full.length) :
    ∀ q : ℕ, C ≤ q ->
      ¬ TaoSection7Case3TriangleHit
        (lemma79HoldPathPointAt start full) family q := by
  intro q hCq hhit
  have hblack :
      taoSection7SourceBlackInDomain n xi epsilon C
        (lemma79HoldPathPointAt start full q) :=
    (hcover _).mpr hhit
  have hdomain := taoSection7SourceBlackInDomain_domain hblack
  have hgt := lemma79HoldPathPoint_j_gt_cutoff
    (start := start) (full := full) hlen hCq
  have hle :
      ((taoSection7RenewalPathPoint start full q).j : ℕ) ≤ C := by
    simpa [lemma79HoldPathPointAt] using hdomain
  omega

theorem lemma79BoundedInclusiveTrace_complete_of_noHit_ge
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79BoundedInclusiveTrace pointAt family H steps)
    (hno :
      ∀ q : ℕ, H ≤ q ->
        ¬ TaoSection7Case3TriangleHit pointAt family q) :
    (steps = [] ->
      ∀ q : ℕ, ¬ TaoSection7Case3TriangleHit pointAt family q) ∧
    (∀ last : ℕ × TaoSection7Triangle,
      TaoSection7Case3StoppingLast? steps = some last ->
        ∀ q : ℕ, last.1 < q ->
          ¬ TaoSection7Case3AfterTriangleHit pointAt family last.2 q) := by
  constructor
  · intro hnil q
    by_cases hq : q < H
    · exact htrace.terminal_empty hnil q hq
    · exact hno q (by omega)
  · intro last hlast q hlast_q
    by_cases hq : q < H
    · exact htrace.terminal_last last hlast q hlast_q hq
    · intro hafter
      exact hno q (by omega) hafter.2

theorem lemma79HoldPathPointAt_take_eq_of_le
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    {q C : ℕ} (hq : q ≤ C) :
    lemma79HoldPathPointAt start (full.take C) q =
      lemma79HoldPathPointAt start full q := by
  apply congrArg TaoSection7RenewalPoint.toPoint
  exact TaoSection7Lemma710.renewalPathPoint_take_eq_of_le
    start full q C hq

theorem lemma79HoldPathInclusiveTraceSteps_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {C : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79BoundedInclusiveTraceSteps
        (lemma79HoldPathPointAt start full) family C =
      lemma79BoundedInclusiveTraceSteps
        (lemma79HoldPathPointAt start (full.take C)) family C := by
  apply lemma79BoundedInclusiveTraceSteps_congr_of_eq_on_lt hpair
  intro q hq
  exact (lemma79HoldPathPointAt_take_eq_of_le start full
    (Nat.le_of_lt hq)).symm

theorem lemma79HoldPathInclusiveTraceHeadKey_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {C : ℕ} :
    lemma79BoundedInclusiveTraceHeadKey
        (lemma79HoldPathPointAt start full) family C =
      lemma79BoundedInclusiveTraceHeadKey
        (lemma79HoldPathPointAt start (full.take C)) family C := by
  apply lemma79BoundedInclusiveTraceHeadKey_congr
  intro q hq
  exact (lemma79HoldPathPointAt_take_eq_of_le start full
    (Nat.le_of_lt hq)).symm

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
