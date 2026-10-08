/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79CutoffStatistic

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem Lemma79BoundedStoppingTail.toBoundedStoppingTail_of_append
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {H q t : ℕ} {old Delta : TaoSection7Triangle}
    {before after : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79BoundedStoppingTail pointAt family q old H
      (before ++ (t, Delta) :: after)) :
    Lemma79BoundedStoppingTail pointAt family t Delta H after := by
  induction before generalizing q old with
  | nil =>
      simpa using htrace.tail
  | cons step before ih =>
      rcases step with ⟨first, Gamma⟩
      exact ih htrace.tail

theorem Lemma79BoundedInclusiveTrace.toBoundedStoppingTail_of_append
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {H t : ℕ} {Delta : TaoSection7Triangle}
    {before after : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79BoundedInclusiveTrace pointAt family H
      (before ++ (t, Delta) :: after)) :
    Lemma79BoundedStoppingTail pointAt family t Delta H after := by
  cases before with
  | nil =>
      simpa using htrace.toBoundedStoppingTail
  | cons step before =>
      rcases step with ⟨first, Gamma⟩
      exact htrace.toBoundedStoppingTail.toBoundedStoppingTail_of_append

theorem lemma79CutoffTrace_exists_first_le_of_hit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {C q : ℕ}
    (hqC : q < C)
    (hhit : TaoSection7Case3TriangleHit pointAt family q) :
    ∃ t Delta rest,
      lemma79CutoffTrace pointAt family C = (t, Delta) :: rest ∧
      t ≤ q ∧
      Lemma79FirstTriangleHitFromZero pointAt family t ∧
      Delta ∈ family ∧ Delta.Mem (pointAt t) := by
  have htrace := lemma79CutoffTrace_spec pointAt family C
  cases hsteps : lemma79CutoffTrace pointAt family C with
  | nil =>
      rw [hsteps] at htrace
      exact (htrace.terminal_empty rfl q hqC hhit).elim
  | cons step rest =>
      rcases step with ⟨t, Delta⟩
      rw [hsteps] at htrace
      have hfirst := htrace.trace_prefix.head_first_hit
      have htq : t ≤ q := by
        by_contra hnot
        exact hfirst.2 q (Nat.lt_of_not_ge hnot) hhit
      cases htrace.trace_prefix with
      | cons hfirst hDelta hmem _ =>
          exact ⟨t, Delta, rest, rfl, htq, hfirst, hDelta, hmem⟩

theorem lemma79CutoffTrace_next_of_decomp_of_afterTriangleHit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {C t p : ℕ} {Delta : TaoSection7Triangle}
    {before after : List (ℕ × TaoSection7Triangle)}
    (hdecomp :
      lemma79CutoffTrace pointAt family C =
        before ++ (t, Delta) :: after)
    (htp : t < p)
    (hpC : p < C)
    (hhit : TaoSection7Case3AfterTriangleHit pointAt family Delta p) :
    ∃ tNext Gamma rest,
      lemma79CutoffTrace pointAt family C =
        before ++ (t, Delta) :: (tNext, Gamma) :: rest ∧
      tNext ≤ p ∧
      TaoSection7Case3StoppingTransition
        pointAt family t Delta tNext Gamma := by
  have htrace : Lemma79BoundedInclusiveTrace pointAt family C
      (before ++ (t, Delta) :: after) := by
    rw [← hdecomp]
    exact lemma79CutoffTrace_spec pointAt family C
  have htail := htrace.toBoundedStoppingTail_of_append
  cases hafter : after with
  | nil =>
      rw [hafter] at htail
      exact (htail.terminal_empty rfl p htp hpC hhit).elim
  | cons step rest =>
      rcases step with ⟨tNext, Gamma⟩
      rw [hafter] at htail
      have hstep :=
        TaoSection7Case3StoppingTail.head_step htail.trace_tail
      have hnextP : tNext ≤ p := by
        by_contra hnot
        exact hstep.first_after_exit.2.2 p htp
          (Nat.lt_of_not_ge hnot) hhit
      exact ⟨tNext, Gamma, rest, by simpa [hafter] using hdecomp,
        hnextP, hstep⟩

theorem tR?_append_cons_length_add_one
    (before after : List (ℕ × TaoSection7Triangle))
    (t : ℕ) (Delta : TaoSection7Triangle) :
    tR? (before ++ (t, Delta) :: after) (before.length + 1) = some t := by
  induction before with
  | nil => simp [tR?]
  | cons step before ih =>
      simpa [tR?, Nat.add_assoc] using ih

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
