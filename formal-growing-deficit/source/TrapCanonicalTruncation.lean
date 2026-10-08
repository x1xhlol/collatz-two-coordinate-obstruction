import Erdos1135.Tao.Renewal.Lemma79InclusiveTrace

/-! Restrict the native complete trace in time without changing its selected entries. -/

set_option autoImplicit false

namespace Erdos1135.Tao
open TaoSection7Case3SourceStoppingRun
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

def trapTraceBefore (M : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    List (ℕ × TaoSection7Triangle) :=
  steps.takeWhile fun step => decide (step.1 < M)

theorem trap_trace_before_isPrefix (M : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    trapTraceBefore M steps <+: steps := by
  exact ⟨_, List.takeWhile_append_dropWhile⟩

theorem trap_bounded_stopping_tail_before
    {pointAt : ℕ → TaoSection7Point} {family : Set TaoSection7Triangle}
    {M C q : ℕ} {old : TaoSection7Triangle} {steps : List (ℕ × TaoSection7Triangle)}
    (hMC : M ≤ C) (htrace : Lemma79BoundedStoppingTail pointAt family q old C steps) :
    Lemma79BoundedStoppingTail pointAt family q old M (trapTraceBefore M steps) := by
  induction steps generalizing q old with
  | nil =>
      refine ⟨TaoSection7Case3StoppingTail.nil q old, ?_, ?_, ?_⟩
      · simp [trapTraceBefore]
      · intro _ t hqt htM
        exact htrace.terminal_empty rfl t hqt (htM.trans_le hMC)
      · simp [trapTraceBefore, TaoSection7Case3StoppingLast?]
  | cons step rest ih =>
      rcases step with ⟨first, Delta⟩
      have hstep := TaoSection7Case3StoppingTail.head_step htrace.trace_tail
      by_cases hfirst : first < M
      · have htail := ih htrace.tail
        change Lemma79BoundedStoppingTail pointAt family q old M
          (List.takeWhile (fun step => decide (step.1 < M)) ((first, Delta) :: rest))
        simp only [List.takeWhile_cons, decide_eq_true_eq, hfirst, ↓reduceIte]
        change Lemma79BoundedStoppingTail pointAt family q old M
          ((first, Delta) :: trapTraceBefore M rest)
        refine ⟨TaoSection7Case3StoppingTail.cons hstep htail.trace_tail, ?_, ?_, ?_⟩
        · intro step hmem
          rcases List.mem_cons.mp hmem with hsame | hrest
          · subst step
            exact hfirst
          · exact htail.all_stop_lt step hrest
        · simp
        · intro last hlast t hlast_t htM
          cases hrest : trapTraceBefore M rest with
          | nil =>
              simp only [hrest, TaoSection7Case3StoppingLast?, Option.some.injEq] at hlast
              subst last
              exact htail.terminal_empty hrest t hlast_t htM
          | cons next after =>
              exact htail.terminal_last last
                (by simpa only [hrest, TaoSection7Case3StoppingLast?] using hlast)
                t hlast_t htM
      · change Lemma79BoundedStoppingTail pointAt family q old M
          (List.takeWhile (fun step => decide (step.1 < M)) ((first, Delta) :: rest))
        simp only [List.takeWhile_cons, decide_eq_true_eq, hfirst, ↓reduceIte]
        refine ⟨TaoSection7Case3StoppingTail.nil q old, ?_, ?_, ?_⟩
        · simp
        · intro _ t hqt htM
          exact hstep.first_after_exit.2.2 t hqt (by omega)
        · simp [TaoSection7Case3StoppingLast?]

theorem trap_bounded_inclusive_trace_before
    {pointAt : ℕ → TaoSection7Point} {family : Set TaoSection7Triangle}
    {M C : ℕ} {steps : List (ℕ × TaoSection7Triangle)}
    (hMC : M ≤ C) (htrace : Lemma79BoundedInclusiveTrace pointAt family C steps) :
    Lemma79BoundedInclusiveTrace pointAt family M (trapTraceBefore M steps) := by
  cases steps with
  | nil =>
      refine ⟨Lemma79InclusiveStoppingPrefix.nil, ?_, ?_, ?_⟩
      · simp [trapTraceBefore]
      · intro _ t htM
        exact htrace.terminal_empty rfl t (htM.trans_le hMC)
      · simp [trapTraceBefore, TaoSection7Case3StoppingLast?]
  | cons step rest =>
      rcases step with ⟨first, Delta⟩
      have hfirsthit := htrace.trace_prefix.head_first_hit
      by_cases hfirst : first < M
      · have htail := trap_bounded_stopping_tail_before hMC htrace.toBoundedStoppingTail
        change Lemma79BoundedInclusiveTrace pointAt family M
          (List.takeWhile (fun step => decide (step.1 < M)) ((first, Delta) :: rest))
        simp only [List.takeWhile_cons, decide_eq_true_eq, hfirst, ↓reduceIte]
        change Lemma79BoundedInclusiveTrace pointAt family M
          ((first, Delta) :: trapTraceBefore M rest)
        refine ⟨?_, ?_, ?_, ?_⟩
        · cases htrace.trace_prefix with
          | cons hhit hfamily hmem _ =>
              exact Lemma79InclusiveStoppingPrefix.cons hhit hfamily hmem htail.trace_tail
        · intro step hmem
          rcases List.mem_cons.mp hmem with hsame | hrest
          · subst step
            exact hfirst
          · exact htail.all_stop_lt step hrest
        · simp
        · intro last hlast t hlast_t htM
          cases hrest : trapTraceBefore M rest with
          | nil =>
              simp only [hrest, TaoSection7Case3StoppingLast?, Option.some.injEq] at hlast
              subst last
              exact htail.terminal_empty hrest t hlast_t htM
          | cons next after =>
              exact htail.terminal_last last
                (by simpa only [hrest, TaoSection7Case3StoppingLast?] using hlast)
                t hlast_t htM
      · change Lemma79BoundedInclusiveTrace pointAt family M
          (List.takeWhile (fun step => decide (step.1 < M)) ((first, Delta) :: rest))
        simp only [List.takeWhile_cons, decide_eq_true_eq, hfirst, ↓reduceIte]
        refine ⟨Lemma79InclusiveStoppingPrefix.nil, ?_, ?_, ?_⟩
        · simp
        · intro _ t htM
          exact hfirsthit.2 t (by omega)
        · simp [TaoSection7Case3StoppingLast?]

theorem trap_canonical_inclusive_trace_before
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle)
    (M C : ℕ) (hMC : M ≤ C) (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79BoundedInclusiveTraceSteps pointAt family M =
      trapTraceBefore M (lemma79BoundedInclusiveTraceSteps pointAt family C) := by
  exact Lemma79BoundedInclusiveTrace.steps_eq_of_pairwiseDisjoint hpair
    (lemma79BoundedInclusiveTraceSteps_spec pointAt family M)
    (trap_bounded_inclusive_trace_before hMC
      (lemma79BoundedInclusiveTraceSteps_spec pointAt family C))

theorem trap_canonical_inclusive_trace_prefix
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle)
    (M C : ℕ) (hMC : M ≤ C) (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79BoundedInclusiveTraceSteps pointAt family M <+:
      lemma79BoundedInclusiveTraceSteps pointAt family C := by
  rw [trap_canonical_inclusive_trace_before pointAt family M C hMC hpair]
  exact trap_trace_before_isPrefix M _

theorem trap_tR_append_of_le_length
    (before after : List (ℕ × TaoSection7Triangle)) (R : ℕ) (hR : R ≤ before.length) :
    tR? (before ++ after) R = tR? before R := by
  induction before generalizing R with
  | nil =>
      have : R = 0 := by simpa using hR
      subst R
      cases after <;> simp [tR?]
  | cons first rest ih =>
      cases R with
      | zero => simp [tR?]
      | succ R =>
          cases R with
          | zero => simp [tR?]
          | succ R =>
              simpa [tR?] using ih (R + 1) (by simpa using hR)

theorem trap_tR_eq_of_prefix
    {before full : List (ℕ × TaoSection7Triangle)} (hprefix : before <+: full)
    (R : ℕ) (hR : R ≤ before.length) : tR? full R = tR? before R := by
  obtain ⟨after, rfl⟩ := hprefix
  exact trap_tR_append_of_le_length before after R hR

theorem trap_full_stop_of_truncated_length
    {pointAt : ℕ → TaoSection7Point} {family : Set TaoSection7Triangle}
    {M C R : ℕ} {steps : List (ℕ × TaoSection7Triangle)}
    (hMC : M ≤ C) (htrace : Lemma79BoundedInclusiveTrace pointAt family C steps)
    (hRpos : 0 < R) (hR : R ≤ (trapTraceBefore M steps).length) :
    ∃ t, tR? steps R = some t ∧ t < M := by
  have hrestricted := trap_bounded_inclusive_trace_before hMC htrace
  obtain ⟨t, ht, htM⟩ := hasTWithinWindow_of_hasAtLeast_all_ltP hRpos hR
    hrestricted.all_stop_lt
  refine ⟨t, ?_, htM⟩
  rw [trap_tR_eq_of_prefix (trap_trace_before_isPrefix M steps) R hR]
  exact ht

theorem trap_full_stop_horizontal_of_truncated_length
    {pointAt : ℕ → TaoSection7Point} {family : Set TaoSection7Triangle}
    {M C R J : ℕ} {steps : List (ℕ × TaoSection7Triangle)}
    (hMC : M ≤ C) (htrace : Lemma79BoundedInclusiveTrace pointAt family C steps)
    (hRpos : 0 < R) (hR : R ≤ (trapTraceBefore M steps).length)
    (hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ J) :
    ∃ t, tR? steps R = some t ∧ ((pointAt t).j : ℕ) ≤ J := by
  obtain ⟨t, ht, htM⟩ := trap_full_stop_of_truncated_length hMC htrace hRpos hR
  exact ⟨t, ht, hdomain t htM⟩

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_bounded_inclusive_trace_before
#print axioms Erdos1135.Tao.trap_canonical_inclusive_trace_before
#print axioms Erdos1135.Tao.trap_canonical_inclusive_trace_prefix
#print axioms Erdos1135.Tao.trap_full_stop_horizontal_of_truncated_length
