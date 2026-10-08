import Erdos1135.Tao.Renewal.Lemma79InclusiveTrace
import TrapFewWhiteFamily

/-! The actual bounded inclusive stopping trace supplies the entry contracts. -/

set_option autoImplicit false

namespace Erdos1135.Tao
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

theorem trap_list_getD_mem {α : Type} (steps : List α) (fallback : α)
    (i : ℕ) (hi : i < steps.length) : steps.getD i fallback ∈ steps := by
  rw [List.getD_eq_getElem steps fallback hi]
  exact List.mem_of_getElem rfl

theorem trap_stopping_tail_mem
    {pointAt : ℕ → TaoSection7Point} {family : Set TaoSection7Triangle}
    {q : ℕ} {old : TaoSection7Triangle} {steps : List (ℕ × TaoSection7Triangle)}
    (htail : TaoSection7Case3StoppingTail pointAt family q old steps) :
    ∀ step ∈ steps, step.2 ∈ family ∧ step.2.Mem (pointAt step.1) := by
  induction htail with
  | nil => simp
  | @cons q first old Delta rest hstep htail ih =>
      intro step hmem
      rcases List.mem_cons.mp hmem with hsame | hrest
      · subst step
        exact ⟨hstep.new_mem_family, hstep.new_mem⟩
      · exact ih step hrest

theorem trap_inclusive_prefix_mem
    {pointAt : ℕ → TaoSection7Point} {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79InclusiveStoppingPrefix pointAt family steps) :
    ∀ step ∈ steps, step.2 ∈ family ∧ step.2.Mem (pointAt step.1) := by
  cases htrace with
  | nil => simp
  | cons hfirst hfamily hmem htail =>
      intro step hstep
      rcases List.mem_cons.mp hstep with hsame | hrest
      · subst step
        exact ⟨hfamily, hmem⟩
      · exact trap_stopping_tail_mem htail step hrest

theorem trap_stopping_tail_getD_transition
    {pointAt : ℕ → TaoSection7Point} {family : Set TaoSection7Triangle}
    (fallback : ℕ × TaoSection7Triangle) (i : ℕ)
    {q : ℕ} {old : TaoSection7Triangle} {rest : List (ℕ × TaoSection7Triangle)}
    (htail : TaoSection7Case3StoppingTail pointAt family q old rest)
    (hi : i < rest.length) :
    TaoSection7Case3StoppingTransition pointAt family
      (((q, old) :: rest).getD i fallback).1
      (((q, old) :: rest).getD i fallback).2
      (rest.getD i fallback).1 (rest.getD i fallback).2 := by
  induction i generalizing q old rest with
  | zero =>
      cases rest with
      | nil => simp at hi
      | cons next rest =>
          exact TaoSection7Case3StoppingTail.head_step htail
  | succ i ih =>
      cases rest with
      | nil => simp at hi
      | cons next rest =>
          simpa only [List.getD_cons_succ] using
            ih (TaoSection7Case3StoppingTail.tail htail) (by simpa using hi)

theorem trap_stopping_last_getD
    (first fallback : ℕ × TaoSection7Triangle) (rest : List (ℕ × TaoSection7Triangle)) :
    TaoSection7Case3StoppingLast? (first :: rest) =
      some ((first :: rest).getD rest.length fallback) := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      simpa only [TaoSection7Case3StoppingLast?, List.length_cons,
        List.getD_cons_succ] using ih next

theorem trap_bounded_inclusive_entry_contracts
    {pointAt : ℕ → TaoSection7Point} {family : Set TaoSection7Triangle} {M : ℕ}
    (first : ℕ × TaoSection7Triangle) (rest : List (ℕ × TaoSection7Triangle))
    (htrace : Lemma79BoundedInclusiveTrace pointAt family M (first :: rest)) :
    let entry := fun i => (first :: rest).getD i first
    (∀ i ≤ rest.length, (entry i).1 < M) ∧
    (∀ i ≤ rest.length, (entry i).2.Mem (pointAt (entry i).1)) ∧
    (∀ i ≤ rest.length, (entry i).2 ∈ family) ∧
    (∀ q < (entry 0).1, ¬ TaoSection7Case3TriangleHit pointAt family q) ∧
    (∀ i < rest.length, TaoSection7Case3FirstAfterTriangleHitFrom pointAt family
      (entry i).2 (entry i).1 (entry (i + 1)).1) ∧
    (∀ q, (entry rest.length).1 < q → q < M →
      ¬ TaoSection7Case3AfterTriangleHit pointAt family (entry rest.length).2 q) := by
  dsimp only
  have hget i (hi : i ≤ rest.length) :=
    trap_list_getD_mem (first :: rest) first i (by simpa using hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact htrace.all_stop_lt _ (hget i hi)
  · intro i hi
    exact (trap_inclusive_prefix_mem htrace.trace_prefix _ (hget i hi)).2
  · intro i hi
    exact (trap_inclusive_prefix_mem htrace.trace_prefix _ (hget i hi)).1
  · exact htrace.trace_prefix.head_first_hit.2
  · intro i hi
    exact (trap_stopping_tail_getD_transition first i
      htrace.toBoundedStoppingTail.trace_tail hi).first_after_exit
  · exact htrace.terminal_last _ (trap_stopping_last_getD first first rest)

theorem exists_native_black_trap_family_of_bounded_trace
    (n coverJ J M K H : ℕ) (xi : ZMod (3 ^ n)) (epsilon V D : ℝ)
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle)
    (first : ℕ × TaoSection7Triangle) (rest : List (ℕ × TaoSection7Triangle)) (S : ℤ)
    (hxi : zmodThreePrimitive n xi) (hnJ : 2 * J ≤ n) (hJcover : J ≤ coverJ) (hV : 0 ≤ V)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon coverJ) family)
    (hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ J)
    (hcount : trapSourceWhiteCount n xi epsilon pointAt M ≤ K)
    (htrace : Lemma79BoundedInclusiveTrace pointAt family M (first :: rest))
    (hmonoJ : Monotone fun q => ((pointAt q).j : ℕ))
    (hstepJ : ∀ q < M, ((pointAt (q + 1)).j : ℕ) ≤ (pointAt q).j + H)
    (hstepL : ∀ q < M, ((pointAt (q + 1)).l : ℝ) ≤ (pointAt q).l + V)
    (htube : ∀ q < M, |((pointAt q).l : ℝ) - 4 * (((pointAt q).j : ℕ) : ℝ)| ≤ D)
    (hS : |(S : ℝ) - 4 * (J : ℝ)| ≤ D)
    (hendpoint : S ≤ (pointAt M).l) :
    ∃ f : NativeBlackTrapFamily epsilon n rest.length,
      f.xi = xi ∧
      nativeTrapFamilyError f ≤
        2 * ((rest.length : ℝ) + 1) * D + V * ((K : ℝ) + 1) +
          2 * V * ((K : ℝ) + rest.length) ∧
      4 * (J : ℝ) - 4 * ((((pointAt 0).j : ℕ) + H * K : ℕ) : ℝ) -
        2 * D - V * ((K : ℝ) + 1) ≤ nativeTrapFamilySpan f := by
  let entry := fun i => (first :: rest).getD i first
  obtain ⟨hstop, hmem, hfamily, hfirst, hnext, hterminal⟩ :=
    trap_bounded_inclusive_entry_contracts first rest htrace
  exact exists_native_black_trap_family_of_few_white n coverJ J M rest.length K H
    xi epsilon V D pointAt family (fun i => (entry i).1) (fun i => (entry i).2) S
    hxi hnJ hJcover hV hcover hdomain hcount hstop hmem hfamily hfirst hnext hterminal
    hmonoJ hstepJ hstepL htube hS hendpoint

theorem trap_bounded_inclusive_nonempty_of_few_white
    (n coverJ M : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle)
    (steps : List (ℕ × TaoSection7Triangle))
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon coverJ) family)
    (hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ coverJ)
    (hcount : trapSourceWhiteCount n xi epsilon pointAt M < M)
    (htrace : Lemma79BoundedInclusiveTrace pointAt family M steps) : steps ≠ [] := by
  obtain ⟨q, hq, hhit⟩ := trap_source_exists_triangle_hit_of_few_white
    n coverJ M xi epsilon pointAt family hcover hdomain hcount
  intro hnil
  exact htrace.terminal_empty hnil q hq hhit

theorem exists_native_black_trap_family_of_canonical_inclusive_trace
    (n coverJ J M K H : ℕ) (xi : ZMod (3 ^ n)) (epsilon V D : ℝ)
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle) (S : ℤ)
    (hxi : zmodThreePrimitive n xi) (hnJ : 2 * J ≤ n) (hJcover : J ≤ coverJ) (hV : 0 ≤ V)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon coverJ) family)
    (hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ J)
    (hcount : trapSourceWhiteCount n xi epsilon pointAt M ≤ K) (hKM : K < M)
    (hmonoJ : Monotone fun q => ((pointAt q).j : ℕ))
    (hstepJ : ∀ q < M, ((pointAt (q + 1)).j : ℕ) ≤ (pointAt q).j + H)
    (hstepL : ∀ q < M, ((pointAt (q + 1)).l : ℝ) ≤ (pointAt q).l + V)
    (htube : ∀ q < M, |((pointAt q).l : ℝ) - 4 * (((pointAt q).j : ℕ) : ℝ)| ≤ D)
    (hS : |(S : ℝ) - 4 * (J : ℝ)| ≤ D)
    (hendpoint : S ≤ (pointAt M).l) :
    ∃ r : ℕ, ∃ f : NativeBlackTrapFamily epsilon n r,
      (lemma79BoundedInclusiveTraceSteps pointAt family M).length = r + 1 ∧
      f.xi = xi ∧
      nativeTrapFamilyError f ≤
        2 * ((r : ℝ) + 1) * D + V * ((K : ℝ) + 1) + 2 * V * ((K : ℝ) + r) ∧
      4 * (J : ℝ) - 4 * ((((pointAt 0).j : ℕ) + H * K : ℕ) : ℝ) -
        2 * D - V * ((K : ℝ) + 1) ≤ nativeTrapFamilySpan f := by
  have htrace := lemma79BoundedInclusiveTraceSteps_spec pointAt family M
  have hne := trap_bounded_inclusive_nonempty_of_few_white n coverJ M xi epsilon
    pointAt family _ hcover (fun q hq => (hdomain q hq).trans hJcover)
    (hcount.trans_lt hKM) htrace
  cases hsteps : lemma79BoundedInclusiveTraceSteps pointAt family M with
  | nil => exact (hne hsteps).elim
  | cons first rest =>
      rw [hsteps] at htrace
      obtain ⟨f, hfxi, herr, hspan⟩ := exists_native_black_trap_family_of_bounded_trace
        n coverJ J M K H xi epsilon V D pointAt family first rest S
        hxi hnJ hJcover hV hcover hdomain hcount htrace
        hmonoJ hstepJ hstepL htube hS hendpoint
      exact ⟨rest.length, f, rfl, hfxi, herr, hspan⟩

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_bounded_inclusive_entry_contracts
#print axioms Erdos1135.Tao.trap_bounded_inclusive_nonempty_of_few_white
#print axioms Erdos1135.Tao.exists_native_black_trap_family_of_bounded_trace
#print axioms Erdos1135.Tao.exists_native_black_trap_family_of_canonical_inclusive_trace
