/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79CutoffStatistic

/-!
# Lemma 7.9 Restart Bookkeeping

This proof leaf records the deterministic time-shift, Hold-path rebase, and
positive-time white-count identities needed before the repaired cutoff
statistic can be restarted.  It does not yet identify the canonical restarted
trace or prove the repaired recurrence.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Add `k` to every recorded stopping time. -/
def lemma79ShiftSteps (k : ℕ)
    (steps : List (ℕ × TaoSection7Triangle)) :
    List (ℕ × TaoSection7Triangle) :=
  steps.map fun step => (k + step.1, step.2)

@[simp] theorem lemma79ShiftSteps_zero
    (steps : List (ℕ × TaoSection7Triangle)) :
    lemma79ShiftSteps 0 steps = steps := by
  simp [lemma79ShiftSteps]

@[simp] theorem lemma79ShiftSteps_length
    (k : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    (lemma79ShiftSteps k steps).length = steps.length := by
  simp [lemma79ShiftSteps]

@[simp] theorem lemma79_r_shiftSteps
    (k : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    r (lemma79ShiftSteps k steps) = r steps := by
  simp [r]

@[simp] theorem lemma79_tR?_shiftSteps
    (k : ℕ) (steps : List (ℕ × TaoSection7Triangle)) (R : ℕ) :
    tR? (lemma79ShiftSteps k steps) R =
      (tR? steps R).map (fun t => k + t) := by
  induction steps generalizing R with
  | nil =>
      cases R <;> simp [lemma79ShiftSteps, tR?]
  | cons step rest ih =>
      cases R with
      | zero => simp [lemma79ShiftSteps, tR?]
      | succ Rpred =>
          cases Rpred with
          | zero => simp [lemma79ShiftSteps, tR?]
          | succ Rtail =>
              simpa [lemma79ShiftSteps, tR?] using ih (Rtail + 1)

@[simp] theorem lemma79ShiftSteps_take
    (k R : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    lemma79ShiftSteps k (steps.take R) =
      (lemma79ShiftSteps k steps).take R := by
  simp [lemma79ShiftSteps]

@[simp] theorem lemma79ShiftSteps_drop
    (k R : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    lemma79ShiftSteps k (steps.drop R) =
      (lemma79ShiftSteps k steps).drop R := by
  simp [lemma79ShiftSteps]

@[simp] theorem lemma79ShiftSteps_add
    (k m : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    lemma79ShiftSteps k (lemma79ShiftSteps m steps) =
      lemma79ShiftSteps (k + m) steps := by
  simp [lemma79ShiftSteps, Nat.add_assoc]

/-- Subtract `k` from every recorded stopping time. -/
def lemma79LocalSteps (k : ℕ) :
    List (ℕ × TaoSection7Triangle) -> List (ℕ × TaoSection7Triangle)
  | [] => []
  | (t, Delta) :: rest =>
      (t - k, Delta) :: lemma79LocalSteps k rest

/-- Localizing steps that were shifted by `k` recovers the original list. -/
@[simp] theorem lemma79LocalSteps_shiftSteps
    (k : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    lemma79LocalSteps k (lemma79ShiftSteps k steps) = steps := by
  induction steps with
  | nil => simp [lemma79LocalSteps, lemma79ShiftSteps]
  | cons step rest ih =>
      rcases step with ⟨t, Delta⟩
      simp only [lemma79ShiftSteps, List.map_cons, lemma79LocalSteps]
      change (k + t - k, Delta) ::
          lemma79LocalSteps k (lemma79ShiftSteps k rest) =
        (t, Delta) :: rest
      rw [ih]
      simp

/-- Shifting localized steps is inverse when all original times are at least `k`. -/
theorem lemma79ShiftSteps_localSteps_of_forall_le
    (k : ℕ) (steps : List (ℕ × TaoSection7Triangle))
    (hall : ∀ step ∈ steps, k ≤ step.1) :
    lemma79ShiftSteps k (lemma79LocalSteps k steps) = steps := by
  induction steps with
  | nil => simp [lemma79LocalSteps, lemma79ShiftSteps]
  | cons step rest ih =>
      rcases step with ⟨t, Delta⟩
      have hhead : k ≤ t := hall (t, Delta) (by simp)
      have htail : ∀ s ∈ rest, k ≤ s.1 := by
        intro s hs
        exact hall s (by simp [hs])
      simp only [lemma79LocalSteps, lemma79ShiftSteps, List.map_cons]
      change (k + (t - k), Delta) ::
          lemma79ShiftSteps k (lemma79LocalSteps k rest) =
        (t, Delta) :: rest
      rw [ih htail, Nat.add_sub_of_le hhead]

/-- The final stopping pair is shifted pointwise. -/
theorem lemma79StoppingLast?_shiftSteps
    (k : ℕ) (steps : List (ℕ × TaoSection7Triangle)) :
    TaoSection7Case3StoppingLast? (lemma79ShiftSteps k steps) =
      (TaoSection7Case3StoppingLast? steps).map
        (fun step => (k + step.1, step.2)) := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      cases rest with
      | nil => simp [lemma79ShiftSteps, TaoSection7Case3StoppingLast?]
      | cons next rest =>
          simpa [lemma79ShiftSteps, TaoSection7Case3StoppingLast?] using ih

/-- Localized times inherit an upper horizon after subtracting their lower base. -/
theorem lemma79LocalSteps_all_lt_sub
    (k C : ℕ) (steps : List (ℕ × TaoSection7Triangle))
    (hlow : ∀ step ∈ steps, k ≤ step.1)
    (hupp : ∀ step ∈ steps, step.1 < C)
    (localStep : ℕ × TaoSection7Triangle)
    (hlocal : localStep ∈ lemma79LocalSteps k steps) :
    localStep.1 < C - k := by
  induction steps generalizing localStep with
  | nil => simp [lemma79LocalSteps] at hlocal
  | cons step rest ih =>
      rcases step with ⟨t, Delta⟩
      have hkt : k ≤ t := hlow (t, Delta) (by simp)
      have htC : t < C := hupp (t, Delta) (by simp)
      have hlowRest : ∀ s ∈ rest, k ≤ s.1 := by
        intro s hs
        exact hlow s (by simp [hs])
      have huppRest : ∀ s ∈ rest, s.1 < C := by
        intro s hs
        exact hupp s (by simp [hs])
      simp only [lemma79LocalSteps, List.mem_cons] at hlocal
      rcases hlocal with rfl | hlocal
      · omega
      · exact ih hlowRest huppRest localStep hlocal

/-- Generic path viewed from global time `k`. -/
def lemma79RestartPointAt
    (pointAt : ℕ -> TaoSection7Point) (k u : ℕ) : TaoSection7Point :=
  pointAt (k + u)

/-- First post-exit hits are invariant under adding `k` to both times. -/
theorem lemma79FirstAfterTriangleHitFrom_restart_iff
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (old : TaoSection7Triangle) (k q t : ℕ) :
    TaoSection7Case3FirstAfterTriangleHitFrom
        (lemma79RestartPointAt pointAt k) family old q t ↔
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old (k + q) (k + t) := by
  constructor
  · rintro ⟨hqt, hhit, hminimal⟩
    refine ⟨by omega, ?_, ?_⟩
    · simpa [TaoSection7Case3AfterTriangleHit,
        lemma79RestartPointAt] using hhit
    · intro s hqs hst hhitS
      have hks : k ≤ s := by omega
      let u := s - k
      have hku : k + u = s := Nat.add_sub_of_le hks
      apply hminimal u (by omega) (by omega)
      simpa [TaoSection7Case3AfterTriangleHit,
        lemma79RestartPointAt, hku] using hhitS
  · rintro ⟨hqt, hhit, hminimal⟩
    refine ⟨by omega, ?_, ?_⟩
    · simpa [TaoSection7Case3AfterTriangleHit,
        lemma79RestartPointAt] using hhit
    · intro u hqu hut hhitU
      apply hminimal (k + u) (by omega) (by omega)
      simpa [TaoSection7Case3AfterTriangleHit,
        lemma79RestartPointAt] using hhitU

/-- Localize one stopping transition whose base time is at least `k`. -/
theorem lemma79StoppingTransition_localize
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old Gamma : TaoSection7Triangle} {k q first : ℕ}
    (hkq : k ≤ q)
    (hstep : TaoSection7Case3StoppingTransition
      pointAt family q old first Gamma) :
    TaoSection7Case3StoppingTransition
      (lemma79RestartPointAt pointAt k) family
      (q - k) old (first - k) Gamma := by
  have hkfirst : k ≤ first :=
    hkq.trans (Nat.le_of_lt hstep.first_after_exit.1)
  have hglobal :
      TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old
        (k + (q - k)) (k + (first - k)) := by
    simpa [Nat.add_sub_of_le hkq, Nat.add_sub_of_le hkfirst] using
      hstep.first_after_exit
  refine
    { first_after_exit :=
        (lemma79FirstAfterTriangleHitFrom_restart_iff
          pointAt family old k (q - k) (first - k)).2 hglobal
      new_mem_family := hstep.new_mem_family
      new_mem := ?_
      new_ne_old := hstep.new_ne_old }
  simpa [lemma79RestartPointAt, Nat.add_sub_of_le hkfirst] using
    hstep.new_mem

/-- Every time in a stopping tail is strictly after its base time. -/
theorem lemma79StoppingTail_base_lt_of_mem
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (htail : TaoSection7Case3StoppingTail pointAt family q old steps) :
    ∀ step ∈ steps, q < step.1 := by
  induction htail with
  | nil => simp
  | @cons q first old Gamma rest hstep htail ih =>
      intro step hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hstep.first_after_exit.1
      · exact hstep.first_after_exit.1.trans (ih step hmem)

/-- Localize an entire stopping tail whose base time is at least `k`. -/
theorem lemma79StoppingTail_localize
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {k q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hkq : k ≤ q)
    (htail : TaoSection7Case3StoppingTail pointAt family q old steps) :
    TaoSection7Case3StoppingTail
      (lemma79RestartPointAt pointAt k) family
      (q - k) old (lemma79LocalSteps k steps) := by
  induction htail with
  | nil q old =>
      simpa [lemma79LocalSteps] using
        TaoSection7Case3StoppingTail.nil
          (pointAt := lemma79RestartPointAt pointAt k)
          (family := family) (q - k) old
  | @cons q first old Gamma rest hstep htail ih =>
      have hkfirst : k ≤ first :=
        hkq.trans (Nat.le_of_lt hstep.first_after_exit.1)
      exact TaoSection7Case3StoppingTail.cons
        (lemma79StoppingTransition_localize hkq hstep) (ih hkfirst)

/-- Rebase the tail of a bounded trace whose second stop occurs at global time `k`. -/
theorem lemma79BoundedInclusiveTrace_rebase_second
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {C p k : ℕ}
    {Delta Gamma : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htrace : Lemma79BoundedInclusiveTrace pointAt family C
      ((p, Delta) :: (k, Gamma) :: rest)) :
    Lemma79BoundedInclusiveTrace
      (lemma79RestartPointAt pointAt k) family (C - k)
      ((0, Gamma) :: lemma79LocalSteps k rest) := by
  have htail0 : TaoSection7Case3StoppingTail
      pointAt family p Delta ((k, Gamma) :: rest) := by
    cases htrace.trace_prefix with
    | cons _ _ _ htail => exact htail
  have hstep := TaoSection7Case3StoppingTail.head_step htail0
  have htail := TaoSection7Case3StoppingTail.tail htail0
  have htailLocal : TaoSection7Case3StoppingTail
      (lemma79RestartPointAt pointAt k) family 0 Gamma
      (lemma79LocalSteps k rest) := by
    simpa using
      lemma79StoppingTail_localize (k := k) (q := k) le_rfl htail
  have hfirstLocal : Lemma79FirstTriangleHitFromZero
      (lemma79RestartPointAt pointAt k) family 0 := by
    apply lemma79FirstTriangleHitFromZero_zero_iff.2
    exact ⟨Gamma, hstep.new_mem_family, by
      simpa [lemma79RestartPointAt] using hstep.new_mem⟩
  have hprefixLocal : Lemma79InclusiveStoppingPrefix
      (lemma79RestartPointAt pointAt k) family
      ((0, Gamma) :: lemma79LocalSteps k rest) :=
    Lemma79InclusiveStoppingPrefix.cons
      hfirstLocal hstep.new_mem_family
      (by simpa [lemma79RestartPointAt] using hstep.new_mem)
      htailLocal
  have hlow : ∀ step ∈ ((k, Gamma) :: rest), k ≤ step.1 := by
    intro step hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact le_rfl
    · exact Nat.le_of_lt
        (lemma79StoppingTail_base_lt_of_mem htail step hmem)
  have hupp : ∀ step ∈ ((k, Gamma) :: rest), step.1 < C := by
    intro step hmem
    exact htrace.all_stop_lt step (by simp [hmem])
  refine
    { trace_prefix := hprefixLocal
      all_stop_lt := ?_
      terminal_empty := ?_
      terminal_last := ?_ }
  · intro step hmem
    apply lemma79LocalSteps_all_lt_sub k C ((k, Gamma) :: rest)
      hlow hupp step
    simpa [lemma79LocalSteps] using hmem
  · intro hnil
    simp at hnil
  · intro last hlast q hlast_q hqC
    have hshift : lemma79ShiftSteps k
        ((0, Gamma) :: lemma79LocalSteps k rest) =
        (k, Gamma) :: rest := by
      simpa [lemma79LocalSteps] using
        lemma79ShiftSteps_localSteps_of_forall_le
          k ((k, Gamma) :: rest) hlow
    have hlastTail :
        TaoSection7Case3StoppingLast? ((k, Gamma) :: rest) =
          some (k + last.1, last.2) := by
      have hmap := lemma79StoppingLast?_shiftSteps k
        ((0, Gamma) :: lemma79LocalSteps k rest)
      rw [hshift] at hmap
      rw [hlast] at hmap
      simpa using hmap
    have hlastFull :
        TaoSection7Case3StoppingLast?
          ((p, Delta) :: (k, Gamma) :: rest) =
          some (k + last.1, last.2) := by
      simpa [TaoSection7Case3StoppingLast?] using hlastTail
    have hno := htrace.terminal_last
      (k + last.1, last.2) hlastFull (k + q) (by omega) (by omega)
    intro hafter
    apply hno
    simpa [TaoSection7Case3AfterTriangleHit,
      lemma79RestartPointAt] using hafter

/-- The rebased active tail is the canonical restarted cutoff trace. -/
theorem lemma79CutoffTrace_rebase_second
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {C p k : ℕ}
    {Delta Gamma : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace : Lemma79BoundedInclusiveTrace pointAt family C
      ((p, Delta) :: (k, Gamma) :: rest)) :
    (0, Gamma) :: lemma79LocalSteps k rest =
      lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k) family (C - k) := by
  exact Lemma79BoundedInclusiveTrace.steps_eq_of_pairwiseDisjoint
    hpair (lemma79BoundedInclusiveTrace_rebase_second htrace)
      (lemma79CutoffTrace_spec
        (lemma79RestartPointAt pointAt k) family (C - k))

/-- The active global tail is the time shift of the canonical restarted trace. -/
theorem lemma79CutoffTrace_tail_eq_shift_restart
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {C p k : ℕ}
    {Delta Gamma : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace : Lemma79BoundedInclusiveTrace pointAt family C
      ((p, Delta) :: (k, Gamma) :: rest)) :
    (k, Gamma) :: rest =
      lemma79ShiftSteps k
        (lemma79CutoffTrace
          (lemma79RestartPointAt pointAt k) family (C - k)) := by
  have htail0 : TaoSection7Case3StoppingTail
      pointAt family p Delta ((k, Gamma) :: rest) := by
    cases htrace.trace_prefix with
    | cons _ _ _ htail => exact htail
  have htail := TaoSection7Case3StoppingTail.tail htail0
  have hlow : ∀ step ∈ ((k, Gamma) :: rest), k ≤ step.1 := by
    intro step hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact le_rfl
    · exact Nat.le_of_lt
        (lemma79StoppingTail_base_lt_of_mem htail step hmem)
  have hshift : lemma79ShiftSteps k
      ((0, Gamma) :: lemma79LocalSteps k rest) =
      (k, Gamma) :: rest := by
    simpa [lemma79LocalSteps] using
      lemma79ShiftSteps_localSteps_of_forall_le
        k ((k, Gamma) :: rest) hlow
  calc
    (k, Gamma) :: rest =
        lemma79ShiftSteps k
          ((0, Gamma) :: lemma79LocalSteps k rest) := hshift.symm
    _ = lemma79ShiftSteps k
          (lemma79CutoffTrace
            (lemma79RestartPointAt pointAt k) family (C - k)) := by
        rw [lemma79CutoffTrace_rebase_second hpair htrace]

/-- Active-tail stopping counts agree with the canonical restarted trace. -/
theorem lemma79CutoffTrace_tail_r_eq_restart
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {C p k : ℕ}
    {Delta Gamma : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace : Lemma79BoundedInclusiveTrace pointAt family C
      ((p, Delta) :: (k, Gamma) :: rest)) :
    r ((k, Gamma) :: rest) =
      r (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k) family (C - k)) := by
  rw [lemma79CutoffTrace_tail_eq_shift_restart hpair htrace]
  exact lemma79_r_shiftSteps _ _

/-- Active-tail endpoint accessors are the shifted restarted accessors. -/
theorem lemma79CutoffTrace_tail_tR?_eq_restart
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {C p k R : ℕ}
    {Delta Gamma : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace : Lemma79BoundedInclusiveTrace pointAt family C
      ((p, Delta) :: (k, Gamma) :: rest)) :
    tR? ((k, Gamma) :: rest) R =
      (tR? (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k) family (C - k)) R).map
          (fun t => k + t) := by
  rw [lemma79CutoffTrace_tail_eq_shift_restart hpair htrace]
  exact lemma79_tR?_shiftSteps _ _ _

/-- A canonical trace may be padded across a later horizon containing no hits. -/
theorem lemma79CutoffTrace_eq_of_noHit_ge
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {H H' : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hle : H ≤ H')
    (hno : ∀ q : ℕ, H ≤ q ->
      ¬ TaoSection7Case3TriangleHit pointAt family q) :
    lemma79CutoffTrace pointAt family H =
      lemma79CutoffTrace pointAt family H' := by
  have hsmall := lemma79CutoffTrace_spec pointAt family H
  have hglobal :=
    lemma79BoundedInclusiveTrace_complete_of_noHit_ge hsmall hno
  have hlarge : Lemma79BoundedInclusiveTrace pointAt family H'
      (lemma79CutoffTrace pointAt family H) :=
    { trace_prefix := hsmall.trace_prefix
      all_stop_lt := by
        intro step hmem
        exact (hsmall.all_stop_lt step hmem).trans_le hle
      terminal_empty := by
        intro hnil q _hq
        exact hglobal.1 hnil q
      terminal_last := by
        intro last hlast q hlast_q _hq
        exact hglobal.2 last hlast q hlast_q }
  exact Lemma79BoundedInclusiveTrace.steps_eq_of_pairwiseDisjoint
    hpair hlarge (lemma79CutoffTrace_spec pointAt family H')

/-- The restarted Hold trace can be padded from `C-k` back to cutoff `C`. -/
theorem lemma79HoldPathCutoffTrace_restart_padding
    {n C k : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hlen : C ≤ full.length) :
    lemma79CutoffTrace
        (lemma79RestartPointAt
          (lemma79HoldPathPointAt start full) k) family (C - k) =
      lemma79CutoffTrace
        (lemma79RestartPointAt
          (lemma79HoldPathPointAt start full) k) family C := by
  apply lemma79CutoffTrace_eq_of_noHit_ge hpair (Nat.sub_le C k)
  intro q hq
  have hglobal := lemma79HoldPath_noTriangleHit_ge_cutoff
    (start := start) (full := full) hcover hlen (k + q) (by omega)
  simpa [TaoSection7Case3TriangleHit, lemma79RestartPointAt] using hglobal

/-- The active Hold tail is the shifted restarted trace at the canonical cutoff. -/
theorem lemma79HoldPathCutoffTrace_tail_eq_shift_restart_padded
    {n C p k : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {Delta Gamma : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hlen : C ≤ full.length)
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79HoldPathPointAt start full) family C
      ((p, Delta) :: (k, Gamma) :: rest)) :
    (k, Gamma) :: rest =
      lemma79ShiftSteps k
        (lemma79CutoffTrace
          (lemma79RestartPointAt
            (lemma79HoldPathPointAt start full) k) family C) := by
  calc
    (k, Gamma) :: rest =
        lemma79ShiftSteps k
          (lemma79CutoffTrace
            (lemma79RestartPointAt
              (lemma79HoldPathPointAt start full) k) family (C - k)) :=
      lemma79CutoffTrace_tail_eq_shift_restart hpair htrace
    _ = lemma79ShiftSteps k
          (lemma79CutoffTrace
            (lemma79RestartPointAt
              (lemma79HoldPathPointAt start full) k) family C) := by
      rw [lemma79HoldPathCutoffTrace_restart_padding hpair hcover hlen]

/-- Restarting after `k` Hold increments rebases local time onto global time. -/
theorem lemma79HoldPathPointAt_drop_add
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (k u : ℕ) :
    lemma79HoldPathPointAt
        (taoSection7RenewalPathPoint start full k)
        (full.drop k) u =
      lemma79HoldPathPointAt start full (k + u) := by
  apply congrArg TaoSection7RenewalPoint.toPoint
  exact taoSection7RenewalPathPoint_drop_add start full k u

/-- Hold path viewed from the endpoint reached at global time `k`. -/
def lemma79HoldPathRestartPointAt
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (k u : ℕ) : TaoSection7Point :=
  lemma79HoldPathPointAt
    (taoSection7RenewalPathPoint start full k) (full.drop k) u

@[simp] theorem lemma79HoldPathRestartPointAt_eq
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (k u : ℕ) :
    lemma79HoldPathRestartPointAt start full k u =
      lemma79HoldPathPointAt start full (k + u) := by
  exact lemma79HoldPathPointAt_drop_add start full k u

/-- Adding one endpoint extends the positive-time count by its indicator. -/
theorem lemma79PositiveWhiteCount_succ
    (W : ℕ -> Prop) [DecidablePred W] (t : ℕ) :
    taoSection7Case3PositiveWhiteCount W (t + 1) =
      taoSection7Case3PositiveWhiteCount W t +
        (if W (t + 1) then 1 else 0) := by
  unfold taoSection7Case3PositiveWhiteCount
  rw [Finset.sum_Icc_succ_top]
  omega

/-- Positive-time counting splits at `k`, with restarted local time beginning at `1`. -/
theorem lemma79PositiveWhiteCount_add
    (W : ℕ -> Prop) [DecidablePred W] (k t : ℕ) :
    taoSection7Case3PositiveWhiteCount W (k + t) =
      taoSection7Case3PositiveWhiteCount W k +
        taoSection7Case3PositiveWhiteCount (fun u => W (k + u)) t := by
  induction t with
  | zero => simp [taoSection7Case3PositiveWhiteCount]
  | succ t ih =>
      calc
        taoSection7Case3PositiveWhiteCount W (k + (t + 1)) =
            taoSection7Case3PositiveWhiteCount W (k + t) +
              (if W (k + t + 1) then 1 else 0) := by
                simpa [Nat.add_assoc] using
                  lemma79PositiveWhiteCount_succ W (k + t)
        _ = (taoSection7Case3PositiveWhiteCount W k +
              taoSection7Case3PositiveWhiteCount (fun u => W (k + u)) t) +
              (if W (k + t + 1) then 1 else 0) := by rw [ih]
        _ = taoSection7Case3PositiveWhiteCount W k +
              (taoSection7Case3PositiveWhiteCount (fun u => W (k + u)) t +
                (if W (k + (t + 1)) then 1 else 0)) := by
                  simp [Nat.add_assoc]
        _ = taoSection7Case3PositiveWhiteCount W k +
              taoSection7Case3PositiveWhiteCount
                (fun u => W (k + u)) (t + 1) := by
                  rw [lemma79PositiveWhiteCount_succ]

/-- The cutoff-white count obeys the same positive-time restart split. -/
theorem lemma79CutoffWhiteCount_add
    (pointAt : ℕ -> TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C k t : ℕ) :
    lemma79CutoffWhiteCount pointAt n xi epsilon C (k + t) =
      lemma79CutoffWhiteCount pointAt n xi epsilon C k +
        lemma79CutoffWhiteCount
          (fun u => pointAt (k + u)) n xi epsilon C t := by
  simpa [lemma79CutoffWhiteCount, taoSection7Case3PositiveWhiteCount] using
    lemma79PositiveWhiteCount_add
      (fun q =>
        taoSection7SourceWhiteWCutoff n xi epsilon C
          ((pointAt q).j : ℕ) (pointAt q).l) k t

/-- Cutoff-white counting splits between a Hold prefix and its restarted path. -/
theorem lemma79HoldPathCutoffWhiteCount_restart_add
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C k t : ℕ) :
    lemma79CutoffWhiteCount
        (lemma79HoldPathPointAt start full) n xi epsilon C (k + t) =
      lemma79CutoffWhiteCount
          (lemma79HoldPathPointAt start full) n xi epsilon C k +
        lemma79CutoffWhiteCount
          (lemma79HoldPathRestartPointAt start full k)
          n xi epsilon C t := by
  rw [lemma79CutoffWhiteCount_add]
  apply congrArg
    (fun count =>
      lemma79CutoffWhiteCount
          (lemma79HoldPathPointAt start full) n xi epsilon C k + count)
  apply lemma79CutoffWhiteCount_congr
  intro q _hq
  exact (lemma79HoldPathRestartPointAt_eq start full k q).symm

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
