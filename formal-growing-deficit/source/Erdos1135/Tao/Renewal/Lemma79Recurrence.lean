import Erdos1135.Tao.Renewal.Lemma79FirstEntryCount

/-!
# Lemma 7.9 Repaired Cutoff Recurrence

This module proves the deterministic positive-index recurrence for the repaired
cutoff statistic.  It consumes the checked first-exit tail equality rather than
assuming a restart identity for the statistic itself.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Removing one trace head decrements every later positive accessor index. -/
theorem lemma79_tR?_cons_succ_of_pos
    (step : ℕ × TaoSection7Triangle)
    (rest : List (ℕ × TaoSection7Triangle))
    {R : ℕ} (hR : 0 < R) :
    tR? (step :: rest) (R + 1) = tR? rest R := by
  cases R with
  | zero => omega
  | succ R => simp [tR?]

/-- Positive accessors are absent exactly off the survival branch. -/
theorem lemma79_tR?_eq_none_iff_r_lt
    {steps : List (ℕ × TaoSection7Triangle)} {R : ℕ}
    (hR : 0 < R) :
    tR? steps R = none ↔ r steps < R := by
  constructor
  · intro ht
    by_contra hnot
    have hle : R ≤ r steps := Nat.le_of_not_gt hnot
    have hisSome := (lemma79_tR?_isSome_iff hR).2 hle
    simp [ht] at hisSome
  · intro hlt
    cases ht : tR? steps R with
    | none => rfl
    | some t =>
        have hle : R ≤ r steps := by
          simpa [r] using tR?_some_length_le ht
        omega

/-- The nonempty global trace has one more stop than its restarted tail. -/
theorem lemma79CutoffTrace_r_eq_succ_restart_of_trace_eq_tail_eq
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {C p k1 : ℕ} {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htrace : lemma79CutoffTrace pointAt family C = (p, old) :: rest)
    (htail : rest = lemma79ShiftSteps k1
      (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k1) family C)) :
    r (lemma79CutoffTrace pointAt family C) =
      r (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k1) family C) + 1 := by
  rw [htrace, htail]
  simp [r, lemma79ShiftSteps_length]

/-- Survival of a nonempty trace is survival of the restarted trace at `R-1`. -/
theorem lemma79CutoffTrace_survival_iff_restart_of_trace_eq_tail_eq
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {C p k1 R : ℕ} {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hR : 2 ≤ R)
    (htrace : lemma79CutoffTrace pointAt family C = (p, old) :: rest)
    (htail : rest = lemma79ShiftSteps k1
      (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k1) family C)) :
    R ≤ r (lemma79CutoffTrace pointAt family C) ↔
      R - 1 ≤ r (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k1) family C) := by
  rw [lemma79CutoffTrace_r_eq_succ_restart_of_trace_eq_tail_eq
    htrace htail]
  omega

/--
Accessor shift obtained from a first-exit tail equality.  The option map keeps
absence distinct from a genuine restarted endpoint at time zero.
-/
theorem lemma79_tR?_eq_map_restart_of_trace_eq_tail_eq
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {C p k1 R : ℕ} {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hR : 2 ≤ R)
    (htrace : lemma79CutoffTrace pointAt family C = (p, old) :: rest)
    (htail : rest = lemma79ShiftSteps k1
      (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k1) family C)) :
    tR? (lemma79CutoffTrace pointAt family C) R =
      Option.map (fun t => k1 + t)
        (tR? (lemma79CutoffTrace
          (lemma79RestartPointAt pointAt k1) family C) (R - 1)) := by
  have hprev : 0 < R - 1 := by omega
  have hsucc : R - 1 + 1 = R := by omega
  calc
    tR? (lemma79CutoffTrace pointAt family C) R =
        tR? ((p, old) :: rest) R := by rw [htrace]
    _ = tR? rest (R - 1) := by
      rw [← hsucc]
      exact lemma79_tR?_cons_succ_of_pos (p, old) rest hprev
    _ = tR? (lemma79ShiftSteps k1
          (lemma79CutoffTrace
            (lemma79RestartPointAt pointAt k1) family C)) (R - 1) := by
      rw [htail]
    _ = Option.map (fun t => k1 + t)
          (tR? (lemma79CutoffTrace
            (lemma79RestartPointAt pointAt k1) family C) (R - 1)) :=
      lemma79_tR?_shiftSteps _ _ _

/-- A restarted time-zero endpoint becomes the absolute first-exit clock. -/
theorem lemma79_tR?_eq_some_exit_of_restart_some_zero
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {C p k1 R : ℕ} {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hR : 2 ≤ R)
    (htrace : lemma79CutoffTrace pointAt family C = (p, old) :: rest)
    (htail : rest = lemma79ShiftSteps k1
      (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k1) family C))
    (hzero : tR? (lemma79CutoffTrace
      (lemma79RestartPointAt pointAt k1) family C) (R - 1) = some 0) :
    tR? (lemma79CutoffTrace pointAt family C) R = some k1 := by
  rw [lemma79_tR?_eq_map_restart_of_trace_eq_tail_eq
    hR htrace htail, hzero]
  simp

/--
Pure recurrence algebra after the canonical global trace and its first-exit
tail have been identified.
-/
theorem lemma79CutoffTailMoment_recurrence_of_trace_eq_tail_eq
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C p k1 R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hR : 2 ≤ R)
    (htrace : lemma79CutoffTrace pointAt family C = (p, old) :: rest)
    (htail : rest = lemma79ShiftSteps k1
      (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k1) family C)) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C R =
      Real.exp
          (-(lemma79CutoffWhiteCount pointAt n xi epsilon C k1 : ℝ) +
            epsilon) *
        lemma79CutoffTailMoment
          (lemma79RestartPointAt pointAt k1)
          family n xi epsilon C (R - 1) := by
  have haccess := lemma79_tR?_eq_map_restart_of_trace_eq_tail_eq
    (pointAt := pointAt) (family := family) hR htrace htail
  cases hlocal : tR? (lemma79CutoffTrace
      (lemma79RestartPointAt pointAt k1) family C) (R - 1) with
  | none =>
      have hglobal : tR? (lemma79CutoffTrace pointAt family C) R = none := by
        simpa [hlocal] using haccess
      simp [lemma79CutoffTailMoment, hglobal, hlocal]
  | some t =>
      have hglobal : tR? (lemma79CutoffTrace pointAt family C) R =
          some (k1 + t) := by
        simpa [hlocal] using haccess
      have hcount := lemma79CutoffWhiteCount_add
        pointAt n xi epsilon C k1 t
      have hcount' :
          lemma79CutoffWhiteCount pointAt n xi epsilon C (k1 + t) =
            lemma79CutoffWhiteCount pointAt n xi epsilon C k1 +
              lemma79CutoffWhiteCount
                (lemma79RestartPointAt pointAt k1)
                n xi epsilon C t := by
        exact hcount
      rw [lemma79CutoffTailMoment_eq_exp_of_tR? hglobal,
        lemma79CutoffTailMoment_eq_exp_of_tR? hlocal,
        ← Real.exp_add]
      rw [hcount']
      congr 1
      push_cast
      have hR_eq : (R : ℝ) = (R - 1 : ℕ) + 1 := by
        have hR_nat : R = R - 1 + 1 := by omega
        exact_mod_cast hR_nat
      rw [hR_eq]
      ring

/-- The two point-function presentations of a restarted Hold path agree. -/
theorem lemma79RestartPointAt_holdPath_eq
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (k : ℕ) :
    lemma79RestartPointAt (lemma79HoldPathPointAt start full) k =
      lemma79HoldPathRestartPointAt start full k := by
  funext u
  exact (lemma79HoldPathRestartPointAt_eq start full k u).symm

/--
Hold-path repaired recurrence at the absolute first-exit clock.  This one
theorem covers active, singleton, and off-survival nonempty traces.
-/
theorem lemma79HoldPathCutoffTailMoment_recurrence
    {n C p k1 R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hR : 2 ≤ R)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hlen : C ≤ full.length)
    (hexit : Lemma79FirstExitCertificate
      (lemma79HoldPathPointAt start full) old p k1)
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79HoldPathPointAt start full) family C
      ((p, old) :: rest)) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C R =
      Real.exp
          (-(lemma79CutoffWhiteCount
              (lemma79HoldPathPointAt start full)
              n xi epsilon C k1 : ℝ) + epsilon) *
        lemma79CutoffTailMoment
          (lemma79HoldPathRestartPointAt start full k1)
          family n xi epsilon C (R - 1) := by
  have hcanonical : lemma79CutoffTrace
      (lemma79HoldPathPointAt start full) family C =
      (p, old) :: rest :=
    Lemma79BoundedInclusiveTrace.steps_eq_of_pairwiseDisjoint
      hpair (lemma79CutoffTrace_spec
        (lemma79HoldPathPointAt start full) family C) htrace
  have htail :=
    lemma79HoldPathCutoffTrace_tail_eq_shift_firstExit_padded
      hpair hcover hlen hexit htrace
  have hrec :=
    lemma79CutoffTailMoment_recurrence_of_trace_eq_tail_eq
      (pointAt := lemma79HoldPathPointAt start full)
      (family := family) (n := n) (xi := xi) (epsilon := epsilon)
      hR hcanonical htail
  rw [lemma79RestartPointAt_holdPath_eq start full k1] at hrec
  exact hrec

/--
Source-facing recurrence with the prefix count split into pre-entry whites and
the entry-relative first-exit block.
-/
theorem lemma79HoldPathCutoffTailMoment_recurrence_firstEntry
    {n C p K R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hR : 2 ≤ R)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hlen : C ≤ full.length)
    (hexit : Lemma79FirstExitCertificate
      (lemma79HoldPathPointAt start full) old p (p + K))
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79HoldPathPointAt start full) family C
      ((p, old) :: rest)) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C R =
      Real.exp
          (-((p.pred + lemma79CutoffWhiteCount
              (lemma79HoldPathRestartPointAt start full p)
              n xi epsilon C K : ℕ) : ℝ) + epsilon) *
        lemma79CutoffTailMoment
          (lemma79HoldPathRestartPointAt start full (p + K))
          family n xi epsilon C (R - 1) := by
  have hfirst := htrace.trace_prefix.head_first_hit
  have hcount := lemma79HoldPathCutoffWhiteCount_firstEntry_add
    hcover hfirst K
  rw [← hcount]
  exact lemma79HoldPathCutoffTailMoment_recurrence
    hR hpair hcover hlen hexit htrace

/-- Exact repaired base case on a nonempty Hold trace. -/
theorem lemma79HoldPathCutoffTailMoment_one_firstEntry
    {n C p : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79HoldPathPointAt start full) family C
      ((p, old) :: rest)) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C 1 =
      Real.exp (-(p.pred : ℝ) + epsilon) := by
  have hcanonical : lemma79CutoffTrace
      (lemma79HoldPathPointAt start full) family C =
      (p, old) :: rest :=
    Lemma79BoundedInclusiveTrace.steps_eq_of_pairwiseDisjoint
      hpair (lemma79CutoffTrace_spec
        (lemma79HoldPathPointAt start full) family C) htrace
  have hfirst := htrace.trace_prefix.head_first_hit
  have hcount := lemma79HoldPathCutoffWhiteCount_firstEntry hcover hfirst
  simp [lemma79CutoffTailMoment, hcanonical, hcount, tR?]

/-- The repaired base case is bounded by `exp epsilon`. -/
theorem lemma79HoldPathCutoffTailMoment_one_le_exp
    {n C p : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79HoldPathPointAt start full) family C
      ((p, old) :: rest)) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C 1 ≤ Real.exp epsilon := by
  rw [lemma79HoldPathCutoffTailMoment_one_firstEntry hpair hcover htrace]
  apply Real.exp_le_exp.mpr
  have hpred : 0 ≤ (p.pred : ℝ) := by positivity
  linarith

/-- Every positive repaired statistic vanishes on an empty canonical trace. -/
theorem lemma79CutoffTailMoment_eq_zero_of_trace_eq_nil
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hR : 0 < R)
    (htrace : lemma79CutoffTrace pointAt family C = []) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C R = 0 := by
  apply lemma79CutoffTailMoment_eq_zero_of_r_lt
  simp [htrace, r, hR]

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
