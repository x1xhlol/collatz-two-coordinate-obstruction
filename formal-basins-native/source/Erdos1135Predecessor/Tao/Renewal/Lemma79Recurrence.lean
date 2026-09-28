/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79FirstEntryCount

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79_tR?_cons_succ_of_pos
    (step : ℕ × TaoSection7Triangle)
    (rest : List (ℕ × TaoSection7Triangle))
    {R : ℕ} (hR : 0 < R) :
    tR? (step :: rest) (R + 1) = tR? rest R := by
  cases R with
  | zero => omega
  | succ R => simp [tR?]

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
        simpa [lemma79RestartPointAt] using hcount
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

theorem lemma79RestartPointAt_holdPath_eq
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (k : ℕ) :
    lemma79RestartPointAt (lemma79HoldPathPointAt start full) k =
      lemma79HoldPathRestartPointAt start full k := by
  funext u
  exact (lemma79HoldPathRestartPointAt_eq start full k u).symm

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

end Erdos1135Predecessor
