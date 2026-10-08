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

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def lemma79ShiftSteps (k : ℕ)
    (steps : List (ℕ × TaoSection7Triangle)) :
    List (ℕ × TaoSection7Triangle) :=
  steps.map fun step => (k + step.1, step.2)

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

def lemma79RestartPointAt
    (pointAt : ℕ -> TaoSection7Point) (k u : ℕ) : TaoSection7Point :=
  pointAt (k + u)

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

theorem lemma79PositiveWhiteCount_succ
    (W : ℕ -> Prop) [DecidablePred W] (t : ℕ) :
    taoSection7Case3PositiveWhiteCount W (t + 1) =
      taoSection7Case3PositiveWhiteCount W t +
        (if W (t + 1) then 1 else 0) := by
  unfold taoSection7Case3PositiveWhiteCount
  rw [Finset.sum_Icc_succ_top]
  omega

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

end Erdos1135Predecessor
