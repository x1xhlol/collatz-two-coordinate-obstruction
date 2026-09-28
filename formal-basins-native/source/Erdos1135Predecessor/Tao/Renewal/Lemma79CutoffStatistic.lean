/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourceDomain
import Erdos1135Predecessor.Tao.Renewal.Lemma79CutoffLocality

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def lemma79CutoffTrace
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) (C : ℕ) :
    List (ℕ × TaoSection7Triangle) :=
  lemma79BoundedInclusiveTraceSteps pointAt family C

theorem lemma79CutoffTrace_spec
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) (C : ℕ) :
    Lemma79BoundedInclusiveTrace pointAt family C
      (lemma79CutoffTrace pointAt family C) := by
  simpa [lemma79CutoffTrace] using
    lemma79BoundedInclusiveTraceSteps_spec pointAt family C

noncomputable def lemma79CutoffWhiteCount
    (pointAt : ℕ -> TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C t : ℕ) : ℕ :=
  (Finset.Icc 1 t).sum fun q =>
    if taoSection7SourceWhiteWCutoff n xi epsilon C
        ((pointAt q).j : ℕ) (pointAt q).l then 1 else 0

noncomputable def lemma79CutoffTailMoment
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C R : ℕ) : ℝ :=
  match tR? (lemma79CutoffTrace pointAt family C) R with
  | none => 0
  | some t =>
      Real.exp
        (-(lemma79CutoffWhiteCount pointAt n xi epsilon C t : ℝ) +
          epsilon * (R : ℝ))

@[simp] theorem lemma79CutoffTailMoment_zero
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (C : ℕ) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C 0 = 0 := by
  unfold lemma79CutoffTailMoment
  cases lemma79CutoffTrace pointAt family C <;> rfl

theorem lemma79CutoffTailMoment_eq_exp_of_tR?
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C R t : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (ht : tR? (lemma79CutoffTrace pointAt family C) R = some t) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C R =
      Real.exp
        (-(lemma79CutoffWhiteCount pointAt n xi epsilon C t : ℝ) +
          epsilon * (R : ℝ)) := by
  simp [lemma79CutoffTailMoment, ht]

theorem lemma79CutoffTailMoment_eq_zero_of_r_lt
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hlt : r (lemma79CutoffTrace pointAt family C) < R) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C R = 0 := by
  cases ht : tR? (lemma79CutoffTrace pointAt family C) R with
  | none => simp [lemma79CutoffTailMoment, ht]
  | some t =>
      have hle := tR?_some_length_le ht
      have : R ≤ r (lemma79CutoffTrace pointAt family C) := by
        simpa [r] using hle
      omega

theorem lemma79CutoffTrace_tR_lt
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle} {C R t : ℕ}
    (ht : tR? (lemma79CutoffTrace pointAt family C) R = some t) :
    t < C := by
  have hRpos : 0 < R := tR?_isSome_pos (by rw [ht]; rfl)
  have hRle : HasAtLeast (lemma79CutoffTrace pointAt family C) R := by
    simpa [HasAtLeast, r] using tR?_some_length_le ht
  rcases hasTWithinWindow_of_hasAtLeast_all_ltP
      hRpos hRle (lemma79CutoffTrace_spec pointAt family C).all_stop_lt with
    ⟨t', ht', ht'C⟩
  have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
  subst t'
  exact ht'C

theorem lemma79CutoffWhiteCount_congr
    {pointAt pointAt' : ℕ -> TaoSection7Point}
    {n C t : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hpoint : ∀ q : ℕ, q ≤ t -> pointAt q = pointAt' q) :
    lemma79CutoffWhiteCount pointAt n xi epsilon C t =
      lemma79CutoffWhiteCount pointAt' n xi epsilon C t := by
  unfold lemma79CutoffWhiteCount
  apply Finset.sum_congr rfl
  intro q hq
  rw [hpoint q (Finset.mem_Icc.mp hq).2]

theorem lemma79CutoffTailMoment_congr_of_trace_eq
    {pointAt pointAt' : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (htrace : lemma79CutoffTrace pointAt family C =
      lemma79CutoffTrace pointAt' family C)
    (hpoint :
      ∀ t : ℕ,
        tR? (lemma79CutoffTrace pointAt family C) R = some t ->
          ∀ q : ℕ, q ≤ t -> pointAt q = pointAt' q) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C R =
      lemma79CutoffTailMoment pointAt' family n xi epsilon C R := by
  unfold lemma79CutoffTailMoment
  rw [← htrace]
  cases ht : tR? (lemma79CutoffTrace pointAt family C) R with
  | none => rfl
  | some t =>
      have hcount := lemma79CutoffWhiteCount_congr
        (n := n) (xi := xi) (epsilon := epsilon) (C := C)
        (hpoint := hpoint t ht)
      simpa [hcount]

theorem lemma79HoldPathCutoffTrace_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {C : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79CutoffTrace (lemma79HoldPathPointAt start full) family C =
      lemma79CutoffTrace
        (lemma79HoldPathPointAt start (full.take C)) family C := by
  exact lemma79HoldPathInclusiveTraceSteps_take hpair

theorem lemma79HoldPathCutoffTailMoment_take
    {n C R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C R =
      lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start (full.take C))
        family n xi epsilon C R := by
  apply lemma79CutoffTailMoment_congr_of_trace_eq
    (lemma79HoldPathCutoffTrace_take hpair)
  intro t ht q hq
  have htC : t < C := lemma79CutoffTrace_tR_lt ht
  exact
    (lemma79HoldPathPointAt_take_eq_of_le start full (by omega)).symm

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
