import Erdos1135.Tao.Renewal.Lemma79CutoffLocality
import Erdos1135.Tao.Fourier.Section7SourceDomain

/-!
# Lemma 7.9 Repaired Cutoff Statistic

This proof leaf defines the cutoff-gated statistic used by the repaired
Lemma 7.9 induction.  The statistic matches directly on the one-based `tR?`
accessor, so a genuine time-zero endpoint remains distinct from absence.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Canonical zero-inclusive stopping trace at cutoff `C`. -/
noncomputable def lemma79CutoffTrace
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) (C : ℕ) :
    List (ℕ × TaoSection7Triangle) :=
  lemma79BoundedInclusiveTraceSteps pointAt family C

/-- The canonical cutoff trace satisfies its bounded chronological contract. -/
theorem lemma79CutoffTrace_spec
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) (C : ℕ) :
    Lemma79BoundedInclusiveTrace pointAt family C
      (lemma79CutoffTrace pointAt family C) := by
  simpa [lemma79CutoffTrace] using
    lemma79BoundedInclusiveTraceSteps_spec pointAt family C

/-- For positive indices, `tR?` is present exactly on the survival branch. -/
theorem lemma79_tR?_isSome_iff
    {steps : List (ℕ × TaoSection7Triangle)} {R : ℕ}
    (hR : 0 < R) :
    (tR? steps R).isSome = true ↔ R ≤ r steps := by
  induction steps generalizing R with
  | nil => simp [tR?, r, Nat.ne_of_gt hR]
  | cons step rest ih =>
      cases R with
      | zero => omega
      | succ Rpred =>
          cases Rpred with
          | zero => simp [tR?, r]
          | succ Rtail =>
              have hRtail : 0 < Rtail + 1 := by omega
              simpa [tR?, r] using ih (R := Rtail + 1) hRtail

/-- Complete support characterization for the source stopping-time accessor. -/
theorem lemma79_tR?_isSome_iff_pos_and_le_r
    {steps : List (ℕ × TaoSection7Triangle)} {R : ℕ} :
    (tR? steps R).isSome = true ↔ 0 < R ∧ R ≤ r steps := by
  constructor
  · intro hisSome
    have hR : 0 < R := tR?_isSome_pos hisSome
    exact ⟨hR, (lemma79_tR?_isSome_iff hR).1 hisSome⟩
  · rintro ⟨hR, hle⟩
    exact (lemma79_tR?_isSome_iff hR).2 hle

/-- Positive survival supplies an endpoint without asserting that endpoint is positive. -/
theorem lemma79_tR?_exists_of_pos_le_r
    {steps : List (ℕ × TaoSection7Triangle)} {R : ℕ}
    (hR : 0 < R) (hle : R ≤ r steps) :
    ∃ t : ℕ, tR? steps R = some t := by
  have hisSome : (tR? steps R).isSome = true :=
    (lemma79_tR?_isSome_iff hR).2 hle
  cases ht : tR? steps R with
  | none => simp [ht] at hisSome
  | some t => exact ⟨t, rfl⟩

/-- Option-valued cutoff `t_min`; unlike `getD`, this preserves absence. -/
noncomputable def lemma79CutoffTMin?
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) (C R : ℕ) : Option ℕ :=
  let steps := lemma79CutoffTrace pointAt family C
  tR? steps (min (r steps) R)

/-- Legacy numeric projection of `lemma79CutoffTMin?`, for downstream adapters only. -/
noncomputable def lemma79CutoffTMinIndex
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) (C R : ℕ) : ℕ :=
  (lemma79CutoffTMin? pointAt family C R).getD 0

/-- Number of cutoff-gated source-white points at positive times through `t`. -/
noncomputable def lemma79CutoffWhiteCount
    (pointAt : ℕ -> TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C t : ℕ) : ℕ :=
  (Finset.Icc 1 t).sum fun q =>
    if taoSection7SourceWhiteWCutoff n xi epsilon C
        ((pointAt q).j : ℕ) (pointAt q).l then 1 else 0

/-- Repaired cutoff statistic `G_C`, zero exactly when the requested stop is absent. -/
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

@[simp] theorem lemma79CutoffTrace_zero
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    lemma79CutoffTrace pointAt family 0 = [] := by
  simp [lemma79CutoffTrace]

@[simp] theorem lemma79CutoffWhiteCount_zero
    (pointAt : ℕ -> TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (C : ℕ) :
    lemma79CutoffWhiteCount pointAt n xi epsilon C 0 = 0 := by
  simp [lemma79CutoffWhiteCount]

/-- The match-based cutoff statistic deliberately vanishes at `R = 0`. -/
@[simp] theorem lemma79CutoffTailMoment_zero
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (C : ℕ) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C 0 = 0 := by
  unfold lemma79CutoffTailMoment
  cases lemma79CutoffTrace pointAt family C <;> rfl

/-- A zero cutoff has an empty trace and hence zero statistic for every `R`. -/
@[simp] theorem lemma79CutoffTailMoment_cutoff_zero
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (R : ℕ) :
    lemma79CutoffTailMoment pointAt family n xi epsilon 0 R = 0 := by
  unfold lemma79CutoffTailMoment
  rw [lemma79CutoffTrace_zero]
  rfl

/-- On a present endpoint, the cutoff statistic is the intended exponential. -/
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

/-- A valid time-zero endpoint selects the exponential branch, not the zero branch. -/
theorem lemma79CutoffTailMoment_of_tR?_eq_some_zero
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (ht : tR? (lemma79CutoffTrace pointAt family C) R = some 0) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C R =
      Real.exp (epsilon * (R : ℝ)) := by
  simpa using lemma79CutoffTailMoment_eq_exp_of_tR? ht

/-- If the run has fewer than `R` stops, the cutoff statistic is zero. -/
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

/-- A present endpoint of the canonical bounded trace lies below its cutoff. -/
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

/-- The cutoff count depends only on path points through its endpoint. -/
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

/-- Trace equality and endpoint-local path equality preserve the cutoff statistic. -/
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
      simp [hcount]

/-- The canonical cutoff trace of a Hold path is determined by `full.take C`. -/
theorem lemma79HoldPathCutoffTrace_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {C : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79CutoffTrace (lemma79HoldPathPointAt start full) family C =
      lemma79CutoffTrace
        (lemma79HoldPathPointAt start (full.take C)) family C := by
  exact lemma79HoldPathInclusiveTraceSteps_take hpair

/-- The cutoff stopping count is determined by `full.take C`. -/
theorem lemma79HoldPathCutoffTrace_r_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {C : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    r (lemma79CutoffTrace (lemma79HoldPathPointAt start full) family C) =
      r (lemma79CutoffTrace
        (lemma79HoldPathPointAt start (full.take C)) family C) := by
  rw [lemma79HoldPathCutoffTrace_take hpair]

/-- Every one-based cutoff endpoint accessor is determined by `full.take C`. -/
theorem lemma79HoldPathCutoffTrace_tR?_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {C R : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    tR? (lemma79CutoffTrace (lemma79HoldPathPointAt start full) family C) R =
      tR? (lemma79CutoffTrace
        (lemma79HoldPathPointAt start (full.take C)) family C) R := by
  rw [lemma79HoldPathCutoffTrace_take hpair]

/-- The option-valued cutoff `t_min` is determined by `full.take C`. -/
theorem lemma79HoldPathCutoffTMin?_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {C R : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79CutoffTMin? (lemma79HoldPathPointAt start full) family C R =
      lemma79CutoffTMin?
        (lemma79HoldPathPointAt start (full.take C)) family C R := by
  simp only [lemma79CutoffTMin?]
  rw [lemma79HoldPathCutoffTrace_take hpair]

/-- The downstream numeric `t_min` projection is determined by `full.take C`. -/
theorem lemma79HoldPathCutoffTMinIndex_take
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {C R : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79CutoffTMinIndex
        (lemma79HoldPathPointAt start full) family C R =
      lemma79CutoffTMinIndex
        (lemma79HoldPathPointAt start (full.take C)) family C R := by
  simp only [lemma79CutoffTMinIndex]
  rw [lemma79HoldPathCutoffTMin?_take hpair]

/-- The repaired cutoff statistic is determined by the canonical Hold prefix. -/
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
end Erdos1135
