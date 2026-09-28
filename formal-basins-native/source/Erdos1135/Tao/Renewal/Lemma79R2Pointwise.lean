import Erdos1135.Tao.Renewal.Lemma79Recurrence

/-!
# Lemma 7.9 Killed R=2 Pointwise Bounds

This proof leaf supplies the deterministic bounds consumed after the canonical
first-exit endpoint law.  It makes the restarted `R=1` estimate total and
shows that a cutoff-white first-exit endpoint forces one additional white
count in the repaired `R=2` recurrence.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A cutoff-white endpoint at positive time contributes at least one to the
positive-time white count through that endpoint. -/
theorem lemma79CutoffWhiteCount_one_le_of_white_at
    {pointAt : ℕ -> TaoSection7Point}
    {n C K : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hK : 0 < K)
    (hwhite :
      taoSection7SourceWhiteWCutoff n xi epsilon C
        ((pointAt K).j : ℕ) (pointAt K).l) :
    1 ≤ lemma79CutoffWhiteCount pointAt n xi epsilon C K := by
  unfold lemma79CutoffWhiteCount
  have hmem : K ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]
    omega
  have hsingle :
      (if taoSection7SourceWhiteWCutoff n xi epsilon C
          ((pointAt K).j : ℕ) (pointAt K).l then 1 else 0) ≤
        ∑ q ∈ Finset.Icc 1 K,
          if taoSection7SourceWhiteWCutoff n xi epsilon C
              ((pointAt q).j : ℕ) (pointAt q).l then 1 else 0 :=
    Finset.single_le_sum
      (f := fun q =>
        if taoSection7SourceWhiteWCutoff n xi epsilon C
            ((pointAt q).j : ℕ) (pointAt q).l then 1 else 0)
      (fun _ _ => Nat.zero_le _) hmem
  simpa [hwhite] using hsingle

/-- The repaired `R=1` statistic is bounded by `exp epsilon` on every Hold
path, including the empty-trace branch. -/
theorem lemma79HoldPathCutoffTailMoment_one_le_exp_total
    {n C : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C 1 ≤ Real.exp epsilon := by
  have htrace :=
    lemma79CutoffTrace_spec
      (lemma79HoldPathPointAt start full) family C
  cases hsteps :
      lemma79CutoffTrace
        (lemma79HoldPathPointAt start full) family C with
  | nil =>
      rw [lemma79CutoffTailMoment_eq_zero_of_trace_eq_nil
        (R := 1) (by omega) hsteps]
      exact (Real.exp_pos epsilon).le
  | cons step rest =>
      rcases step with ⟨p, old⟩
      rw [hsteps] at htrace
      exact lemma79HoldPathCutoffTailMoment_one_le_exp
        hpair hcover htrace

/-- Every certified first exit has the undiscounted `R=2` pointwise
envelope; no whiteness premise is required. -/
theorem lemma79HoldPathCutoffTailMoment_two_le_of_firstExit
    {n C p K : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
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
        family n xi epsilon C 2 ≤
      Real.exp (-(p.pred : ℝ) + 2 * epsilon) := by
  let count :=
    lemma79CutoffWhiteCount
      (lemma79HoldPathRestartPointAt start full p)
      n xi epsilon C K
  have hbase :
      lemma79CutoffTailMoment
          (lemma79HoldPathRestartPointAt start full (p + K))
          family n xi epsilon C 1 ≤ Real.exp epsilon := by
    simpa [lemma79HoldPathRestartPointAt] using
      (lemma79HoldPathCutoffTailMoment_one_le_exp_total
        (n := n) (C := C) (xi := xi) (epsilon := epsilon)
        (family := family)
        (start := taoSection7RenewalPathPoint start full (p + K))
        (full := full.drop (p + K)) hpair hcover)
  rw [lemma79HoldPathCutoffTailMoment_recurrence_firstEntry
    (R := 2) (by omega) hpair hcover hlen hexit htrace]
  calc
    Real.exp
          (-((p.pred + count : ℕ) : ℝ) + epsilon) *
        lemma79CutoffTailMoment
          (lemma79HoldPathRestartPointAt start full (p + K))
          family n xi epsilon C 1 ≤
      Real.exp (-((p.pred + count : ℕ) : ℝ) + epsilon) *
        Real.exp epsilon :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = Real.exp (-((p.pred + count : ℕ) : ℝ) + 2 * epsilon) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(p.pred : ℝ) + 2 * epsilon) := by
      apply Real.exp_le_exp.mpr
      have hcountReal : (0 : ℝ) ≤ (count : ℝ) := by positivity
      push_cast
      linarith

/-- A cutoff-white first-exit endpoint gives the discounted pointwise
`R=2` envelope. -/
theorem lemma79HoldPathCutoffTailMoment_two_le_of_firstExit_white
    {n C p K : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hlen : C ≤ full.length)
    (hexit : Lemma79FirstExitCertificate
      (lemma79HoldPathPointAt start full) old p (p + K))
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79HoldPathPointAt start full) family C
      ((p, old) :: rest))
    (hwhite :
      taoSection7SourceWhiteWCutoff n xi epsilon C
        ((lemma79HoldPathRestartPointAt start full p K).j : ℕ)
        (lemma79HoldPathRestartPointAt start full p K).l) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C 2 ≤
      Real.exp (-(p.pred : ℝ) + 2 * epsilon) * Real.exp (-1) := by
  let count :=
    lemma79CutoffWhiteCount
      (lemma79HoldPathRestartPointAt start full p)
      n xi epsilon C K
  have hK : 0 < K := by
    have := hexit.entry_lt_exit
    omega
  have hcount : 1 ≤ count :=
    lemma79CutoffWhiteCount_one_le_of_white_at hK hwhite
  have hbase :
      lemma79CutoffTailMoment
          (lemma79HoldPathRestartPointAt start full (p + K))
          family n xi epsilon C 1 ≤ Real.exp epsilon := by
    simpa [lemma79HoldPathRestartPointAt] using
      (lemma79HoldPathCutoffTailMoment_one_le_exp_total
        (n := n) (C := C) (xi := xi) (epsilon := epsilon)
        (family := family)
        (start := taoSection7RenewalPathPoint start full (p + K))
        (full := full.drop (p + K)) hpair hcover)
  rw [lemma79HoldPathCutoffTailMoment_recurrence_firstEntry
    (R := 2) (by omega) hpair hcover hlen hexit htrace]
  calc
    Real.exp
          (-((p.pred + count : ℕ) : ℝ) + epsilon) *
        lemma79CutoffTailMoment
          (lemma79HoldPathRestartPointAt start full (p + K))
          family n xi epsilon C 1 ≤
      Real.exp (-((p.pred + count : ℕ) : ℝ) + epsilon) *
        Real.exp epsilon :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = Real.exp (-((p.pred + count : ℕ) : ℝ) + 2 * epsilon) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(p.pred : ℝ) - 1 + 2 * epsilon) := by
      apply Real.exp_le_exp.mpr
      have hcountReal : (1 : ℝ) ≤ (count : ℝ) := by
        exact_mod_cast hcount
      push_cast
      linarith
    _ = Real.exp (-(p.pred : ℝ) + 2 * epsilon) * Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- One pointwise `R=2` envelope with the endpoint white discount exposed as
a two-valued weight. -/
theorem lemma79HoldPathCutoffTailMoment_two_le_firstExitWeight
    {n C p K : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
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
        family n xi epsilon C 2 ≤
      Real.exp (-(p.pred : ℝ) + 2 * epsilon) *
        (if taoSection7SourceWhiteWCutoff n xi epsilon C
            ((lemma79HoldPathRestartPointAt start full p K).j : ℕ)
            (lemma79HoldPathRestartPointAt start full p K).l
          then Real.exp (-1) else 1) := by
  by_cases hwhite :
      taoSection7SourceWhiteWCutoff n xi epsilon C
        ((lemma79HoldPathRestartPointAt start full p K).j : ℕ)
        (lemma79HoldPathRestartPointAt start full p K).l
  · rw [if_pos hwhite]
    exact lemma79HoldPathCutoffTailMoment_two_le_of_firstExit_white
      hpair hcover hlen hexit htrace hwhite
  · rw [if_neg hwhite, mul_one]
    exact lemma79HoldPathCutoffTailMoment_two_le_of_firstExit
      hpair hcover hlen hexit htrace

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
