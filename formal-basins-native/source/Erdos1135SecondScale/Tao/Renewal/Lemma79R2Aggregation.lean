/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79TailExpectationCore
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2Pointwise

/-!
# Lemma 7.9 Killed R=2 Native Key Aggregation

This proof leaf partitions a native nonnegative PMF expectation over exact key
fibers.  It also closes the absent first-entry key and reduces the global
killed `R=2` expectation to bounds on the complete semantic `some` fibers.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Weighted native expectation partition over the fibers of an arbitrary key. -/
theorem lemma79_pmfENNExpectation_partition_of_key
    {Omega Key : Type*} (mu : PMF Omega)
    (Parent : Set Omega) (key : Omega -> Key) (F : Omega -> ENNReal) :
    lemma79PMFENNExpectation mu (Parent.indicator F) =
      ∑' k, lemma79PMFENNExpectation mu
        ((lemma79KeyAtom Parent key k).indicator F) := by
  classical
  unfold lemma79PMFENNExpectation
  calc
    (∑' omega, mu omega * Parent.indicator F omega) =
        ∑' omega, ∑' k,
          mu omega *
            (lemma79KeyAtom Parent key k).indicator F omega := by
      apply tsum_congr
      intro omega
      by_cases hParent : omega ∈ Parent
      · rw [tsum_eq_single (key omega)]
        · simp [lemma79KeyAtom, Set.indicator, hParent]
        · intro k hne
          have hkey_ne : key omega ≠ k := fun h => hne h.symm
          simp [lemma79KeyAtom, Set.indicator, hParent, hkey_ne]
      · simp [lemma79KeyAtom, Set.indicator, hParent]
    _ = ∑' k, ∑' omega,
        mu omega *
          (lemma79KeyAtom Parent key k).indicator F omega := by
      rw [ENNReal.tsum_comm]

/-- Per-key native expectation bounds aggregate with the corresponding
unnormalized key masses. -/
theorem lemma79_pmfENNExpectation_le_mul_of_key
    {Omega Key : Type*} (mu : PMF Omega)
    (Parent : Set Omega) (key : Omega -> Key)
    (F : Omega -> ENNReal) (C : ENNReal)
    (hlocal : ∀ k,
      lemma79PMFENNExpectation mu
          ((lemma79KeyAtom Parent key k).indicator F) ≤
        mu.toOuterMeasure (lemma79KeyAtom Parent key k) * C) :
    lemma79PMFENNExpectation mu (Parent.indicator F) ≤
      mu.toOuterMeasure Parent * C := by
  rw [lemma79_pmfENNExpectation_partition_of_key]
  calc
    (∑' k, lemma79PMFENNExpectation mu
        ((lemma79KeyAtom Parent key k).indicator F)) ≤
        ∑' k, mu.toOuterMeasure (lemma79KeyAtom Parent key k) * C :=
      ENNReal.tsum_le_tsum hlocal
    _ = (∑' k, mu.toOuterMeasure (lemma79KeyAtom Parent key k)) * C := by
      rw [ENNReal.tsum_mul_right]
    _ = mu.toOuterMeasure Parent * C := by
      rw [← lemma79_pmfToOuterMeasure_partition_of_key]

/-- An absent bounded head key forces the repaired positive-index statistic to
vanish. -/
theorem lemma79CutoffTailMoment_eq_zero_of_headKey_eq_none
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hR : 0 < R)
    (hkey :
      lemma79BoundedInclusiveTraceHeadKey pointAt family C = none) :
    lemma79CutoffTailMoment
        pointAt family n xi epsilon C R = 0 := by
  have hhead :
      lemma79InclusiveTraceHeadKey pointAt
          (lemma79CutoffTrace pointAt family C) = none := by
    simpa [lemma79BoundedInclusiveTraceHeadKey, lemma79CutoffTrace] using hkey
  have htrace : lemma79CutoffTrace pointAt family C = [] :=
    (lemma79InclusiveTraceHeadKey_eq_none_iff
      pointAt (lemma79CutoffTrace pointAt family C)).1 hhead
  exact lemma79CutoffTailMoment_eq_zero_of_trace_eq_nil hR htrace

/-- First-entry key of one Hold sample at the fixed cutoff. -/
noncomputable def lemma79HoldPathHeadKey
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (C : ℕ)
    (full : List TaoSection7RenewalPoint) :
    Option (ℕ × TaoSection7Point) :=
  lemma79BoundedInclusiveTraceHeadKey
    (lemma79HoldPathPointAt start full) family C

/-- Native repaired cutoff statistic on one Hold sample. -/
noncomputable def lemma79HoldPathCutoffTailMomentENN
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C R : ℕ) (full : List TaoSection7RenewalPoint) : ENNReal :=
  ENNReal.ofReal
    (lemma79CutoffTailMoment
      (lemma79HoldPathPointAt start full)
      family n xi epsilon C R)

/-- Every positive repaired payload is zero on an absent-key sample. -/
theorem lemma79HoldPathCutoffTailMomentENN_eq_zero_of_headKey_none
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {n C R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {full : List TaoSection7RenewalPoint}
    (hR : 0 < R)
    (hkey : lemma79HoldPathHeadKey start family C full = none) :
    lemma79HoldPathCutoffTailMomentENN
        start family n xi epsilon C R full = 0 := by
  unfold lemma79HoldPathCutoffTailMomentENN
  rw [lemma79CutoffTailMoment_eq_zero_of_headKey_eq_none hR hkey]
  simp

/-- The complete absent-key fiber contributes zero expectation for every
positive repaired index. -/
theorem lemma79_holdList_cutoffTailMomentENN_noneKey_eq_zero
    (J : ℕ) (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (R : ℕ) (hR : 0 < R) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF J)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey start family J) none).indicator
            (lemma79HoldPathCutoffTailMomentENN
              start family n xi epsilon J R)) = 0 := by
  unfold lemma79PMFENNExpectation
  rw [ENNReal.tsum_eq_zero]
  intro full
  by_cases hmem :
      full ∈ lemma79KeyAtom Set.univ
        (lemma79HoldPathHeadKey start family J) none
  · have hkey :
        lemma79HoldPathHeadKey start family J full = none := hmem.2
    rw [Set.indicator_of_mem hmem,
      lemma79HoldPathCutoffTailMomentENN_eq_zero_of_headKey_none hR hkey,
      mul_zero]
  · simp [Set.indicator, hmem]

/-- Per-`some`-key native bounds aggregate to a global bound for every
positive repaired index. -/
theorem lemma79_holdList_cutoffTailMomentENN_le_of_someKey_bounds
    (J : ℕ) (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (R : ℕ) (hR : 0 < R) (D : ENNReal)
    (hsome : ∀ k : ℕ × TaoSection7Point,
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF J)
          ((lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey start family J) (some k)).indicator
              (lemma79HoldPathCutoffTailMomentENN
                start family n xi epsilon J R)) ≤
        (taoSection7HoldListPMF J).toOuterMeasure
            (lemma79KeyAtom Set.univ
              (lemma79HoldPathHeadKey start family J) (some k)) * D) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF J)
        (lemma79HoldPathCutoffTailMomentENN
          start family n xi epsilon J R) ≤ D := by
  have hlocal :
      ∀ k : Option (ℕ × TaoSection7Point),
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF J)
            ((lemma79KeyAtom Set.univ
              (lemma79HoldPathHeadKey start family J) k).indicator
                (lemma79HoldPathCutoffTailMomentENN
                  start family n xi epsilon J R)) ≤
          (taoSection7HoldListPMF J).toOuterMeasure
              (lemma79KeyAtom Set.univ
                (lemma79HoldPathHeadKey start family J) k) * D := by
    intro k
    cases k with
    | none =>
        rw [lemma79_holdList_cutoffTailMomentENN_noneKey_eq_zero
          J start family n xi epsilon R hR]
        exact bot_le
    | some k => exact hsome k
  have hagg :=
    lemma79_pmfENNExpectation_le_mul_of_key
      (taoSection7HoldListPMF J) Set.univ
      (lemma79HoldPathHeadKey start family J)
      (lemma79HoldPathCutoffTailMomentENN
        start family n xi epsilon J R) D hlocal
  have huniv :
      (taoSection7HoldListPMF J).toOuterMeasure Set.univ = 1 :=
    ((taoSection7HoldListPMF J).toOuterMeasure_apply_eq_one_iff Set.univ).2
      (Set.subset_univ _)
  simpa [huniv] using hagg

/-- The native killed `R=2` payload is zero on every absent-key sample. -/
theorem lemma79HoldPathCutoffTailMomentENN_two_eq_zero_of_headKey_none
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {n C : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {full : List TaoSection7RenewalPoint}
    (hkey : lemma79HoldPathHeadKey start family C full = none) :
    lemma79HoldPathCutoffTailMomentENN
        start family n xi epsilon C 2 full = 0 := by
  unfold lemma79HoldPathCutoffTailMomentENN
  rw [lemma79CutoffTailMoment_eq_zero_of_headKey_eq_none
    (R := 2) (by omega) hkey]
  simp

/-- The complete absent-key fiber contributes zero expectation. -/
theorem lemma79_holdList_cutoffTailMomentENN_two_noneKey_eq_zero
    (J : ℕ) (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF J)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey start family J) none).indicator
            (lemma79HoldPathCutoffTailMomentENN
              start family n xi epsilon J 2)) = 0 := by
  unfold lemma79PMFENNExpectation
  rw [ENNReal.tsum_eq_zero]
  intro full
  by_cases hmem :
      full ∈ lemma79KeyAtom Set.univ
        (lemma79HoldPathHeadKey start family J) none
  · have hkey :
        lemma79HoldPathHeadKey start family J full = none := hmem.2
    rw [Set.indicator_of_mem hmem,
      lemma79HoldPathCutoffTailMomentENN_two_eq_zero_of_headKey_none hkey,
      mul_zero]
  · simp [Set.indicator, hmem]

/-- Global native killed `R=2` expectation reduced to bounds on all complete
semantic `some` fibers. -/
theorem lemma79_holdList_cutoffTailMomentENN_two_le_of_someKey_bounds
    (J : ℕ) (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (hsome : ∀ k : ℕ × TaoSection7Point,
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF J)
          ((lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey start family J) (some k)).indicator
              (lemma79HoldPathCutoffTailMomentENN
                start family n xi epsilon J 2)) ≤
        (taoSection7HoldListPMF J).toOuterMeasure
            (lemma79KeyAtom Set.univ
              (lemma79HoldPathHeadKey start family J) (some k)) *
          ENNReal.ofReal (Real.exp epsilon)) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF J)
        (lemma79HoldPathCutoffTailMomentENN
          start family n xi epsilon J 2) ≤
      ENNReal.ofReal (Real.exp epsilon) := by
  have hlocal :
      ∀ k : Option (ℕ × TaoSection7Point),
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF J)
            ((lemma79KeyAtom Set.univ
              (lemma79HoldPathHeadKey start family J) k).indicator
                (lemma79HoldPathCutoffTailMomentENN
                  start family n xi epsilon J 2)) ≤
          (taoSection7HoldListPMF J).toOuterMeasure
              (lemma79KeyAtom Set.univ
                (lemma79HoldPathHeadKey start family J) k) *
            ENNReal.ofReal (Real.exp epsilon) := by
    intro k
    cases k with
    | none =>
        rw [lemma79_holdList_cutoffTailMomentENN_two_noneKey_eq_zero]
        exact bot_le
    | some k =>
        exact hsome k
  have hagg :=
    lemma79_pmfENNExpectation_le_mul_of_key
      (taoSection7HoldListPMF J) Set.univ
      (lemma79HoldPathHeadKey start family J)
      (lemma79HoldPathCutoffTailMomentENN
        start family n xi epsilon J 2)
      (ENNReal.ofReal (Real.exp epsilon)) hlocal
  have huniv :
      (taoSection7HoldListPMF J).toOuterMeasure Set.univ = 1 :=
    ((taoSection7HoldListPMF J).toOuterMeasure_apply_eq_one_iff Set.univ).2
      (Set.subset_univ _)
  simpa [huniv] using hagg

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
