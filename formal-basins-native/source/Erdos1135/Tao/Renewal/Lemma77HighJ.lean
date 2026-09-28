import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Renewal.Lemma710PostStoppedKernel
import Erdos1135.Tao.Renewal.Lemma77PotentialCore
import Erdos1135.Tao.Fourier.Section7Geometry

/-!
# Lemma 7.7 High-Horizontal Tail Surface

This module isolates the prefix high-horizontal tail event used by the outer
`(7.54)` `BadPre` branch.  It does not prove Tao's Lemma 7.7; it only records
the deterministic current-scale/log-gap reduction that a future Lemma 7.7
tail summation should feed.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

/--
Source-hit specialization of `prefixIncrement`.

This is the deterministic rewrite needed before the outer `(7.54)` `Jpre`
producer can target source-list data instead of an abstract renewal endpoint.
It is not itself a proof that the arbitrary outer statistic `Jpre` is this
source-hit displacement.
-/
theorem prefixIncrement_sourceHitPathPoint
    {Ω : Type*}
    (j : Ω → ℕ+) (sourceHeight : Ω → ℕ)
    (pre0 : Ω → List ℕ) (pres : Ω → List (List ℕ))
    (K : Ω → ℕ) (ω : Ω) :
    prefixIncrement
        (fun ω => taoSection7SourceHitPoint (j ω) (sourceHeight ω) (pre0 ω))
        K
        (fun ω => taoSection7HoldIncrementsOfPrefixes (pres ω)) ω =
      ((taoSection7SourceHitPathPoint
          (j ω) (sourceHeight ω) (pre0 ω) (pres ω) (K ω)).j : ℕ) -
        ((taoSection7SourceHitPoint
          (j ω) (sourceHeight ω) (pre0 ω)).j : ℕ) := by
  simp [prefixIncrement, taoSection7RenewalPathPoint_sourceHit_eq]

/--
Ledger projection from a source-run q-to-first displacement to the Lemma 7.7
prefix increment.

The hypothesis `hJpre` is still the hard same-sample outer `(7.54)` fact: it
identifies the arbitrary `Jpre` statistic with the source-run displacement.
This theorem only transports that displacement through the existing random-`K`
source ledger to the renewal prefix increment used by Lemma 7.7.
-/
theorem jpre_eq_prefixIncrement_of_randomKSourceLedger_pointAt
    {Ω : Type*}
    {Jpre : Ω → ℕ}
    {PrefixOK : Ω → ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {j : Ω → ℕ+} {sourceHeight : Ω → ℕ}
    {firstBlock : Ω → List ℕ}
    {sourceSuffixes : Ω → List (List ℕ)}
    {old : Ω → TaoSection7Triangle}
    {q first K verticalGap : Ω → ℕ}
    {start : Ω → TaoSection7RenewalPoint}
    {holdPrefix : Ω → List TaoSection7RenewalPoint}
    (hJpre :
      ∀ ω, Jpre ω =
        ((pointAt ω (first ω)).j : ℕ) - ((pointAt ω (q ω)).j : ℕ))
    (hledger :
      ∀ ω,
        TaoSection7Lemma710.RandomKSourceLedger (PrefixOK ω) (pointAt ω)
          (j ω) (sourceHeight ω) (firstBlock ω) (sourceSuffixes ω)
          (old ω) (q ω) (first ω) (K ω) (verticalGap ω)
          (start ω) (holdPrefix ω)) :
    ∀ ω, Jpre ω = prefixIncrement start K holdPrefix ω := by
  intro ω
  simpa [prefixIncrement, (hledger ω).first_point_eq, (hledger ω).point_q_eq]
    using hJpre ω

/-- The `h77_highJ` event consumed by the outer `(7.54)` `BadPre` adapter. -/
def highJEvent
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (m : ℕ) : Set Ω :=
  {ω | 4 * m ≤ 5 * prefixIncrement start K pre ω}

/-- Positive linear gap between Tao's `4/5` high-`j` threshold and `(7.52)/4`. -/
def currentScaleHighJMargin : ℝ :=
  (4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4

theorem currentScaleHighJMargin_pos :
    0 < currentScaleHighJMargin := by
  dsimp [currentScaleHighJMargin]
  exact sub_pos.mpr taoSection7_log9_div_log2_div_four_lt_four_fifths

/--
The centered high-tail event that should be bounded by Tao's Lemma 7.7 after
the current-scale `(7.52)` estimate is supplied.
-/
def centeredHighTailEvent
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s m : ℕ) : Set Ω :=
  {ω |
    ((s : ℝ) / 4) + currentScaleHighJMargin * (m : ℝ) ≤
      (prefixIncrement start K pre ω : ℝ)}

theorem highJEvent_subset_centeredHighTailEvent_of_currentScale
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m : ℕ}
    (hscale : (s : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ)) :
    highJEvent start K pre m ⊆ centeredHighTailEvent start K pre s m := by
  intro ω hω
  have hscale_div :
      (s : ℝ) / 4 ≤
        ((Real.log 9 / Real.log 2) / 4) * (m : ℝ) := by
    calc
      (s : ℝ) / 4 ≤
          ((Real.log 9 / Real.log 2) * (m : ℝ)) / 4 :=
        div_le_div_of_nonneg_right hscale (by norm_num)
      _ = ((Real.log 9 / Real.log 2) / 4) * (m : ℝ) := by ring
  have hinc :
      (4 / 5 : ℝ) * (m : ℝ) ≤
        (prefixIncrement start K pre ω : ℝ) := by
    have hcast :
        (4 : ℝ) * (m : ℝ) ≤
          (5 : ℝ) * (prefixIncrement start K pre ω : ℝ) := by
      exact_mod_cast hω
    nlinarith
  show
      ((s : ℝ) / 4) + currentScaleHighJMargin * (m : ℝ) ≤
        (prefixIncrement start K pre ω : ℝ)
  calc
    ((s : ℝ) / 4) + currentScaleHighJMargin * (m : ℝ)
        ≤ ((Real.log 9 / Real.log 2) / 4) * (m : ℝ) +
            currentScaleHighJMargin * (m : ℝ) := by
          simpa [add_comm] using
            add_le_add_right hscale_div
              (currentScaleHighJMargin * (m : ℝ))
    _ = (4 / 5 : ℝ) * (m : ℝ) := by
          dsimp [currentScaleHighJMargin]
          ring
    _ ≤ (prefixIncrement start K pre ω : ℝ) := hinc

/--
Consume the current-scale `(7.52)` inequality and a future Lemma 7.7 high-tail
probability estimate to produce the exact `h77_highJ` probability event.
-/
theorem highJ_prob_le_of_currentScale_centeredTail
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m : ℕ} {bPre : ℝ}
    (hscale : (s : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ))
    (htail :
      pmfProb μ (centeredHighTailEvent start K pre s m) ≤ bPre) :
    pmfProb μ (highJEvent start K pre m) ≤ bPre :=
  le_trans
    (pmfProb_mono μ
      (highJEvent_subset_centeredHighTailEvent_of_currentScale
        (start := start) (K := K) (pre := pre) hscale))
    htail

end TaoSection7Lemma77

end

end Tao
end Erdos1135
