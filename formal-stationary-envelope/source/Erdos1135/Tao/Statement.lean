import Erdos1135.Basic
import Erdos1135.Tao.Density.LogDensity

/-!
# Statement Surface For Tao's Almost-Bounded-Orbits Theorem

This module records statement-facing predicates for the Tao lane without asserting the main
theorem.  The proof-facing surface uses "hits below a threshold" instead of an infinite orbit
minimum, matching the strict inequality in Tao's numbered theorem while keeping the first API
small.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

/-- A real-valued function on natural numbers tends to `+∞`. -/
def GrowsToInfinity (f : ℕ → ℝ) : Prop :=
  Tendsto f atTop atTop

/-- The standard Collatz orbit of `N` eventually hits below the real threshold `b`. -/
def collatzHitsBelowReal (N : ℕ) (b : ℝ) : Prop :=
  ∃ m : ℕ, ((collatzStep^[m]) N : ℝ) < b

/-- The standard Collatz orbit of `N` eventually hits at most the natural threshold `B`. -/
def collatzHitsAtMost (N B : ℕ) : Prop :=
  ∃ m : ℕ, (collatzStep^[m]) N ≤ B

/-- Fixed-threshold good set used by later finite-threshold assembly lemmas. -/
def collatzThresholdGood (B : ℕ) : Set ℕ :=
  {N : ℕ | 0 < N ∧ collatzHitsAtMost N B}

/--
The theorem-shaped target corresponding to Tao's published strict-inequality statement.  This is a
`Prop` target, not an asserted theorem.
-/
def TaoAlmostBoundedStatement : Prop :=
  ∀ f : ℕ → ℝ,
    GrowsToInfinity f →
      HasLogDensity {N : ℕ | 0 < N ∧ collatzHitsBelowReal N (f N)} 1

/-- A finite natural threshold below a real threshold gives a real hit-below witness. -/
theorem collatzHitsAtMost_to_hitsBelowReal {N B : ℕ} {b : ℝ}
    (h : collatzHitsAtMost N B) (hb : (B : ℝ) < b) :
    collatzHitsBelowReal N b := by
  rcases h with ⟨m, hm⟩
  exact ⟨m, lt_of_le_of_lt (by exact_mod_cast hm) hb⟩

/--
Schematic threshold-family hypothesis for the later Section 3 assembly route.  Analytic work
should provide this or a source-normalized finite-window variant; this module only records the
consumer shape.
-/
def ThresholdLowerBoundHypothesis (eps : ℕ → ℝ) : Prop :=
  Tendsto eps atTop (nhds 0) ∧
    ∀ B : ℕ, 2 ≤ B →
      ∀ᶠ X in atTop, 1 - eps B ≤ logCountingRatio (collatzThresholdGood B) X

/--
Once `f` is eventually above a fixed threshold, the fixed-threshold good set is eventually a
subset of the `f`-dependent hit-below set.
-/
theorem eventually_thresholdGood_subset_hitsBelowReal {f : ℕ → ℝ}
    (hf : GrowsToInfinity f) {B : ℕ} :
    ∀ᶠ N in atTop,
      N ∈ collatzThresholdGood B →
        0 < N ∧ collatzHitsBelowReal N (f N) := by
  filter_upwards [hf.eventually_gt_atTop (B : ℝ)] with N hB hN
  exact ⟨hN.1, collatzHitsAtMost_to_hitsBelowReal hN.2 hB⟩

/--
The future assembly target from finite-threshold lower bounds to the almost-bounded statement.
This remains a `Prop` target until the finite-initial-segment and analytic inputs are proved.
-/
def TaoThresholdAssemblyStatement : Prop :=
  ∀ eps : ℕ → ℝ, ThresholdLowerBoundHypothesis eps → TaoAlmostBoundedStatement

end Tao
end Erdos1135
