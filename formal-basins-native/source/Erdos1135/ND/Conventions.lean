import Erdos1135.Tao.ColMin
import Erdos1135.Tao.Probability.LogWindowEndpoints
import Erdos1135.Tao.Probability.LogWindowPMF
import Erdos1135.Tao.Section5.Schedule
import Erdos1135.Tao.Syracuse.FirstPassage
import Erdos1135.Tao.Syracuse.RealFirstPassage
import Erdos1135.Tao.Syracuse.Statement
import Erdos1135.Terras.Density.NaturalDensity

/-!
# Conventions For The Natural-Density Upgrade

This module freezes the finite-window, no-hit, total-variation, orbit-minimum,
and natural-counting conventions used by the v10 ND statement surface.  It
contains no analytic estimate.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

/-- The fixed Tao/ND scale exponent `alpha = 1.001`. -/
noncomputable abbrev alpha : ℝ := Tao.taoAlpha

/-- The branch-indexed ND-M2 source scale over a real threshold. -/
noncomputable def transportSourceY
    (x : ℝ) : Tao.TaoSection5SourceBranch → ℝ
  | .alpha => Real.rpow x alpha
  | .alphaSq => Real.rpow x (alpha ^ 2)

/-- Positive natural numbers, with zero explicitly excluded. -/
def positiveNaturals : Set ℕ :=
  {N : ℕ | 0 < N}

/-- Positive odd natural numbers. -/
def positiveOddNaturals : Set ℕ :=
  {N : ℕ | 0 < N ∧ Odd N}

/-- The inclusive odd block `2N+1 ∩ [y, y^alpha]`.

The lower endpoint is `ceil y` and the upper endpoint is
`floor (y^alpha)`, through the checked Tao endpoint convention. -/
noncomputable def oddBlock (y : ℝ) : Finset ℕ :=
  Tao.taoNyOddWindow y alpha

/-- The uniform law on a nonempty finite set of naturals. -/
noncomputable def uniformFinsetPMF (S : Finset ℕ) (hS : S.Nonempty) :
    PMF {N : ℕ // N ∈ S} := by
  letI : Nonempty {N : ℕ // N ∈ S} :=
    ⟨⟨hS.choose, hS.choose_spec⟩⟩
  exact PMF.uniformOfFintype _

/-- The natural-counting block law `U_y`. -/
noncomputable def uniformOddBlockPMF (y : ℝ)
    (hwindow : (oddBlock y).Nonempty) :
    PMF {N : ℕ // N ∈ oddBlock y} :=
  uniformFinsetPMF (oddBlock y) hwindow

/-- The logarithmically weighted block law `N_y`. -/
noncomputable def logOddBlockPMF (y : ℝ)
    (hmass : 0 < Tao.logFinsetMass (oddBlock y)) :
    PMF {N : ℕ // N ∈ oddBlock y} :=
  Tao.logFinsetPMF (oddBlock y) hmass

/-- Total first-passage location at the real threshold `x`.

The codomain is bounded by `floor x`; if the Syracuse orbit never hits the
threshold, the value is the distinguished endpoint `1`. -/
noncomputable def passLocationOrOne (x : ℝ) (N : ℕ) (hx : 1 ≤ x) :
    {M : ℕ // M ≤ Nat.floor x} :=
  Tao.syracusePassLocationAtMostOrOne (Nat.floor x) N
    (Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx))

/-- Pushforward of the uniform block law by totalized first passage. -/
noncomputable def uniformPassLaw (x y : ℝ) (hx : 1 ≤ x)
    (hwindow : (oddBlock y).Nonempty) :
    PMF {M : ℕ // M ≤ Nat.floor x} :=
  (uniformOddBlockPMF y hwindow).map
    (fun N => passLocationOrOne x N.1 hx)

/-- Pushforward of the logarithmic block law by totalized first passage. -/
noncomputable def logPassLaw (x y : ℝ) (hx : 1 ≤ x)
    (hmass : 0 < Tao.logFinsetMass (oddBlock y)) :
    PMF {M : ℕ // M ≤ Nat.floor x} :=
  (logOddBlockPMF y hmass).map
    (fun N => passLocationOrOne x N.1 hx)

/-- Uniform-block probability of never hitting the real threshold `x`. -/
noncomputable def uniformNoHitProbability (x y : ℝ)
    (hwindow : (oddBlock y).Nonempty) : ℝ :=
  Tao.pmfProb (uniformOddBlockPMF y hwindow)
    {N | ¬ Tao.syracuseHitsAtMostReal N.1 x}

/-- Full-L1 distance between the totalized uniform and logarithmic pass laws.

This is Tao's project convention `sum |p-q|`, not half L1. -/
noncomputable def passFullL1 (x y : ℝ) (hx : 1 ≤ x)
    (hwindow : (oddBlock y).Nonempty)
    (hmass : 0 < Tao.logFinsetMass (oddBlock y)) : ℝ :=
  Tao.taoTV (uniformPassLaw x y hx hwindow)
    (logPassLaw x y hx hmass)

/-- Values attained by the Syracuse orbit of `N`. -/
noncomputable def syracuseOrbitValues (N : ℕ) : Set ℕ :=
  Set.range (fun m : ℕ => (Tao.syracuse^[m]) N)

/-- Natural-number minimum of the Syracuse orbit of `N`. -/
noncomputable def syracuseOrbitMin (N : ℕ) : ℕ :=
  sInf (syracuseOrbitValues N)

theorem syracuseOrbitValues_nonempty (N : ℕ) :
    (syracuseOrbitValues N).Nonempty := by
  refine ⟨N, ?_⟩
  exact ⟨0, by simp⟩

theorem syracuseOrbitMin_mem (N : ℕ) :
    syracuseOrbitMin N ∈ syracuseOrbitValues N := by
  simpa [syracuseOrbitMin] using
    Nat.sInf_mem (syracuseOrbitValues_nonempty N)

theorem syracuseOrbitMin_le_iterate (N m : ℕ) :
    syracuseOrbitMin N ≤ (Tao.syracuse^[m]) N := by
  exact Nat.sInf_le
    (show (Tao.syracuse^[m]) N ∈ syracuseOrbitValues N from ⟨m, rfl⟩)

/-- A finite Syracuse threshold is hit exactly when the orbit minimum is at
most that threshold. -/
theorem syracuseHitsAtMost_iff_orbitMin_le {N B : ℕ} :
    Tao.syracuseHitsAtMost N B ↔ syracuseOrbitMin N ≤ B := by
  constructor
  · rintro ⟨m, hm⟩
    exact (syracuseOrbitMin_le_iterate N m).trans hm
  · intro h
    rcases syracuseOrbitMin_mem N with ⟨m, hm⟩
    exact ⟨m, by simpa [hm] using h⟩

/-- The no-hit event is exactly the source-facing strict minimum event. -/
theorem not_syracuseHitsAtMost_iff_lt_orbitMin {N B : ℕ} :
    ¬ Tao.syracuseHitsAtMost N B ↔ B < syracuseOrbitMin N := by
  rw [syracuseHitsAtMost_iff_orbitMin_le]
  exact not_le

/-- Strict real hit-below and the source-facing Syracuse minimum agree. -/
theorem syracuseHitsBelowReal_iff_orbitMin_lt {N : ℕ} {b : ℝ} :
    Tao.syracuseHitsBelowReal N b ↔ (syracuseOrbitMin N : ℝ) < b := by
  constructor
  · rintro ⟨m, hm⟩
    exact lt_of_le_of_lt
      (Nat.cast_le.mpr (syracuseOrbitMin_le_iterate N m)) hm
  · intro h
    rcases syracuseOrbitMin_mem N with ⟨m, hm⟩
    exact ⟨m, by simpa [hm] using h⟩

/-- Inclusive natural count `#(S ∩ [0,X])`.

The inherited `natCount S K` counts the half-open prefix `[0,K)`, hence the
explicit successor. -/
noncomputable def natCountLE (S : Set ℕ) (X : ℕ) : ℕ :=
  Terras.natCount S (X + 1)

/-- Inclusive real-endpoint count, with endpoint `floor x`. -/
noncomputable def natCountLEReal (S : Set ℕ) (x : ℝ) : ℕ :=
  natCountLE S (Nat.floor x)

end ND
end Erdos1135
