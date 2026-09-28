/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Density.FiniteLogCountAlgebra
import Erdos1135SecondScale.Tao.Probability.LogWindowEndpoints
import Erdos1135SecondScale.Tao.Probability.LogWindowPrefix
import Erdos1135SecondScale.Tao.Probability.LogWindowPMF
import Erdos1135SecondScale.Tao.Syracuse.FirstPassage
import Erdos1135SecondScale.Tao.Syracuse.RealFirstPassage
import Erdos1135SecondScale.Tao.Syracuse.Statement
import Erdos1135SecondScale.Tao.ThresholdAssembly

/-!
# Section 3 Statement Sockets

This module records source-facing statement surfaces around Tao's Theorem 3.1
and Proposition 1.11.  It names the finite-threshold Syracuse lower-bound
target, the later Syracuse-to-Collatz transfer socket, and a first-passage
stabilization socket over finite logarithmic windows.

It names the concrete integer endpoint convention and the real-floor endpoint
lift for `N_y`.  It does not prove Proposition 1.11, provide a rate-bearing
real-threshold socket or floor-rate transfer, prove Theorem 3.1, or prove the
Syracuse-to-Collatz transfer.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped Topology BigOperators

/-- Odd-Syracuse finite-threshold lower-bound hypothesis in Theorem 3.1 form. -/
def SyracuseThresholdLowerBoundHypothesis (eps : ℕ → ℝ) : Prop :=
  Tendsto eps atTop (nhds 0) ∧
    ∀ B : ℕ, 2 ≤ B →
      ∀ᶠ X in atTop,
        (1 / 2 : ℝ) - eps B ≤ logCountingRatio (syracuseThresholdGood B) X

/-- Theorem 3.1 statement socket: some vanishing error proves the odd lower bound. -/
def TaoTheorem31SyracuseFiniteThresholdStatement : Prop :=
  ∃ eps : ℕ → ℝ, SyracuseThresholdLowerBoundHypothesis eps

/--
Later equation `(1.2)`/finite-cutoff work should turn the odd Syracuse
finite-threshold lower bound into the Collatz threshold lower-bound hypothesis
already consumed by `ThresholdAssembly`.
-/
def TaoTheorem31ToCollatzThresholdStatement : Prop :=
  TaoTheorem31SyracuseFiniteThresholdStatement →
    ∃ eps : ℕ → ℝ, ThresholdLowerBoundHypothesis eps

/-- The Collatz-transfer socket plus the checked assembly theorem imply Tao's statement target. -/
theorem TaoTheorem31ToCollatzThresholdStatement.to_taoAlmostBounded
    (htransfer : TaoTheorem31ToCollatzThresholdStatement)
    (h31 : TaoTheorem31SyracuseFiniteThresholdStatement) :
    TaoAlmostBoundedStatement := by
  rcases htransfer h31 with ⟨eps, heps⟩
  exact taoAlmostBounded_of_thresholdLowerBound heps

/-- Total first-passage location with Tao's artificial no-hit value `1`. -/
noncomputable def syracusePassLocationOrOne
    (B N : ℕ) (hB : 1 ≤ B) : {M : ℕ // M ≤ B} :=
  syracusePassLocationAtMostOrOne B N hB

/-- Total pass-location law from a finite odd logarithmic source window. -/
noncomputable def syracusePassLocationLaw
    (lo hi B : ℕ) (hB : 1 ≤ B)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    PMF {M : ℕ // M ≤ B} :=
  (oddLogWindowPMF lo hi hmass).map
    fun N : {n : ℕ // n ∈ oddLogWindow lo hi} =>
      syracusePassLocationOrOne B (N : ℕ) hB

/-- Source event for not hitting a natural Syracuse threshold. -/
def syracuseNoHitAtMost (B : ℕ) : Set ℕ :=
  {N : ℕ | ¬ syracuseHitsAtMost N B}

/-- Source event for not hitting a real Syracuse threshold. -/
def syracuseNoHitAtMostReal (x : ℝ) : Set ℕ :=
  {N : ℕ | ¬ syracuseHitsAtMostReal N x}

/-- Real no-hit events reduce to the natural floor threshold under `0 <= x`. -/
theorem syracuseNoHitAtMostReal_iff_floor {x : ℝ} (hx : 0 ≤ x) {N : ℕ} :
    N ∈ syracuseNoHitAtMostReal x ↔
      N ∈ syracuseNoHitAtMost (Nat.floor x) := by
  simp [syracuseNoHitAtMostReal, syracuseNoHitAtMost,
    syracuseHitsAtMostReal_iff_floor hx]

/-- If `1 <= x`, the floor threshold is a nonzero threshold for totalized pass locations. -/
theorem one_le_floor_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ Nat.floor x :=
  Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx)

/-- No-hit probability for a finite odd logarithmic source window. -/
noncomputable def syracuseNoHitWindowProb (B lo hi : ℕ)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) : ℝ :=
  pmfProb (oddLogWindowPMF lo hi hmass)
    {N : {n : ℕ // n ∈ oddLogWindow lo hi} |
      (N : ℕ) ∈ syracuseNoHitAtMost B}

/-- No-hit probability for a finite odd logarithmic source window and real threshold. -/
noncomputable def syracuseNoHitRealWindowProb (x : ℝ) (lo hi : ℕ)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) : ℝ :=
  pmfProb (oddLogWindowPMF lo hi hmass)
    {N : {n : ℕ // n ∈ oddLogWindow lo hi} |
      (N : ℕ) ∈ syracuseNoHitAtMostReal x}

/-- Real no-hit window probability reduces to the natural floor threshold. -/
theorem syracuseNoHitRealWindowProb_eq_floor {x : ℝ} (hx : 0 ≤ x)
    (lo hi : ℕ) (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    syracuseNoHitRealWindowProb x lo hi hmass =
      syracuseNoHitWindowProb (Nat.floor x) lo hi hmass := by
  simp [syracuseNoHitRealWindowProb, syracuseNoHitWindowProb,
    syracuseNoHitAtMostReal_iff_floor hx]

/-- Total real-threshold pass location, represented over the finite floor-bounded codomain. -/
noncomputable def syracusePassLocationRealFloorOrOne
    (x : ℝ) (N : ℕ) (hx : 1 ≤ x) :
    {M : ℕ // M ≤ Nat.floor x} :=
  syracusePassLocationOrOne (Nat.floor x) N (one_le_floor_of_one_le hx)

/-- The real-floor totalizer is definitionally the natural totalizer at `Nat.floor x`. -/
theorem syracusePassLocationRealFloorOrOne_eq_floor
    (x : ℝ) (N : ℕ) (hx : 1 ≤ x) :
    syracusePassLocationRealFloorOrOne x N hx =
      syracusePassLocationOrOne (Nat.floor x) N (one_le_floor_of_one_le hx) :=
  rfl

/-- Total pass-location law for a finite odd logarithmic source window and real threshold. -/
noncomputable def syracusePassLocationRealFloorLaw
    (lo hi : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    PMF {M : ℕ // M ≤ Nat.floor x} :=
  (oddLogWindowPMF lo hi hmass).map
    fun N : {n : ℕ // n ∈ oddLogWindow lo hi} =>
      syracusePassLocationRealFloorOrOne x (N : ℕ) hx

/-- The real-floor pass-location law is the natural law at `Nat.floor x`. -/
theorem syracusePassLocationRealFloorLaw_eq_floor
    (lo hi : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    syracusePassLocationRealFloorLaw lo hi x hx hmass =
      syracusePassLocationLaw lo hi (Nat.floor x)
        (one_le_floor_of_one_le hx) hmass :=
  rfl

/-- Full-L1 distance between two total pass-location laws. -/
noncomputable def syracusePassWindowTV
    (B lo₁ hi₁ lo₂ hi₂ : ℕ) (hB : 1 ≤ B)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)) : ℝ :=
  taoTV (syracusePassLocationLaw lo₁ hi₁ B hB hmass₁)
    (syracusePassLocationLaw lo₂ hi₂ B hB hmass₂)

/-- Full-L1 distance between real-floor pass-location laws. -/
noncomputable def syracusePassRealFloorWindowTV
    (x : ℝ) (lo₁ hi₁ lo₂ hi₂ : ℕ) (hx : 1 ≤ x)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)) : ℝ :=
  taoTV (syracusePassLocationRealFloorLaw lo₁ hi₁ x hx hmass₁)
    (syracusePassLocationRealFloorLaw lo₂ hi₂ x hx hmass₂)

/-- Real-floor pass-location TV is the natural pass-location TV at `Nat.floor x`. -/
theorem syracusePassRealFloorWindowTV_eq_floor
    (x : ℝ) (lo₁ hi₁ lo₂ hi₂ : ℕ) (hx : 1 ≤ x)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)) :
    syracusePassRealFloorWindowTV x lo₁ hi₁ lo₂ hi₂ hx hmass₁ hmass₂ =
      syracusePassWindowTV (Nat.floor x) lo₁ hi₁ lo₂ hi₂
        (one_le_floor_of_one_le hx) hmass₁ hmass₂ :=
  rfl

theorem pmfProb_syracusePassLocationLaw_preimage {lo hi B : ℕ} (hB : 1 ≤ B)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (A : Set {M : ℕ // M ≤ B}) :
    pmfProb (syracusePassLocationLaw lo hi B hB hmass) A =
      pmfProb (oddLogWindowPMF lo hi hmass)
        {N : {n : ℕ // n ∈ oddLogWindow lo hi} |
          syracusePassLocationOrOne B (N : ℕ) hB ∈ A} := by
  rw [syracusePassLocationLaw]
  exact pmfProb_map_preimage (oddLogWindowPMF lo hi hmass)
    (fun N : {n : ℕ // n ∈ oddLogWindow lo hi} =>
      syracusePassLocationOrOne B (N : ℕ) hB) A

theorem pmfProb_syracusePassLocationLaw_logFinsetProb {lo hi B : ℕ} (hB : 1 ≤ B)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (A : Set {M : ℕ // M ≤ B}) :
    pmfProb (syracusePassLocationLaw lo hi B hB hmass) A =
      logFinsetProb (oddLogWindow lo hi)
        {N : ℕ | syracusePassLocationOrOne B N hB ∈ A} := by
  rw [pmfProb_syracusePassLocationLaw_preimage]
  simpa using pmfProb_oddLogWindowPMF lo hi hmass
    ({N : ℕ | syracusePassLocationOrOne B N hB ∈ A})

theorem pmfProb_syracusePassLocationLaw_sub_windowTV_le
    {lo₁ hi₁ lo₂ hi₂ B : ℕ} (hB : 1 ≤ B)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (A : Set {M : ℕ // M ≤ B}) :
    pmfProb (syracusePassLocationLaw lo₁ hi₁ B hB hmass₁) A -
        syracusePassWindowTV B lo₁ hi₁ lo₂ hi₂ hB hmass₁ hmass₂ ≤
      pmfProb (syracusePassLocationLaw lo₂ hi₂ B hB hmass₂) A := by
  exact pmfProb_sub_taoTV_le_pmfProb
    (syracusePassLocationLaw lo₁ hi₁ B hB hmass₁)
    (syracusePassLocationLaw lo₂ hi₂ B hB hmass₂) A

theorem pmfProb_syracusePassLocationLaw_sub_of_windowTV_le
    {lo₁ hi₁ lo₂ hi₂ B : ℕ} (hB : 1 ≤ B)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (A : Set {M : ℕ // M ≤ B}) {eps : ℝ}
    (hTV : syracusePassWindowTV B lo₁ hi₁ lo₂ hi₂ hB hmass₁ hmass₂ ≤ eps) :
    pmfProb (syracusePassLocationLaw lo₁ hi₁ B hB hmass₁) A - eps ≤
      pmfProb (syracusePassLocationLaw lo₂ hi₂ B hB hmass₂) A := by
  have h := pmfProb_syracusePassLocationLaw_sub_windowTV_le
    (B := B) (lo₁ := lo₁) (hi₁ := hi₁) (lo₂ := lo₂) (hi₂ := hi₂)
    hB hmass₁ hmass₂ A
  linarith

theorem pass_prob_sub_noHit_le_source_event_prob
    {lo hi B : ℕ} (hB : 1 ≤ B)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (A : Set {M : ℕ // M ≤ B}) (Good : Set ℕ)
    (hGood : ∀ N : ℕ, N ∈ oddLogWindow lo hi →
      N ∉ syracuseNoHitAtMost B →
      syracusePassLocationOrOne B N hB ∈ A → N ∈ Good) :
    pmfProb (syracusePassLocationLaw lo hi B hB hmass) A -
        syracuseNoHitWindowProb B lo hi hmass ≤
      logFinsetProb (oddLogWindow lo hi) Good := by
  let passEvent : Set {n : ℕ // n ∈ oddLogWindow lo hi} :=
    {N | syracusePassLocationOrOne B (N : ℕ) hB ∈ A}
  let badEvent : Set {n : ℕ // n ∈ oddLogWindow lo hi} :=
    {N | (N : ℕ) ∈ syracuseNoHitAtMost B}
  let goodEvent : Set {n : ℕ // n ∈ oddLogWindow lo hi} :=
    {N | (N : ℕ) ∈ Good}
  have hsubset : passEvent \ badEvent ⊆ goodEvent := by
    intro N hN
    exact hGood (N : ℕ) N.property hN.2 hN.1
  have hdiff :
      pmfProb (oddLogWindowPMF lo hi hmass) passEvent -
          pmfProb (oddLogWindowPMF lo hi hmass) badEvent ≤
        pmfProb (oddLogWindowPMF lo hi hmass) goodEvent :=
    pmfProb_diff_le_of_diff_subset (oddLogWindowPMF lo hi hmass) hsubset
  calc
    pmfProb (syracusePassLocationLaw lo hi B hB hmass) A -
        syracuseNoHitWindowProb B lo hi hmass =
      pmfProb (oddLogWindowPMF lo hi hmass) passEvent -
          pmfProb (oddLogWindowPMF lo hi hmass) badEvent := by
        rw [pmfProb_syracusePassLocationLaw_preimage, syracuseNoHitWindowProb]
    _ ≤ pmfProb (oddLogWindowPMF lo hi hmass) goodEvent := hdiff
    _ = logFinsetProb (oddLogWindow lo hi) Good := by
        rw [pmfProb_oddLogWindowPMF]

theorem source_event_prob_sub_noHit_le_pass_prob
    {lo hi B : ℕ} (hB : 1 ≤ B)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (A : Set {M : ℕ // M ≤ B}) (Good : Set ℕ)
    (hPass : ∀ N : ℕ, N ∈ oddLogWindow lo hi →
      N ∉ syracuseNoHitAtMost B →
      N ∈ Good → syracusePassLocationOrOne B N hB ∈ A) :
    logFinsetProb (oddLogWindow lo hi) Good -
        syracuseNoHitWindowProb B lo hi hmass ≤
      pmfProb (syracusePassLocationLaw lo hi B hB hmass) A := by
  let sourceEvent : Set {n : ℕ // n ∈ oddLogWindow lo hi} :=
    {N | (N : ℕ) ∈ Good}
  let badEvent : Set {n : ℕ // n ∈ oddLogWindow lo hi} :=
    {N | (N : ℕ) ∈ syracuseNoHitAtMost B}
  let passEvent : Set {n : ℕ // n ∈ oddLogWindow lo hi} :=
    {N | syracusePassLocationOrOne B (N : ℕ) hB ∈ A}
  have hsubset : sourceEvent \ badEvent ⊆ passEvent := by
    intro N hN
    exact hPass (N : ℕ) N.property hN.2 hN.1
  have hdiff :
      pmfProb (oddLogWindowPMF lo hi hmass) sourceEvent -
          pmfProb (oddLogWindowPMF lo hi hmass) badEvent ≤
        pmfProb (oddLogWindowPMF lo hi hmass) passEvent :=
    pmfProb_diff_le_of_diff_subset (oddLogWindowPMF lo hi hmass) hsubset
  calc
    logFinsetProb (oddLogWindow lo hi) Good -
        syracuseNoHitWindowProb B lo hi hmass =
      pmfProb (oddLogWindowPMF lo hi hmass) sourceEvent -
          pmfProb (oddLogWindowPMF lo hi hmass) badEvent := by
        rw [← pmfProb_oddLogWindowPMF lo hi hmass Good, syracuseNoHitWindowProb]
    _ ≤ pmfProb (oddLogWindowPMF lo hi hmass) passEvent := hdiff
    _ = pmfProb (syracusePassLocationLaw lo hi B hB hmass) A := by
        rw [pmfProb_syracusePassLocationLaw_preimage]

theorem source_event_prob_two_window_step
    {lo₁ hi₁ lo₂ hi₂ B : ℕ} (hB : 1 ≤ B)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (A : Set {M : ℕ // M ≤ B}) (Good₁ Good₂ : Set ℕ)
    (hPass₁ : ∀ N : ℕ, N ∈ oddLogWindow lo₁ hi₁ →
      N ∉ syracuseNoHitAtMost B →
      N ∈ Good₁ → syracusePassLocationOrOne B N hB ∈ A)
    (hGood₂ : ∀ N : ℕ, N ∈ oddLogWindow lo₂ hi₂ →
      N ∉ syracuseNoHitAtMost B →
      syracusePassLocationOrOne B N hB ∈ A → N ∈ Good₂) :
    logFinsetProb (oddLogWindow lo₁ hi₁) Good₁ -
        syracuseNoHitWindowProb B lo₁ hi₁ hmass₁ -
          syracusePassWindowTV B lo₁ hi₁ lo₂ hi₂ hB hmass₁ hmass₂ -
            syracuseNoHitWindowProb B lo₂ hi₂ hmass₂ ≤
      logFinsetProb (oddLogWindow lo₂ hi₂) Good₂ := by
  have hsource := source_event_prob_sub_noHit_le_pass_prob
    (B := B) (lo := lo₁) (hi := hi₁) hB hmass₁ A Good₁ hPass₁
  have htv := pmfProb_syracusePassLocationLaw_sub_windowTV_le
    (B := B) (lo₁ := lo₁) (hi₁ := hi₁) (lo₂ := lo₂) (hi₂ := hi₂)
    hB hmass₁ hmass₂ A
  have htarget := pass_prob_sub_noHit_le_source_event_prob
    (B := B) (lo := lo₂) (hi := hi₂) hB hmass₂ A Good₂ hGood₂
  linarith

theorem source_event_two_window_logCount_lower_bound
    {lo₁ hi₁ lo₂ hi₂ B : ℕ} (hB : 1 ≤ B)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (A : Set {M : ℕ // M ≤ B}) (Good₁ Good₂ : Set ℕ)
    (p eNoHit₁ eTV eNoHit₂ : ℝ)
    (hPass₁ : ∀ N : ℕ, N ∈ oddLogWindow lo₁ hi₁ →
      N ∉ syracuseNoHitAtMost B →
      N ∈ Good₁ → syracusePassLocationOrOne B N hB ∈ A)
    (hGood₂ : ∀ N : ℕ, N ∈ oddLogWindow lo₂ hi₂ →
      N ∉ syracuseNoHitAtMost B →
      syracusePassLocationOrOne B N hB ∈ A → N ∈ Good₂)
    (hsrc : p ≤ logFinsetProb (oddLogWindow lo₁ hi₁) Good₁)
    (hno₁ : syracuseNoHitWindowProb B lo₁ hi₁ hmass₁ ≤ eNoHit₁)
    (htv : syracusePassWindowTV B lo₁ hi₁ lo₂ hi₂ hB hmass₁ hmass₂ ≤ eTV)
    (hno₂ : syracuseNoHitWindowProb B lo₂ hi₂ hmass₂ ≤ eNoHit₂) :
    (p - eNoHit₁ - eTV - eNoHit₂) *
        logCount (oddLogWindowSet lo₂ hi₂) hi₂ ≤
      logCount (oddLogWindowSet lo₂ hi₂ ∩ Good₂) hi₂ := by
  have hstep := source_event_prob_two_window_step
    (B := B) (lo₁ := lo₁) (hi₁ := hi₁) (lo₂ := lo₂) (hi₂ := hi₂)
    hB hmass₁ hmass₂ A Good₁ Good₂ hPass₁ hGood₂
  have hprob :
      p - eNoHit₁ - eTV - eNoHit₂ ≤
        logFinsetProb (oddLogWindow lo₂ hi₂) Good₂ := by
    linarith
  exact logCount_oddWindow_inter_ge_of_logFinsetProb_ge hmass₂ hprob

/--
Proposition 1.11 stabilization socket over finite logarithmic windows.

The concrete `N_y = Log(2ℕ+1 ∩ [y, y^α])` endpoint policy and quantitative
error rates are left to later modules; `WindowPair` is the future endpoint
relation connecting the two compared source windows.
-/
def TaoProp111FirstPassageStabilizationSocket
    (WindowPair : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ errNoHit errTV : ℕ → ℝ,
    Tendsto errNoHit atTop (nhds 0) ∧
      Tendsto errTV atTop (nhds 0) ∧
        ∀ B lo₁ hi₁ lo₂ hi₂ : ℕ,
          (hB : 1 ≤ B) →
            WindowPair B lo₁ hi₁ lo₂ hi₂ →
              ∀ (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
                (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)),
                    syracuseNoHitWindowProb B lo₁ hi₁ hmass₁ ≤ errNoHit B ∧
                      syracuseNoHitWindowProb B lo₂ hi₂ hmass₂ ≤ errNoHit B ∧
                        syracusePassWindowTV B lo₁ hi₁ lo₂ hi₂ hB hmass₁ hmass₂
                          ≤ errTV B

/--
Rate-bearing Proposition 1.11 stabilization socket.

The weak stabilization socket above is useful for naming convergence, but the
Section 3 scale telescope needs summable rate information.  This statement
surface records polynomial no-hit decay and logarithmic-power TV decay without
yet proving either estimate.
-/
def TaoProp111FirstPassageStabilizationRateSocket
    (WindowPair : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ errNoHit errTV : ℕ → ℝ,
    ∃ C c : ℝ,
      0 ≤ C ∧ 0 < c ∧
        (∀ᶠ B : ℕ in atTop,
          0 ≤ errNoHit B ∧
            0 ≤ errTV B ∧
              errNoHit B ≤ C * ((B : ℝ) ^ (-c)) ∧
                errTV B ≤ C * ((Real.log (B : ℝ)) ^ (-c))) ∧
          ∀ B lo₁ hi₁ lo₂ hi₂ : ℕ,
            (hB : 1 ≤ B) →
              WindowPair B lo₁ hi₁ lo₂ hi₂ →
                ∀ (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
                  (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)),
                    syracuseNoHitWindowProb B lo₁ hi₁ hmass₁ ≤ errNoHit B ∧
                      syracuseNoHitWindowProb B lo₂ hi₂ hmass₂ ≤ errNoHit B ∧
                        syracusePassWindowTV B lo₁ hi₁ lo₂ hi₂ hB hmass₁ hmass₂
                          ≤ errTV B

/-- Abstract finite-chain error-budget socket for a Section 3 geometric scale telescope. -/
def Section3FiniteGeometricErrorBudget
    (totalErr : ℕ → ℝ) (stepErr : ℕ → ℕ → ℝ) : Prop :=
  Tendsto totalErr atTop (nhds 0) ∧
    ∀ B₀ : ℕ, 2 ≤ B₀ →
      ∀ J : ℕ,
        (∑ j ∈ Finset.range J, stepErr B₀ j) ≤ totalErr B₀

theorem section3_budgeted_telescope_lower_bound
    (p : ℕ → ℕ → ℝ) (stepErr : ℕ → ℕ → ℝ)
    (totalErr baseErr : ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : ∀ B₀ : ℕ, 2 ≤ B₀ → 1 - baseErr B₀ ≤ p B₀ 0)
    (hstep : ∀ B₀ : ℕ, 2 ≤ B₀ → ∀ j : ℕ,
      p B₀ j - stepErr B₀ j ≤ p B₀ (j + 1)) :
    ∀ B₀ : ℕ, 2 ≤ B₀ → ∀ J : ℕ,
      1 - (baseErr B₀ + totalErr B₀) ≤ p B₀ J := by
  intro B₀ hB₀ J
  exact finite_telescope_lower_bound_of_sum_le
    (p B₀) (stepErr B₀) (baseErr B₀) (totalErr B₀) J
    (hbase B₀ hB₀) (hstep B₀ hB₀) (hbudget.2 B₀ hB₀ J)

theorem section3_total_error_tendsto_zero
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0)) :
    Tendsto (fun B₀ : ℕ => baseErr B₀ + totalErr B₀) atTop (nhds 0) := by
  simpa using hbase.add hbudget.1

theorem taoTheorem31_of_budgeted_eventual_lower_bound
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hlower : ∀ B : ℕ, 2 ≤ B → ∀ᶠ X in atTop,
      (1 / 2 : ℝ) - (baseErr B + totalErr B) ≤
        logCountingRatio (syracuseThresholdGood B) X) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  refine ⟨fun B : ℕ => baseErr B + totalErr B, ?_, ?_⟩
  · exact section3_total_error_tendsto_zero stepErr totalErr baseErr hbudget hbase
  · exact hlower

theorem taoTheorem31_of_eventually_large_syracuseThresholdLowerBound
    (eps : ℕ → ℝ)
    (heps : Tendsto eps atTop (nhds 0))
    (hlarge : ∀ᶠ B : ℕ in atTop,
      2 ≤ B → ∀ᶠ X in atTop,
        (1 / 2 : ℝ) - eps B ≤ logCountingRatio (syracuseThresholdGood B) X) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  rcases eventually_atTop.mp hlarge with ⟨B₀, hB₀⟩
  let eps' : ℕ → ℝ := fun B => if B < B₀ then (1 / 2 : ℝ) else eps B
  refine ⟨eps', ?_, ?_⟩
  · refine heps.congr' ?_
    refine eventually_atTop.mpr ⟨B₀, ?_⟩
    intro B hB
    simp [eps', not_lt.mpr hB]
  · intro B hB
    by_cases hsmall : B < B₀
    · filter_upwards [logCountingRatio_nonneg_eventually (syracuseThresholdGood B)] with X hnonneg
      simpa [eps', hsmall] using hnonneg
    · filter_upwards [hB₀ B (le_of_not_gt hsmall) hB] with X hX
      simpa [eps', hsmall] using hX

theorem taoTheorem31_of_budgeted_eventually_large_lower_bound
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hlarge : ∀ᶠ B : ℕ in atTop,
      2 ≤ B → ∀ᶠ X in atTop,
        (1 / 2 : ℝ) - (baseErr B + totalErr B) ≤
          logCountingRatio (syracuseThresholdGood B) X) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  exact taoTheorem31_of_eventually_large_syracuseThresholdLowerBound
    (fun B : ℕ => baseErr B + totalErr B)
    (section3_total_error_tendsto_zero stepErr totalErr baseErr hbudget hbase)
    hlarge

theorem section3_final_arithmetic_of_exact_defect {η ρ e : ℝ}
    (h : ((1 / 2 : ℝ) - ρ) + η * ρ ≤ e) :
    (1 / 2 : ℝ) - e ≤ (1 - η) * ρ := by
  nlinarith

theorem section3_final_arithmetic_of_cover_defect_nohit_half {η ρ δ e : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hδ0 : 0 ≤ δ)
    (hrho : (1 / 2 : ℝ) - δ ≤ ρ)
    (he : δ + η / 2 ≤ e) :
    (1 / 2 : ℝ) - e ≤ (1 - η) * ρ := by
  have hnonneg : 0 ≤ 1 - η := by linarith
  have hmul : (1 - η) * ((1 / 2 : ℝ) - δ) ≤ (1 - η) * ρ := by
    exact mul_le_mul_of_nonneg_left hrho hnonneg
  have hηδ : 0 ≤ η * δ := mul_nonneg hη0 hδ0
  nlinarith

theorem section3_final_arithmetic_of_cover_defect_nohit_unit {η ρ δ e : ℝ}
    (hη0 : 0 ≤ η)
    (hrhoLower : (1 / 2 : ℝ) - δ ≤ ρ) (hrhoUpper : ρ ≤ 1)
    (he : δ + η ≤ e) :
    (1 / 2 : ℝ) - e ≤ (1 - η) * ρ := by
  have hsharp : ((1 / 2 : ℝ) - ρ) + η * ρ ≤ e := by
    have hcover : (1 / 2 : ℝ) - ρ ≤ δ := by linarith
    have hηρ : η * ρ ≤ η := by
      exact mul_le_of_le_one_right hη0 hrhoUpper
    nlinarith
  exact section3_final_arithmetic_of_exact_defect hsharp

/-- First source scale in the integer-threshold specialization of Proposition 1.11. -/
noncomputable def taoProp111Y1 (B : ℕ) : ℝ :=
  (B : Real) ^ taoAlpha

/-- Second source scale in the integer-threshold specialization of Proposition 1.11. -/
noncomputable def taoProp111Y2 (B : ℕ) : ℝ :=
  (B : Real) ^ (taoAlpha ^ 2)

/--
Concrete endpoint relation for the integer-threshold specialization of Tao's
Proposition 1.11 paired windows.

This relation is intentionally pure endpoint data.  The stabilization socket
already carries the positive-mass hypotheses for the two finite windows.
-/
def TaoProp111WindowPair (B lo1 hi1 lo2 hi2 : ℕ) : Prop :=
  lo1 = taoNyLo (taoProp111Y1 B) ∧
    hi1 = taoNyHi (taoProp111Y1 B) taoAlpha ∧
      lo2 = taoNyLo (taoProp111Y2 B) ∧
        hi2 = taoNyHi (taoProp111Y2 B) taoAlpha

/-- First source scale in the real-threshold form of Proposition 1.11. -/
noncomputable def taoProp111RealY1 (x : ℝ) : ℝ :=
  x ^ taoAlpha

/-- Second source scale in the real-threshold form of Proposition 1.11. -/
noncomputable def taoProp111RealY2 (x : ℝ) : ℝ :=
  x ^ (taoAlpha ^ 2)

/-- Concrete endpoint relation for Tao's real-threshold Proposition 1.11 window pair. -/
def TaoProp111RealWindowPair (x : ℝ) (lo1 hi1 lo2 hi2 : ℕ) : Prop :=
  lo1 = taoNyLo (taoProp111RealY1 x) ∧
    hi1 = taoNyHi (taoProp111RealY1 x) taoAlpha ∧
      lo2 = taoNyLo (taoProp111RealY2 x) ∧
        hi2 = taoNyHi (taoProp111RealY2 x) taoAlpha

/--
Floor-lift a real-threshold window pair to the existing natural-threshold
Proposition 1.11 socket.
-/
def TaoFloorLiftWindowPair
    (RealWindowPair : ℝ → ℕ → ℕ → ℕ → ℕ → Prop)
    (B lo1 hi1 lo2 hi2 : ℕ) : Prop :=
  ∃ x : ℝ, 1 ≤ x ∧ B = Nat.floor x ∧
    RealWindowPair x lo1 hi1 lo2 hi2

/--
Real-threshold Proposition 1.11 socket using the real-floor pass-location and
no-hit wrappers, with errors indexed by `Nat.floor x`.
-/
def TaoRealFirstPassageStabilizationSocket
    (RealWindowPair : ℝ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ errNoHit errTV : ℕ → ℝ,
    Tendsto errNoHit atTop (nhds 0) ∧
      Tendsto errTV atTop (nhds 0) ∧
        ∀ x lo₁ hi₁ lo₂ hi₂,
          (hx : 1 ≤ x) →
            RealWindowPair x lo₁ hi₁ lo₂ hi₂ →
              ∀ (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
                (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)),
                    syracuseNoHitRealWindowProb x lo₁ hi₁ hmass₁ ≤
                        errNoHit (Nat.floor x) ∧
                      syracuseNoHitRealWindowProb x lo₂ hi₂ hmass₂ ≤
                        errNoHit (Nat.floor x) ∧
                        syracusePassRealFloorWindowTV x lo₁ hi₁ lo₂ hi₂ hx
                          hmass₁ hmass₂ ≤ errTV (Nat.floor x)

/--
A natural-threshold Proposition 1.11 socket over floor-lifted windows implies
the real-threshold socket.
-/
theorem TaoRealFirstPassageStabilizationSocket_of_nat_floor_socket
    {RealWindowPair : ℝ → ℕ → ℕ → ℕ → ℕ → Prop}
    (h : TaoProp111FirstPassageStabilizationSocket
      (TaoFloorLiftWindowPair RealWindowPair)) :
    TaoRealFirstPassageStabilizationSocket RealWindowPair := by
  rcases h with ⟨errNoHit, errTV, herrNoHit, herrTV, hnat⟩
  refine ⟨errNoHit, errTV, herrNoHit, herrTV, ?_⟩
  intro x lo₁ hi₁ lo₂ hi₂ hx hpair hmass₁ hmass₂
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hfloor : 1 ≤ Nat.floor x := one_le_floor_of_one_le hx
  have hnat_pair :
      TaoFloorLiftWindowPair RealWindowPair (Nat.floor x) lo₁ hi₁ lo₂ hi₂ :=
    ⟨x, hx, rfl, hpair⟩
  rcases hnat (Nat.floor x) lo₁ hi₁ lo₂ hi₂ hfloor hnat_pair hmass₁ hmass₂ with
    ⟨hno₁, hno₂, htv⟩
  constructor
  · simpa [syracuseNoHitRealWindowProb_eq_floor hx0 lo₁ hi₁ hmass₁] using hno₁
  constructor
  · simpa [syracuseNoHitRealWindowProb_eq_floor hx0 lo₂ hi₂ hmass₂] using hno₂
  · simpa [syracusePassRealFloorWindowTV_eq_floor x lo₁ hi₁ lo₂ hi₂ hx hmass₁ hmass₂]
      using htv

/-- Concrete integer-threshold Proposition 1.11 first-passage stabilization socket. -/
def TaoProp111ConcreteFirstPassageStabilizationStatement : Prop :=
  TaoProp111FirstPassageStabilizationSocket TaoProp111WindowPair

/-- Natural-threshold socket for the real Proposition 1.11 windows after floor-lift. -/
def TaoProp111RealFloorNatSocketStatement : Prop :=
  TaoProp111FirstPassageStabilizationSocket
    (TaoFloorLiftWindowPair TaoProp111RealWindowPair)

/-- Real-threshold Proposition 1.11 first-passage stabilization socket. -/
def TaoProp111RealFirstPassageStabilizationStatement : Prop :=
  TaoRealFirstPassageStabilizationSocket TaoProp111RealWindowPair

/-- Concrete integer-threshold rate-bearing Proposition 1.11 stabilization socket. -/
def TaoProp111ConcreteFirstPassageStabilizationRateStatement : Prop :=
  TaoProp111FirstPassageStabilizationRateSocket TaoProp111WindowPair

theorem taoProp111Rate_source_event_two_window_logCount_step
    (h111 : TaoProp111ConcreteFirstPassageStabilizationRateStatement) :
    ∃ errNoHit errTV : ℕ → ℝ,
      ∃ C c : ℝ,
        0 ≤ C ∧ 0 < c ∧
          (∀ᶠ B : ℕ in atTop,
            0 ≤ errNoHit B ∧
              0 ≤ errTV B ∧
                errNoHit B ≤ C * ((B : ℝ) ^ (-c)) ∧
                  errTV B ≤ C * ((Real.log (B : ℝ)) ^ (-c))) ∧
          ∀ {B lo₁ hi₁ lo₂ hi₂ : ℕ},
            (hB : 1 ≤ B) →
            TaoProp111WindowPair B lo₁ hi₁ lo₂ hi₂ →
            ∀ (_hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
              (_hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
              (A : Set {M : ℕ // M ≤ B}) (Good₁ Good₂ : Set ℕ) (p : ℝ),
              (∀ N : ℕ, N ∈ oddLogWindow lo₁ hi₁ →
                N ∉ syracuseNoHitAtMost B →
                N ∈ Good₁ → syracusePassLocationOrOne B N hB ∈ A) →
              (∀ N : ℕ, N ∈ oddLogWindow lo₂ hi₂ →
                N ∉ syracuseNoHitAtMost B →
                syracusePassLocationOrOne B N hB ∈ A → N ∈ Good₂) →
              p ≤ logFinsetProb (oddLogWindow lo₁ hi₁) Good₁ →
              (p - errNoHit B - errTV B - errNoHit B) *
                  logCount (oddLogWindowSet lo₂ hi₂) hi₂ ≤
                logCount (oddLogWindowSet lo₂ hi₂ ∩ Good₂) hi₂ := by
  rcases h111 with ⟨errNoHit, errTV, C, c, hC, hc, hrate, hbounds⟩
  refine ⟨errNoHit, errTV, C, c, hC, hc, hrate, ?_⟩
  intro B lo₁ hi₁ lo₂ hi₂ hB hpair hmass₁ hmass₂ A Good₁ Good₂ p hPass₁ hGood₂ hsrc
  rcases hbounds B lo₁ hi₁ lo₂ hi₂ hB hpair hmass₁ hmass₂ with ⟨hno₁, hno₂, htv⟩
  exact source_event_two_window_logCount_lower_bound
    (B := B) (lo₁ := lo₁) (hi₁ := hi₁) (lo₂ := lo₂) (hi₂ := hi₂)
    hB hmass₁ hmass₂ A Good₁ Good₂ p (errNoHit B) (errTV B) (errNoHit B)
    hPass₁ hGood₂ hsrc hno₁ htv hno₂

theorem eventually_taoProp111Y1_window_mass_pos :
    ∀ᶠ B : ℕ in atTop,
      0 < logFinsetMass
        (oddLogWindow (taoNyLo (taoProp111Y1 B))
          (taoNyHi (taoProp111Y1 B) taoAlpha)) := by
  filter_upwards [support_guard_comp_nat_rpow taoNy_width_eventually taoAlpha_pos] with B hwidth
  change 0 < logFinsetMass (taoNyOddWindow (taoProp111Y1 B) taoAlpha)
  exact logFinsetMass_taoNyOddWindow_pos_of_width
    (Real.rpow_nonneg (Nat.cast_nonneg B) taoAlpha) hwidth

theorem eventually_taoProp111Y2_window_mass_pos :
    ∀ᶠ B : ℕ in atTop,
      0 < logFinsetMass
        (oddLogWindow (taoNyLo (taoProp111Y2 B))
          (taoNyHi (taoProp111Y2 B) taoAlpha)) := by
  filter_upwards [support_guard_comp_nat_rpow taoNy_width_eventually taoAlpha_sq_pos] with B hwidth
  change 0 < logFinsetMass (taoNyOddWindow (taoProp111Y2 B) taoAlpha)
  exact logFinsetMass_taoNyOddWindow_pos_of_width
    (Real.rpow_nonneg (Nat.cast_nonneg B) (taoAlpha ^ 2)) hwidth

theorem syracuseNoHitWindowProb_eq_logCount_ratio
    (B lo hi : ℕ) (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    syracuseNoHitWindowProb B lo hi hmass =
      logCount (oddLogWindowSet lo hi ∩ syracuseNoHitAtMost B) hi /
        logCount (oddLogWindowSet lo hi) hi := by
  rw [syracuseNoHitWindowProb, pmfProb_oddLogWindowPMF,
    logFinsetProb_oddLogWindow_eq_logCount_ratio]

theorem logCount_noHitWindow_le_of_prob_le {B lo hi : ℕ} {eps : ℝ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (hprob : syracuseNoHitWindowProb B lo hi hmass ≤ eps) :
    logCount (syracuseNoHitAtMost B ∩ oddLogWindowSet lo hi) hi ≤
      eps * logCount (oddLogWindowSet lo hi) hi := by
  have hratio :
      logCount (syracuseNoHitAtMost B ∩ oddLogWindowSet lo hi) hi /
          logCount (oddLogWindowSet lo hi) hi ≤ eps := by
    simpa [syracuseNoHitWindowProb_eq_logCount_ratio B lo hi hmass, Set.inter_comm]
      using hprob
  exact logCount_inter_le_mul_of_ratio_le hratio

theorem odd_noHit_subset_syracuseThresholdGood {B : ℕ} {W : Set ℕ}
    (hodd : ∀ n, n ∈ W → Odd n) :
    W \ syracuseNoHitAtMost B ⊆ syracuseThresholdGood B := by
  intro n hn
  exact ⟨hodd n hn.1, by simpa [syracuseNoHitAtMost] using hn.2⟩

theorem logCount_window_diff_noHit_le_good {B N : ℕ} {W : Set ℕ}
    (hodd : ∀ n, n ∈ W → Odd n) :
    logCount (W \ syracuseNoHitAtMost B) N ≤
      logCount (syracuseThresholdGood B) N := by
  exact logCount_mono (odd_noHit_subset_syracuseThresholdGood (B := B) (W := W) hodd) N

theorem logCount_syracuseThresholdGood_ge_window_of_noHit_le
    {B N : ℕ} {W : Set ℕ} {eta : ℝ}
    (hodd : ∀ n, n ∈ W → Odd n)
    (hbad : logCount (syracuseNoHitAtMost B ∩ W) N ≤ eta * logCount W N) :
    (1 - eta) * logCount W N ≤ logCount (syracuseThresholdGood B) N := by
  calc
    (1 - eta) * logCount W N ≤ logCount (W \ syracuseNoHitAtMost B) N := by
      exact logCount_window_diff_ge_of_bad_inter_le hbad
    _ ≤ logCount (syracuseThresholdGood B) N := by
      exact logCount_window_diff_noHit_le_good (B := B) (N := N) (W := W) hodd

theorem logCount_syracuseThresholdGood_ge_oddWindow_of_noHit_le
    {B lo hi : ℕ} {eta : ℝ}
    (hbad :
      logCount (syracuseNoHitAtMost B ∩ oddLogWindowSet lo hi) hi ≤
        eta * logCount (oddLogWindowSet lo hi) hi) :
    (1 - eta) * logCount (oddLogWindowSet lo hi) hi ≤
      logCount (syracuseThresholdGood B) hi := by
  have hoddWindow : ∀ n, n ∈ oddLogWindowSet lo hi → Odd n := by
    intro n hn
    exact Nat.odd_iff.mpr (oddLogWindowSet_mem.mp hn).2.2
  exact logCount_syracuseThresholdGood_ge_window_of_noHit_le
    (B := B) (N := hi) (W := oddLogWindowSet lo hi) hoddWindow hbad

theorem logCountingRatio_syracuseThresholdGood_ge_of_endpoint_oddWindow_noHit_bounds
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (lo hi : ι → ℕ) (B X : ℕ) (η ρ c : ℝ)
    (hX : 0 < X) (hη : 0 ≤ 1 - η)
    (hhiX : ∀ i ∈ I, hi i ≤ X)
    (hpairW : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (oddLogWindowSet (lo i) (hi i)) (oddLogWindowSet (lo j) (hi j)))
    (hbad : ∀ i ∈ I,
      logCount (syracuseNoHitAtMost B ∩ oddLogWindowSet (lo i) (hi i)) (hi i) ≤
        η * logCount (oddLogWindowSet (lo i) (hi i)) (hi i))
    (hcover : ρ * logMass X ≤
      ∑ i ∈ I, logCount (oddLogWindowSet (lo i) (hi i)) X)
    (hc : c ≤ (1 - η) * ρ) :
    c ≤ logCountingRatio (syracuseThresholdGood B) X := by
  refine logCountingRatio_ge_of_endpoint_window_inter_lower_bounds
    I (fun i => oddLogWindowSet (lo i) (hi i)) hi
    (fun _i => (syracuseNoHitAtMost B)ᶜ)
    (syracuseThresholdGood B) X (1 - η) ρ c
    hX hη ?hsupport hhiX hpairW ?hlocal ?hlower hcover hc
  · intro i _hiI
    exact oddLogWindowSet_subset_Iic (lo i) (hi i)
  · intro i _hiI n hn
    have hodd : ∀ n, n ∈ oddLogWindowSet (lo i) (hi i) → Odd n := by
      intro n hn
      exact Nat.odd_iff.mpr (oddLogWindowSet_mem.mp hn).2.2
    exact odd_noHit_subset_syracuseThresholdGood (B := B)
      (W := oddLogWindowSet (lo i) (hi i)) hodd ⟨hn.1, hn.2⟩
  · intro i hiI
    simpa [Set.diff_eq] using
      (logCount_window_diff_ge_of_bad_inter_le
        (bad := syracuseNoHitAtMost B)
        (window := oddLogWindowSet (lo i) (hi i))
        (η := η) (N := hi i) (hbad i hiI))

/-- One finite `X` payload for odd-window no-hit probability cover packaging. -/
def Section3OddWindowNoHitProbabilityCoverPayload
    (B X : ℕ) (I : Finset ℕ) (lo hi : ℕ → ℕ) (η ρ c : ℝ) : Prop :=
  ∃ hmass : ∀ i, i ∈ I → 0 < logFinsetMass (oddLogWindow (lo i) (hi i)),
    0 ≤ 1 - η ∧
      (∀ i ∈ I, hi i ≤ X) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        Disjoint (oddLogWindowSet (lo i) (hi i)) (oddLogWindowSet (lo j) (hi j))) ∧
      (∀ i, ∀ hiI : i ∈ I,
        syracuseNoHitWindowProb B (lo i) (hi i) (hmass i hiI) ≤ η) ∧
      ρ * logMass X ≤ ∑ i ∈ I, logCount (oddLogWindowSet (lo i) (hi i)) X ∧
      c ≤ (1 - η) * ρ

theorem Section3OddWindowNoHitProbabilityCoverPayload.of_cover_defect_nohit_half
    {B X : ℕ} {I : Finset ℕ} {lo hi : ℕ → ℕ} {η ρ δ e : ℝ}
    (hmass : ∀ i, i ∈ I → 0 < logFinsetMass (oddLogWindow (lo i) (hi i)))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hδ0 : 0 ≤ δ)
    (hhiX : ∀ i ∈ I, hi i ≤ X)
    (hpairW : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (oddLogWindowSet (lo i) (hi i)) (oddLogWindowSet (lo j) (hi j)))
    (hprob : ∀ i, ∀ hiI : i ∈ I,
      syracuseNoHitWindowProb B (lo i) (hi i) (hmass i hiI) ≤ η)
    (hrho : (1 / 2 : ℝ) - δ ≤ ρ)
    (hcoverMass : ρ * logMass X ≤
      ∑ i ∈ I, logCount (oddLogWindowSet (lo i) (hi i)) X)
    (he : δ + η / 2 ≤ e) :
    Section3OddWindowNoHitProbabilityCoverPayload B X I lo hi η ρ ((1 / 2 : ℝ) - e) := by
  refine ⟨hmass, ?_, hhiX, hpairW, hprob, hcoverMass, ?_⟩
  · linarith
  · exact section3_final_arithmetic_of_cover_defect_nohit_half hη0 hη1 hδ0 hrho he

theorem Section3OddWindowNoHitProbabilityCoverPayload.of_ordered_gaps_cover_defect_nohit_half
    {B X : ℕ} {I : Finset ℕ} {lo hi : ℕ → ℕ} {η ρ δ e : ℝ}
    (hmass : ∀ i, i ∈ I → 0 < logFinsetMass (oddLogWindow (lo i) (hi i)))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hδ0 : 0 ≤ δ)
    (hhiX : ∀ i ∈ I, hi i ≤ X)
    (hgap : ∀ i ∈ I, ∀ j ∈ I, i < j → hi i < lo j)
    (hprob : ∀ i, ∀ hiI : i ∈ I,
      syracuseNoHitWindowProb B (lo i) (hi i) (hmass i hiI) ≤ η)
    (hrho : (1 / 2 : ℝ) - δ ≤ ρ)
    (hcoverMass : ρ * logMass X ≤
      ∑ i ∈ I, logCount (oddLogWindowSet (lo i) (hi i)) X)
    (he : δ + η / 2 ≤ e) :
    Section3OddWindowNoHitProbabilityCoverPayload B X I lo hi η ρ ((1 / 2 : ℝ) - e) := by
  exact Section3OddWindowNoHitProbabilityCoverPayload.of_cover_defect_nohit_half
    hmass hη0 hη1 hδ0 hhiX
    (oddLogWindowSet_pairwise_disjoint_of_ordered_gaps I lo hi hgap)
    hprob hrho hcoverMass he

theorem logCountingRatio_syracuseThresholdGood_ge_of_oddWindow_noHit_probability_cover_payload
    {B X : ℕ} {I : Finset ℕ} {lo hi : ℕ → ℕ} {η ρ c : ℝ}
    (hX : 0 < X)
    (hpayload : Section3OddWindowNoHitProbabilityCoverPayload B X I lo hi η ρ c) :
    c ≤ logCountingRatio (syracuseThresholdGood B) X := by
  rcases hpayload with ⟨hmass, hη, hhiX, hpairW, hprob, hcoverMass, hc⟩
  have hbad : ∀ i ∈ I,
      logCount (syracuseNoHitAtMost B ∩ oddLogWindowSet (lo i) (hi i)) (hi i) ≤
        η * logCount (oddLogWindowSet (lo i) (hi i)) (hi i) := by
    intro i hiI
    exact logCount_noHitWindow_le_of_prob_le
      (B := B) (lo := lo i) (hi := hi i) (eps := η)
      (hmass i hiI) (hprob i hiI)
  exact logCountingRatio_syracuseThresholdGood_ge_of_endpoint_oddWindow_noHit_bounds
    I lo hi B X η ρ c hX hη hhiX hpairW hbad hcoverMass hc

theorem taoTheorem31_of_budgeted_eventual_oddWindow_noHit_endpoint_cover
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (I : ℕ → ℕ → Finset ℕ) (lo hi : ℕ → ℕ → ℕ → ℕ)
    (η ρ : ℕ → ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hcover : ∀ B : ℕ, 2 ≤ B → ∀ᶠ X in atTop,
      0 ≤ 1 - η B X ∧
      (∀ i ∈ I B X, hi B X i ≤ X) ∧
      (∀ i ∈ I B X, ∀ j ∈ I B X, i ≠ j →
        Disjoint (oddLogWindowSet (lo B X i) (hi B X i))
          (oddLogWindowSet (lo B X j) (hi B X j))) ∧
      (∀ i ∈ I B X,
        logCount (syracuseNoHitAtMost B ∩ oddLogWindowSet (lo B X i) (hi B X i))
            (hi B X i) ≤
          η B X * logCount (oddLogWindowSet (lo B X i) (hi B X i)) (hi B X i)) ∧
      ρ B X * logMass X ≤
        ∑ i ∈ I B X, logCount (oddLogWindowSet (lo B X i) (hi B X i)) X ∧
      (1 / 2 : ℝ) - (baseErr B + totalErr B) ≤ (1 - η B X) * ρ B X) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  refine taoTheorem31_of_budgeted_eventual_lower_bound
    stepErr totalErr baseErr hbudget hbase ?_
  intro B hB
  have hXpos : ∀ᶠ X in atTop, 0 < X :=
    eventually_atTop.mpr ⟨1, fun X hX => lt_of_lt_of_le zero_lt_one hX⟩
  filter_upwards [hXpos, hcover B hB] with X hX hdata
  rcases hdata with ⟨hη, hhiX, hpairW, hbad, hcoverMass, hc⟩
  exact logCountingRatio_syracuseThresholdGood_ge_of_endpoint_oddWindow_noHit_bounds
    (I B X) (lo B X) (hi B X) B X (η B X) (ρ B X)
    ((1 / 2 : ℝ) - (baseErr B + totalErr B))
    hX hη hhiX hpairW hbad hcoverMass hc

theorem taoTheorem31_of_budgeted_eventual_oddWindow_noHit_probability_cover
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (I : ℕ → ℕ → Finset ℕ) (lo hi : ℕ → ℕ → ℕ → ℕ)
    (η ρ : ℕ → ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hcover : ∀ B : ℕ, 2 ≤ B → ∀ᶠ X in atTop,
      ∃ hmass : ∀ i, i ∈ I B X →
          0 < logFinsetMass (oddLogWindow (lo B X i) (hi B X i)),
        0 ≤ 1 - η B X ∧
        (∀ i ∈ I B X, hi B X i ≤ X) ∧
        (∀ i ∈ I B X, ∀ j ∈ I B X, i ≠ j →
          Disjoint (oddLogWindowSet (lo B X i) (hi B X i))
            (oddLogWindowSet (lo B X j) (hi B X j))) ∧
        (∀ i, ∀ hiI : i ∈ I B X,
          syracuseNoHitWindowProb B (lo B X i) (hi B X i) (hmass i hiI) ≤ η B X) ∧
        ρ B X * logMass X ≤
          ∑ i ∈ I B X, logCount (oddLogWindowSet (lo B X i) (hi B X i)) X ∧
        (1 / 2 : ℝ) - (baseErr B + totalErr B) ≤ (1 - η B X) * ρ B X) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  refine taoTheorem31_of_budgeted_eventual_oddWindow_noHit_endpoint_cover
    stepErr totalErr baseErr I lo hi η ρ hbudget hbase ?_
  intro B hB
  filter_upwards [hcover B hB] with X hdata
  rcases hdata with ⟨hmass, hη, hhiX, hpairW, hprob, hcoverMass, hc⟩
  refine ⟨hη, hhiX, hpairW, ?_, hcoverMass, hc⟩
  intro i hiI
  exact logCount_noHitWindow_le_of_prob_le
    (B := B) (lo := lo B X i) (hi := hi B X i) (eps := η B X)
    (hmass i hiI) (hprob i hiI)

theorem taoTheorem31_of_budgeted_eventual_oddWindow_noHit_probability_cover_payload
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (I : ℕ → ℕ → Finset ℕ) (lo hi : ℕ → ℕ → ℕ → ℕ)
    (η ρ : ℕ → ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hcover : ∀ B : ℕ, 2 ≤ B → ∀ᶠ X in atTop,
      Section3OddWindowNoHitProbabilityCoverPayload B X (I B X) (lo B X) (hi B X)
        (η B X) (ρ B X) ((1 / 2 : ℝ) - (baseErr B + totalErr B))) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  refine taoTheorem31_of_budgeted_eventual_lower_bound
    stepErr totalErr baseErr hbudget hbase ?_
  intro B hB
  have hXpos : ∀ᶠ X in atTop, 0 < X :=
    eventually_atTop.mpr ⟨1, fun X hX => lt_of_lt_of_le zero_lt_one hX⟩
  filter_upwards [hXpos, hcover B hB] with X hX hpayload
  exact logCountingRatio_syracuseThresholdGood_ge_of_oddWindow_noHit_probability_cover_payload
    hX hpayload

theorem taoTheorem31_of_budgeted_eventual_oddWindow_noHit_cover_defect_half_payload
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (I : ℕ → ℕ → Finset ℕ) (lo hi : ℕ → ℕ → ℕ → ℕ)
    (η ρ δ : ℕ → ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hcover : ∀ B : ℕ, 2 ≤ B → ∀ᶠ X in atTop,
      ∃ hmass : ∀ i, i ∈ I B X →
          0 < logFinsetMass (oddLogWindow (lo B X i) (hi B X i)),
        0 ≤ η B X ∧
        η B X ≤ 1 ∧
        0 ≤ δ B X ∧
        (∀ i ∈ I B X, hi B X i ≤ X) ∧
        (∀ i ∈ I B X, ∀ j ∈ I B X, i ≠ j →
          Disjoint (oddLogWindowSet (lo B X i) (hi B X i))
            (oddLogWindowSet (lo B X j) (hi B X j))) ∧
        (∀ i, ∀ hiI : i ∈ I B X,
          syracuseNoHitWindowProb B (lo B X i) (hi B X i) (hmass i hiI) ≤ η B X) ∧
        (1 / 2 : ℝ) - δ B X ≤ ρ B X ∧
        ρ B X * logMass X ≤
          ∑ i ∈ I B X, logCount (oddLogWindowSet (lo B X i) (hi B X i)) X ∧
        δ B X + η B X / 2 ≤ baseErr B + totalErr B) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  refine taoTheorem31_of_budgeted_eventual_oddWindow_noHit_probability_cover_payload
    stepErr totalErr baseErr I lo hi η ρ hbudget hbase ?_
  intro B hB
  filter_upwards [hcover B hB] with X hdata
  rcases hdata with ⟨hmass, hη0, hη1, hδ0, hhiX, hpairW, hprob, hrho,
    hcoverMass, hfinal⟩
  exact Section3OddWindowNoHitProbabilityCoverPayload.of_cover_defect_nohit_half
    hmass hη0 hη1 hδ0 hhiX hpairW hprob hrho hcoverMass hfinal

theorem taoTheorem31_of_budgeted_eventually_large_oddWindow_noHit_probability_cover_payload
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (I : ℕ → ℕ → Finset ℕ) (lo hi : ℕ → ℕ → ℕ → ℕ)
    (η ρ : ℕ → ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hcover : ∀ᶠ B : ℕ in atTop,
      2 ≤ B → ∀ᶠ X in atTop,
        Section3OddWindowNoHitProbabilityCoverPayload B X (I B X) (lo B X) (hi B X)
          (η B X) (ρ B X) ((1 / 2 : ℝ) - (baseErr B + totalErr B))) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  refine taoTheorem31_of_budgeted_eventually_large_lower_bound
    stepErr totalErr baseErr hbudget hbase ?_
  filter_upwards [hcover] with B hcoverB
  intro hB
  have hXpos : ∀ᶠ X in atTop, 0 < X :=
    eventually_atTop.mpr ⟨1, fun X hX => lt_of_lt_of_le zero_lt_one hX⟩
  filter_upwards [hXpos, hcoverB hB] with X hX hpayload
  exact logCountingRatio_syracuseThresholdGood_ge_of_oddWindow_noHit_probability_cover_payload
    hX hpayload

theorem taoTheorem31_of_budgeted_eventually_large_oddWindow_noHit_cover_defect_half_payload
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (I : ℕ → ℕ → Finset ℕ) (lo hi : ℕ → ℕ → ℕ → ℕ)
    (η ρ δ : ℕ → ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hcover : ∀ᶠ B : ℕ in atTop,
      2 ≤ B → ∀ᶠ X in atTop,
        ∃ hmass : ∀ i, i ∈ I B X →
            0 < logFinsetMass (oddLogWindow (lo B X i) (hi B X i)),
          0 ≤ η B X ∧
          η B X ≤ 1 ∧
          0 ≤ δ B X ∧
          (∀ i ∈ I B X, hi B X i ≤ X) ∧
          (∀ i ∈ I B X, ∀ j ∈ I B X, i ≠ j →
            Disjoint (oddLogWindowSet (lo B X i) (hi B X i))
              (oddLogWindowSet (lo B X j) (hi B X j))) ∧
          (∀ i, ∀ hiI : i ∈ I B X,
            syracuseNoHitWindowProb B (lo B X i) (hi B X i) (hmass i hiI) ≤ η B X) ∧
          (1 / 2 : ℝ) - δ B X ≤ ρ B X ∧
          ρ B X * logMass X ≤
            ∑ i ∈ I B X, logCount (oddLogWindowSet (lo B X i) (hi B X i)) X ∧
          δ B X + η B X / 2 ≤ baseErr B + totalErr B) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  refine taoTheorem31_of_budgeted_eventually_large_oddWindow_noHit_probability_cover_payload
    stepErr totalErr baseErr I lo hi η ρ hbudget hbase ?_
  filter_upwards [hcover] with B hcoverB
  intro hB
  filter_upwards [hcoverB hB] with X hdata
  rcases hdata with ⟨hmass, hη0, hη1, hδ0, hhiX, hpairW, hprob, hrho,
    hcoverMass, hfinal⟩
  exact Section3OddWindowNoHitProbabilityCoverPayload.of_cover_defect_nohit_half
    hmass hη0 hη1 hδ0 hhiX hpairW hprob hrho hcoverMass hfinal

theorem taoTheorem31_of_budgeted_eventually_large_ordered_oddWindow_noHit_cover_defect_half_payload
    (stepErr : ℕ → ℕ → ℝ) (totalErr baseErr : ℕ → ℝ)
    (I : ℕ → ℕ → Finset ℕ) (lo hi : ℕ → ℕ → ℕ → ℕ)
    (η ρ δ : ℕ → ℕ → ℝ)
    (hbudget : Section3FiniteGeometricErrorBudget totalErr stepErr)
    (hbase : Tendsto baseErr atTop (nhds 0))
    (hcover : ∀ᶠ B : ℕ in atTop,
      2 ≤ B → ∀ᶠ X in atTop,
        ∃ hmass : ∀ i, i ∈ I B X →
            0 < logFinsetMass (oddLogWindow (lo B X i) (hi B X i)),
          0 ≤ η B X ∧
          η B X ≤ 1 ∧
          0 ≤ δ B X ∧
          (∀ i ∈ I B X, hi B X i ≤ X) ∧
          (∀ i ∈ I B X, ∀ j ∈ I B X, i < j → hi B X i < lo B X j) ∧
          (∀ i, ∀ hiI : i ∈ I B X,
            syracuseNoHitWindowProb B (lo B X i) (hi B X i) (hmass i hiI) ≤ η B X) ∧
          (1 / 2 : ℝ) - δ B X ≤ ρ B X ∧
          ρ B X * logMass X ≤
            ∑ i ∈ I B X, logCount (oddLogWindowSet (lo B X i) (hi B X i)) X ∧
          δ B X + η B X / 2 ≤ baseErr B + totalErr B) :
    TaoTheorem31SyracuseFiniteThresholdStatement := by
  refine taoTheorem31_of_budgeted_eventually_large_oddWindow_noHit_cover_defect_half_payload
    stepErr totalErr baseErr I lo hi η ρ δ hbudget hbase ?_
  filter_upwards [hcover] with B hcoverB
  intro hB
  filter_upwards [hcoverB hB] with X hdata
  rcases hdata with ⟨hmass, hη0, hη1, hδ0, hhiX, hgap, hprob, hrho,
    hcoverMass, hfinal⟩
  refine ⟨hmass, hη0, hη1, hδ0, hhiX, ?_, hprob, hrho, hcoverMass, hfinal⟩
  exact oddLogWindowSet_pairwise_disjoint_of_ordered_gaps (I B X) (lo B X) (hi B X) hgap

end Tao
end Erdos1135SecondScale
