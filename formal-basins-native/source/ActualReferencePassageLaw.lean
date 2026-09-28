import RealCanonicalClockRates
import DefaultPassComposition
import FinitePMFLadder

open Filter
open scoped Topology

namespace CollatzClockAudit
open Erdos1135.Tao

noncomputable def realClockPassageLaw (x : ℝ) (hx : 1 ≤ x)
    (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))) :
    PMF {m : ℕ // m ≤ Nat.floor x} :=
  syracusePassLocationRealFloorLaw (realClockSourceLo x branch)
    (realClockSourceHi x branch) x hx hmass

theorem real_odd_source_map_passage_eq (x : ℝ) (hx : 1 ≤ x)
    (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))) :
    (oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch) hmass).map
      (fun q => syracusePassLocationRealFloorOrOne x q.1 hx) =
        realClockPassageLaw x hx branch hmass := by
  rw [oddLogWindowOddNatPMF, PMF.map_comp]
  rfl

theorem real_canonical_window_pair (x : ℝ) :
    TaoProp111RealWindowPair x
      (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)
      (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- All probabilistic inputs at one real scale are produced from the checked
local clock/landing theorems and checked Proposition 1.11. -/
structure RealClockScaleFacts (C c x : ℝ) : Prop where
  one_le_x : 1 ≤ x
  mass_pos : ∀ branch : TaoSection5SourceBranch, 0 < logFinsetMass
    (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))
  clock_bound : ∀ (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))),
    ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
      hmass).toOuterMeasure (realLocalClockGoodEvent x)ᶜ).toReal ≤
        200000 * (Real.log x) ^ (-(1 / 10 : ℝ))
  landing_bound : ∀ (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))),
    ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
      hmass).toOuterMeasure (realLargeLandingGoodEvent x)ᶜ).toReal ≤
        200000 * x ^ (-(1 / 12800000 : ℝ))
  tv_bound : ∀ (h₁ : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)))
    (h₂ : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq))),
    taoTV (realClockPassageLaw x one_le_x .alpha h₁)
      (realClockPassageLaw x one_le_x .alphaSq h₂) ≤ C * (Real.log x) ^ (-c)

theorem exists_eventually_real_clock_scale_facts :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ x : ℝ in atTop, RealClockScaleFacts C c x := by
  obtain ⟨errNoHit, errTV, C, c, hC, hc, hrates, hbound⟩ :=
    taoProp111RealFirstPassageStabilizationRate_checked
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [hrates, eventually_real_local_clock_and_landing_rates,
    eventually_ge_atTop (1 : ℝ)] with x hrates hlocal hx
  refine ⟨hx, hlocal.1, fun b hm => (hlocal.2 b hm).1,
    fun b hm => (hlocal.2 b hm).2, ?_⟩
  intro h₁ h₂
  have ht := (hbound x (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)
    (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq)
    hx (real_canonical_window_pair x) h₁ h₂).2.2
  exact ht.trans hrates.2.2.2

theorem adjacent_real_sourceY {x : ℝ} (hx : 0 ≤ x) :
    realClockSourceY (x ^ taoAlpha) .alpha = realClockSourceY x .alphaSq := by
  change (x ^ taoAlpha) ^ taoAlpha = x ^ (taoAlpha ^ 2)
  rw [← Real.rpow_mul hx, pow_two]

theorem adjacent_real_sourceLo {x : ℝ} (hx : 0 ≤ x) :
    realClockSourceLo (x ^ taoAlpha) .alpha = realClockSourceLo x .alphaSq :=
  congrArg taoNyLo (adjacent_real_sourceY hx)

theorem adjacent_real_sourceHi {x : ℝ} (hx : 0 ≤ x) :
    realClockSourceHi (x ^ taoAlpha) .alpha = realClockSourceHi x .alphaSq :=
  congrArg (fun y => taoNyHi y taoAlpha) (adjacent_real_sourceY hx)

/-- One lower passage of the reference landing law is compared with the
next reference law by the actual checked adjacent-window stabilization. -/
theorem adjacent_reference_passage_tv {C c x : ℝ} (facts : RealClockScaleFacts C c x)
    (hmassNext : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo (x ^ taoAlpha) .alpha)
        (realClockSourceHi (x ^ taoAlpha) .alpha)))
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x .alpha) (realClockSourceHi x .alpha))) :
    taoTV
      ((realClockPassageLaw (x ^ taoAlpha)
        (Real.one_le_rpow facts.one_le_x taoAlpha_pos.le) .alpha hmassNext).map
        (fun u => syracusePassLocationRealFloorOrOne x u.1 facts.one_le_x))
      (realClockPassageLaw x facts.one_le_x .alpha hmass) ≤ C * (Real.log x) ^ (-c) := by
  have hx : 0 ≤ x := zero_le_one.trans facts.one_le_x
  have hxy : x ≤ x ^ taoAlpha := Real.self_le_rpow_of_one_le facts.one_le_x taoAlpha_one_lt.le
  have hmass₂ : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq)) := by
    simpa only [adjacent_real_sourceLo hx, adjacent_real_sourceHi hx] using hmassNext
  rw [taoTV_comm]
  unfold realClockPassageLaw
  rw [realFloorPassLocationLaw_map_lower hmassNext facts.one_le_x hxy]
  simpa only [realClockPassageLaw, adjacent_real_sourceLo hx, adjacent_real_sourceHi hx] using
    facts.tv_bound hmass hmass₂

end CollatzClockAudit

#print axioms CollatzClockAudit.real_odd_source_map_passage_eq
#print axioms CollatzClockAudit.exists_eventually_real_clock_scale_facts
#print axioms CollatzClockAudit.adjacent_real_sourceY
#print axioms CollatzClockAudit.adjacent_reference_passage_tv
