/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case2Discount
import Erdos1135Predecessor.Tao.Renewal.QStoppedApprox

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoSection7PMFExpectation_mono_of_support
    {Ω : Type*} (μ : PMF Ω) {F G : Ω → ℝ}
    (hFsum : Summable fun ω => (μ ω).toReal * F ω)
    (hGsum : Summable fun ω => (μ ω).toReal * G ω)
    (hFG : ∀ ω, μ ω ≠ 0 → F ω ≤ G ω) :
    taoSection7PMFExpectation μ F ≤ taoSection7PMFExpectation μ G := by
  have hpoint : ∀ ω, (μ ω).toReal * F ω ≤ (μ ω).toReal * G ω := by
    intro ω
    by_cases hμ : μ ω = 0
    · simp [hμ]
    · exact mul_le_mul_of_nonneg_left (hFG ω hμ) ENNReal.toReal_nonneg
  unfold taoSection7PMFExpectation
  exact hFsum.tsum_le_tsum hpoint hGsum

theorem taoSection7PMFExpectation_summable_and_le_of_support
    {Ω : Type*} (μ : PMF Ω) {F G : Ω → ℝ}
    (hF0 : ∀ ω, μ ω ≠ 0 → 0 ≤ F ω)
    (hFG : ∀ ω, μ ω ≠ 0 → F ω ≤ G ω)
    (hGsum : Summable fun ω => (μ ω).toReal * G ω) :
    Summable (fun ω => (μ ω).toReal * F ω) ∧
      taoSection7PMFExpectation μ F ≤ taoSection7PMFExpectation μ G := by
  have hnonneg : ∀ ω, 0 ≤ (μ ω).toReal * F ω := by
    intro ω
    by_cases hμ : μ ω = 0
    · simp [hμ]
    · exact mul_nonneg ENNReal.toReal_nonneg (hF0 ω hμ)
  have hpoint : ∀ ω, (μ ω).toReal * F ω ≤ (μ ω).toReal * G ω := by
    intro ω
    by_cases hμ : μ ω = 0
    · simp [hμ]
    · exact mul_le_mul_of_nonneg_left (hFG ω hμ) ENNReal.toReal_nonneg
  have hFsum : Summable fun ω => (μ ω).toReal * F ω :=
    Summable.of_nonneg_of_le hnonneg hpoint hGsum
  exact ⟨hFsum,
    taoSection7PMFExpectation_mono_of_support μ hFsum hGsum hFG⟩

theorem taoSection7PMFEventMass_ne_top
    {Ω : Type*} (μ : PMF Ω) (E : Set Ω) :
    μ.toOuterMeasure E ≠ ⊤ := by
  have huniv : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  calc
    μ.toOuterMeasure E ≤ μ.toOuterMeasure Set.univ :=
      μ.toOuterMeasure.mono (Set.subset_univ E)
    _ = 1 := huniv

theorem taoSection7PMFEventMass_le_add_of_support_cover
    {Ω : Type*} (μ : PMF Ω) {Middle E F : Set Ω}
    (hcover :
      ∀ ω, μ ω ≠ 0 → ω ∈ Middle → ω ∈ E ∪ F) :
    μ.toOuterMeasure Middle ≤
      μ.toOuterMeasure E + μ.toOuterMeasure F := by
  calc
    μ.toOuterMeasure Middle ≤ μ.toOuterMeasure (E ∪ F) := by
      apply μ.toOuterMeasure_mono
      intro ω hω
      exact hcover ω ((μ.mem_support_iff ω).1 hω.2) hω.1
    _ ≤ μ.toOuterMeasure E + μ.toOuterMeasure F :=
      MeasureTheory.measure_union_le E F

theorem taoSection7PMFEventMass_mono
    {Ω : Type*} (μ : PMF Ω) {E E' : Set Ω} (hEE' : E ⊆ E') :
    (μ.toOuterMeasure E).toReal ≤ (μ.toOuterMeasure E').toReal :=
  ENNReal.toReal_mono (taoSection7PMFEventMass_ne_top μ E')
    (μ.toOuterMeasure.mono hEE')

theorem taoSection7PMFEventMass_le_one
    {Ω : Type*} (μ : PMF Ω) (E : Set Ω) :
    (μ.toOuterMeasure E).toReal ≤ 1 := by
  have hmono := taoSection7PMFEventMass_mono μ (Set.subset_univ E)
  have huniv : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  simpa [huniv] using hmono

theorem taoSection7PMFExpectation_summable_and_le_threeRegion
    {Ω : Type*} (μ : PMF Ω) (Bad Low : Set Ω) (F : Ω → ℝ)
    {badCap lowCap goodCap : ℝ}
    (_hbadCap0 : 0 ≤ badCap) (_hlowCap0 : 0 ≤ lowCap)
    (_hgoodCap0 : 0 ≤ goodCap)
    (hF0 : ∀ ω, μ ω ≠ 0 → 0 ≤ F ω)
    (hbad : ∀ ω, μ ω ≠ 0 → ω ∈ Bad → F ω ≤ badCap)
    (hlow : ∀ ω, μ ω ≠ 0 → ω ∉ Bad → ω ∈ Low → F ω ≤ lowCap)
    (hgood : ∀ ω, μ ω ≠ 0 → ω ∉ Bad → ω ∉ Low → F ω ≤ goodCap) :
    Summable (fun ω => (μ ω).toReal * F ω) ∧
      taoSection7PMFExpectation μ F ≤
        badCap * (μ.toOuterMeasure Bad).toReal +
          lowCap * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
            goodCap * (μ.toOuterMeasure ((Bad ∪ Low)ᶜ)).toReal := by
  classical
  let mass : Ω → ℝ := fun ω => (μ ω).toReal
  let badMass : Ω → ℝ := Bad.indicator mass
  let lowMass : Ω → ℝ := (Badᶜ ∩ Low).indicator mass
  let goodMass : Ω → ℝ := ((Bad ∪ Low)ᶜ).indicator mass
  let cap : Ω → ℝ := fun ω =>
    badCap * Bad.indicator (fun _ => (1 : ℝ)) ω +
      lowCap * (Badᶜ ∩ Low).indicator (fun _ => (1 : ℝ)) ω +
        goodCap * ((Bad ∪ Low)ᶜ).indicator (fun _ => (1 : ℝ)) ω
  let major : Ω → ℝ := fun ω =>
    badCap * badMass ω + lowCap * lowMass ω + goodCap * goodMass ω
  have hmassSum : Summable mass := by
    simpa [mass] using ENNReal.summable_toReal μ.tsum_coe_ne_top
  have hbadMassSum : Summable badMass := by
    simpa [badMass] using hmassSum.indicator Bad
  have hlowMassSum : Summable lowMass := by
    simpa [lowMass] using hmassSum.indicator (Badᶜ ∩ Low)
  have hgoodMassSum : Summable goodMass := by
    simpa [goodMass] using hmassSum.indicator ((Bad ∪ Low)ᶜ)
  have hbadTermSum : Summable fun ω => badCap * badMass ω :=
    hbadMassSum.mul_left badCap
  have hlowTermSum : Summable fun ω => lowCap * lowMass ω :=
    hlowMassSum.mul_left lowCap
  have hgoodTermSum : Summable fun ω => goodCap * goodMass ω :=
    hgoodMassSum.mul_left goodCap
  have hmajorSum : Summable major := by
    dsimp [major]
    exact (hbadTermSum.add hlowTermSum).add hgoodTermSum
  have hweightedCap : ∀ ω, mass ω * cap ω = major ω := by
    intro ω
    by_cases hBad : ω ∈ Bad <;> by_cases hLow : ω ∈ Low <;>
      simp [mass, badMass, lowMass, goodMass, cap, major, hBad, hLow] <;> ring
  have hcapSum : Summable fun ω => (μ ω).toReal * cap ω := by
    refine hmajorSum.congr ?_
    intro ω
    simpa [mass] using (hweightedCap ω).symm
  have hFcap : ∀ ω, μ ω ≠ 0 → F ω ≤ cap ω := by
    intro ω hμ
    by_cases hBad : ω ∈ Bad
    · simpa [cap, hBad] using hbad ω hμ hBad
    · by_cases hLow : ω ∈ Low
      · simpa [cap, hBad, hLow] using hlow ω hμ hBad hLow
      · simpa [cap, hBad, hLow] using hgood ω hμ hBad hLow
  have hmono := taoSection7PMFExpectation_summable_and_le_of_support
    μ hF0 hFcap hcapSum
  have hcapExpectation :
      taoSection7PMFExpectation μ cap =
        badCap * (μ.toOuterMeasure Bad).toReal +
          lowCap * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
            goodCap * (μ.toOuterMeasure ((Bad ∪ Low)ᶜ)).toReal := by
    unfold taoSection7PMFExpectation
    change (∑' ω, mass ω * cap ω) = _
    calc
      (∑' ω, mass ω * cap ω) = ∑' ω, major ω :=
        tsum_congr hweightedCap
      _ = (∑' ω, badCap * badMass ω) +
          (∑' ω, lowCap * lowMass ω) +
            ∑' ω, goodCap * goodMass ω := by
        dsimp [major]
        rw [(hbadTermSum.add hlowTermSum).tsum_add hgoodTermSum,
          hbadTermSum.tsum_add hlowTermSum]
      _ = badCap * (∑' ω, badMass ω) +
          lowCap * (∑' ω, lowMass ω) +
            goodCap * (∑' ω, goodMass ω) := by
        rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
      _ = badCap * (μ.toOuterMeasure Bad).toReal +
          lowCap * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
            goodCap * (μ.toOuterMeasure ((Bad ∪ Low)ᶜ)).toReal := by
        simp only [badMass, lowMass, goodMass, mass]
        rw [← pmf_eventMass_toReal_eq_tsum_indicator,
          ← pmf_eventMass_toReal_eq_tsum_indicator,
          ← pmf_eventMass_toReal_eq_tsum_indicator]
  exact ⟨hmono.1, hmono.2.trans_eq hcapExpectation⟩

theorem taoSection7PMFExpectation_zeroSafe_closeout
    {Ω : Type*} (μ : PMF Ω) {payload weight : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hpayload0 : ∀ ω, μ ω ≠ 0 → 0 ≤ payload ω)
    (hsumWeight : Summable fun ω => (μ ω).toReal * weight ω)
    (hdom : ∀ ω, μ ω ≠ 0 → payload ω ≤ c * weight ω)
    (hweight_le_one : taoSection7PMFExpectation μ weight ≤ 1) :
    Summable (fun ω => (μ ω).toReal * payload ω) ∧
      taoSection7PMFExpectation μ payload ≤ c := by
  have hscaledSum :
      Summable fun ω => (μ ω).toReal * (c * weight ω) := by
    refine (hsumWeight.mul_left c).congr ?_
    intro ω
    ring
  have hmono := taoSection7PMFExpectation_summable_and_le_of_support
    μ hpayload0 hdom hscaledSum
  have hscale :
      taoSection7PMFExpectation μ (fun ω => c * weight ω) =
        c * taoSection7PMFExpectation μ weight := by
    unfold taoSection7PMFExpectation
    calc
      (∑' ω, (μ ω).toReal * (c * weight ω)) =
          ∑' ω, c * ((μ ω).toReal * weight ω) := by
        apply tsum_congr
        intro ω
        ring
      _ = c * ∑' ω, (μ ω).toReal * weight ω := by rw [tsum_mul_left]
  refine ⟨hmono.1, hmono.2.trans ?_⟩
  calc
    taoSection7PMFExpectation μ (fun ω => c * weight ω) =
        c * taoSection7PMFExpectation μ weight := hscale
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hweight_le_one hc
    _ = c := mul_one c

end

end Tao

end Erdos1135Predecessor
