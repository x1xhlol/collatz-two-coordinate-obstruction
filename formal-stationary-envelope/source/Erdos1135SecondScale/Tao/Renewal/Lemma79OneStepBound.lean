/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79R3AtomBound
import Erdos1135SecondScale.Tao.Renewal.Lemma79R3Prefix
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2PositiveKeyBound

/-!
# Lemma 7.9 Killed Native One-Step Bound

This proof leaf integrates the support-guarded atom restart estimate against
the exact stopped-prefix/fresh-tail tower.  The future hypothesis is uniform in
the restarted endpoint, and every key-dependent master is pulled back to the
fixed cutoff law before countable key aggregation.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- One canonical positive semantic key inherits the bound at `R` from a
uniform bound at every restarted endpoint for `R-1`. -/
theorem lemma79_canonical_someKey_step_of_cutoff_eq
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    {R : ℕ} (hR : 2 ≤ R)
    (hfuture : ∀ endpoint : TaoSection7RenewalPoint,
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF (n / 2))
          (lemma79HoldPathCutoffTailMomentENN endpoint
            (taoSection7CanonicalTriangleFamily hxi hscalar)
            n xi epsilon (n / 2) (R - 1)) ≤
        ENNReal.ofReal (Real.exp epsilon))
    (origin : TaoSection7RenewalPoint)
    {J : ℕ} (hJ : J = n / 2)
    (p : ℕ) (entryPoint : TaoSection7Point) :
    let family := taoSection7CanonicalTriangleFamily hxi hscalar
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF J)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey origin family J)
          (some (p, entryPoint))).indicator
            (lemma79HoldPathCutoffTailMomentENN
              origin family n xi epsilon J R)) ≤
      (taoSection7HoldListPMF J).toOuterMeasure
          (lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey origin family J)
            (some (p, entryPoint))) *
        ENNReal.ofReal (Real.exp epsilon) := by
  dsimp only
  let family := taoSection7CanonicalTriangleFamily hxi hscalar
  let shortAtom :=
    lemma79KeyAtom Set.univ
      (lemma79HoldPathHeadKey origin family J)
      (some (p, entryPoint))
  by_cases hmass :
      (taoSection7HoldListPMF J).toOuterMeasure shortAtom = 0
  · have hzero :=
      lemma79PMFENNExpectation_indicator_eq_zero_of_mass_eq_zero
        (taoSection7HoldListPMF J) shortAtom
        (lemma79HoldPathCutoffTailMomentENN
          origin family n xi epsilon J R) hmass
    change
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF J)
          (shortAtom.indicator
            (lemma79HoldPathCutoffTailMomentENN
              origin family n xi epsilon J R)) ≤
        (taoSection7HoldListPMF J).toOuterMeasure shortAtom *
          ENNReal.ofReal (Real.exp epsilon)
    rw [hzero, hmass]
    simp
  · rcases lemma79_exists_supported_firstEntry_unique_canonicalTriangle
      hxi hscalar J origin p entryPoint hmass with
      ⟨_short, _hshort, _hshortKey, hpJ, _hentryShort,
        Delta, hDelta, hDeltaMem, _hDeltaUnique⟩
    let entry := lemma79RenewalPointOfPoint entryPoint
    let gap := lemma79EntryVerticalGap Delta entryPoint
    let B := p + (gap + 1 + J)
    let longAtom :=
      lemma79KeyAtom Set.univ
        (lemma79HoldPathHeadKey origin family J)
        (some (p, entryPoint))
    let White : Set (ℕ × ℤ) :=
      {x | taoSection7SourceActualW n xi epsilon
        (lemma77RenewalPointOfRelativeEndpoint entry x)}
    let prefixWeight : List TaoSection7RenewalPoint -> ENNReal :=
      fun pre =>
        lemma79R2EndpointWeight White
          (lemma77EndpointOfPrefix entry pre)
    let future : TaoSection7RenewalPoint ->
        List TaoSection7RenewalPoint -> ENNReal :=
      fun endpoint tail =>
        lemma79HoldPathCutoffTailMomentENN endpoint family
          n xi epsilon J (R - 1) tail
    let towerIntegrand : List TaoSection7RenewalPoint -> ENNReal :=
      fun full =>
        let pair := lemma79VerticalFirstPassageFixedTailSplit
          J entry gap ((full.drop p).take (gap + 1 + J))
        prefixWeight pair.1 *
          future
            (taoSection7RenewalPathPoint entry pair.1 pair.1.length)
            pair.2
    let prefactor : ENNReal :=
      ENNReal.ofReal (Real.exp (-(p.pred : ℝ) + epsilon))
    have hJB : J ≤ B := by omega
    have hroom : p + (gap + 1 + J) ≤ B := by omega
    have hpair : TaoSection7TriangleFamilyPairwiseDisjoint family := by
      simpa [family] using
        taoSection7CanonicalTriangleFamily_pairwiseDisjoint hxi hscalar
    have hgap : lemma79EntryVerticalGap Delta entry.toPoint = gap := by
      simp [entry, gap]
    have hvalue : ∀ full : List TaoSection7RenewalPoint,
        taoSection7HoldListPMF B full ≠ 0 ->
        longAtom.indicator
            (lemma79HoldPathCutoffTailMomentENN
              origin family n xi epsilon J R) full ≤
          longAtom.indicator towerIntegrand full * prefactor := by
      intro full hfull
      by_cases hatom : full ∈ longAtom
      · have hkey :
          lemma79HoldPathHeadKey origin family J full =
            some (p, entry.toPoint) := by
          simpa [longAtom, entry] using hatom.2
        have hpoint :=
          lemma79HoldPathCutoffTailMomentENN_le_firstPassagePair
            (B := B) (R := R) hxi hscalar hJ hR hfull
            (by simpa [family] using hkey) hDelta
            (by simpa [entry] using hDeltaMem) hgap hroom
        rw [Set.indicator_of_mem hatom, Set.indicator_of_mem hatom]
        simpa [family, towerIntegrand, prefixWeight, future,
          prefactor, White, entry, gap] using hpoint.trans_eq (by ac_rfl)
      · simp [Set.indicator, hatom]
    have hsummand : ∀ full : List TaoSection7RenewalPoint,
        taoSection7HoldListPMF B full *
            longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J R) full ≤
          taoSection7HoldListPMF B full *
            (longAtom.indicator towerIntegrand full * prefactor) := by
      intro full
      by_cases hfull : taoSection7HoldListPMF B full = 0
      · simp [hfull]
      · exact mul_le_mul_right (hvalue full hfull) _
    have htoTower :
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J R)) ≤
          lemma79PMFENNExpectation
              (taoSection7HoldListPMF B)
              (longAtom.indicator towerIntegrand) * prefactor := by
      calc
        _ ≤ lemma79PMFENNExpectation
              (taoSection7HoldListPMF B)
              (fun full => longAtom.indicator towerIntegrand full * prefactor) := by
          unfold lemma79PMFENNExpectation
          exact ENNReal.tsum_le_tsum hsummand
        _ = lemma79PMFENNExpectation
              (taoSection7HoldListPMF B)
              (longAtom.indicator towerIntegrand) * prefactor :=
          lemma79PMFENNExpectation_mul_const
            (taoSection7HoldListPMF B)
            (longAtom.indicator towerIntegrand) prefactor
    have hfutureJ : ∀ endpoint,
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF J) (future endpoint) ≤
          ENNReal.ofReal (Real.exp epsilon) := by
      intro endpoint
      simpa [future, family, hJ] using hfuture endpoint
    have htower :
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator towerIntegrand) ≤
          (taoSection7HoldListPMF B).toOuterMeasure longAtom *
            (ENNReal.ofReal (Real.exp epsilon) *
              lemma79PMFENNExpectation
                (lemma79RawHoldFirstPassagePrefixPMF J entry gap)
                prefixWeight) := by
      simpa [family, longAtom, towerIntegrand] using
        (lemma79_holdList_firstEntryKey_firstPassageFixedTailWeightedExpectation_le
          (origin := origin) (entry := entry) (family := family)
          (C := J) (B := B) (p := p) (gap := gap) (J := J)
          hpJ hroom prefixWeight future
          (ENNReal.ofReal (Real.exp epsilon)) hfutureJ)
    have hprefix :
        lemma79PMFENNExpectation
            (lemma79RawHoldFirstPassagePrefixPMF J entry gap)
            prefixWeight ≤
          ENNReal.ofReal lemma79R2ContractionFactor := by
      simpa [prefixWeight, White] using
        (lemma79_rawHoldFirstPassagePrefix_r2EndpointWeight_le_contraction
          hxi hscalar hDelta (entry := entry) (gap := gap) (L := L)
          (J := J) (by simpa [entry] using hDeltaMem) hgap
          (hlocalizedMass entry gap) hcollar)
    have hscalarReal :
        (Real.exp (-(p.pred : ℝ) + epsilon) * Real.exp epsilon) *
            lemma79R2ContractionFactor ≤
          Real.exp epsilon := by
      calc
        (Real.exp (-(p.pred : ℝ) + epsilon) * Real.exp epsilon) *
              lemma79R2ContractionFactor =
            Real.exp (-(p.pred : ℝ) + 2 * epsilon) *
              lemma79R2ContractionFactor := by
          rw [← Real.exp_add]
          congr 2
          ring
        _ ≤ Real.exp (-(p.pred : ℝ) + epsilon) :=
          lemma79_exp_add_two_epsilon_mul_r2Contraction_le hscalar
        _ ≤ Real.exp epsilon := Real.exp_le_exp.mpr (by
          have hpred : 0 ≤ (p.pred : ℝ) := Nat.cast_nonneg _
          linarith)
    have hscalarENN :
        (prefactor * ENNReal.ofReal (Real.exp epsilon)) *
            ENNReal.ofReal lemma79R2ContractionFactor ≤
          ENNReal.ofReal (Real.exp epsilon) := by
      dsimp [prefactor]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [← ENNReal.ofReal_mul
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hscalarReal
    have hlong :
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J R)) ≤
          (taoSection7HoldListPMF B).toOuterMeasure longAtom *
            ENNReal.ofReal (Real.exp epsilon) := by
      calc
        _ ≤ lemma79PMFENNExpectation
              (taoSection7HoldListPMF B)
              (longAtom.indicator towerIntegrand) * prefactor := htoTower
        _ ≤ ((taoSection7HoldListPMF B).toOuterMeasure longAtom *
              (ENNReal.ofReal (Real.exp epsilon) *
                lemma79PMFENNExpectation
                  (lemma79RawHoldFirstPassagePrefixPMF J entry gap)
                  prefixWeight)) * prefactor :=
          mul_le_mul_left htower prefactor
        _ ≤ ((taoSection7HoldListPMF B).toOuterMeasure longAtom *
              (ENNReal.ofReal (Real.exp epsilon) *
                ENNReal.ofReal lemma79R2ContractionFactor)) * prefactor :=
          mul_le_mul_left
            (mul_le_mul_right
              (mul_le_mul_right hprefix
                (ENNReal.ofReal (Real.exp epsilon)))
              ((taoSection7HoldListPMF B).toOuterMeasure longAtom))
            prefactor
        _ = (taoSection7HoldListPMF B).toOuterMeasure longAtom *
              ((prefactor * ENNReal.ofReal (Real.exp epsilon)) *
                ENNReal.ofReal lemma79R2ContractionFactor) := by
          ac_rfl
        _ ≤ (taoSection7HoldListPMF B).toOuterMeasure longAtom *
              ENNReal.ofReal (Real.exp epsilon) :=
          mul_le_mul_right hscalarENN _
    have hExpPull :=
      lemma79_holdList_keyAtom_cutoffTailMomentENN_expectation_eq_of_le
        hJB origin family hpair (some (p, entryPoint))
        (n := n) (R := R) (xi := xi) (epsilon := epsilon)
    have hMassPull :=
      lemma79_holdList_keyAtom_mass_eq_of_le
        hJB origin family (some (p, entryPoint))
    calc
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF J)
          (shortAtom.indicator
            (lemma79HoldPathCutoffTailMomentENN
              origin family n xi epsilon J R)) =
          lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J R)) := by
        simpa [shortAtom, longAtom] using hExpPull.symm
      _ ≤ (taoSection7HoldListPMF B).toOuterMeasure longAtom *
          ENNReal.ofReal (Real.exp epsilon) := hlong
      _ = (taoSection7HoldListPMF J).toOuterMeasure shortAtom *
          ENNReal.ofReal (Real.exp epsilon) := by
        rw [hMassPull]

/-- The canonical killed bound advances from `R-1` to `R`, uniformly in the
initial renewal point. -/
theorem lemma79_canonical_step
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    {R : ℕ} (hR : 2 ≤ R)
    (hfuture : ∀ endpoint : TaoSection7RenewalPoint,
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF (n / 2))
          (lemma79HoldPathCutoffTailMomentENN endpoint
            (taoSection7CanonicalTriangleFamily hxi hscalar)
            n xi epsilon (n / 2) (R - 1)) ≤
        ENNReal.ofReal (Real.exp epsilon))
    (origin : TaoSection7RenewalPoint) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF (n / 2))
        (lemma79HoldPathCutoffTailMomentENN origin
          (taoSection7CanonicalTriangleFamily hxi hscalar)
          n xi epsilon (n / 2) R) ≤
      ENNReal.ofReal (Real.exp epsilon) := by
  apply lemma79_holdList_cutoffTailMomentENN_le_of_someKey_bounds
    (n / 2) origin (taoSection7CanonicalTriangleFamily hxi hscalar)
    n xi epsilon R (by omega) (ENNReal.ofReal (Real.exp epsilon))
  rintro ⟨p, entryPoint⟩
  exact lemma79_canonical_someKey_step_of_cutoff_eq
    L hlocalizedMass hxi hscalar hcollar hR hfuture origin rfl p entryPoint

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
