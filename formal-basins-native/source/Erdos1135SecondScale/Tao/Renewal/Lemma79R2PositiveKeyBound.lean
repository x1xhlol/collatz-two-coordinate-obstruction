/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79R2PositiveKey
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2MasterTransport
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2EndpointExpectation

/-!
# Lemma 7.9 Killed R=2 Positive-Key Bound

This proof leaf composes the positive-key source witness, a key-dependent iid
Hold master, the pointwise first-exit recurrence, and the native canonical
endpoint contraction.  Both the weighted expectation and key mass are pulled
back to the original cutoff law before countable aggregation.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A zero-mass PMF event contributes zero to every native nonnegative
indicator-weighted expectation. -/
theorem lemma79PMFENNExpectation_indicator_eq_zero_of_mass_eq_zero
    {Omega : Type*} (mu : PMF Omega) (Event : Set Omega)
    (F : Omega -> ENNReal)
    (hmass : mu.toOuterMeasure Event = 0) :
    lemma79PMFENNExpectation mu (Event.indicator F) = 0 := by
  have hdisjoint : Disjoint mu.support Event :=
    (PMF.toOuterMeasure_apply_eq_zero_iff mu Event).1 hmass
  unfold lemma79PMFENNExpectation
  rw [ENNReal.tsum_eq_zero]
  intro omega
  by_cases hEvent : omega ∈ Event
  · have hmu : mu omega = 0 := by
      by_contra hne
      exact (Set.disjoint_left.1 hdisjoint) hne hEvent
    simp [hmu]
  · simp [Set.indicator, hEvent]

/-- One canonical positive semantic key satisfies the killed `R=2` bound
under the original iid Hold law. -/
theorem lemma79_canonical_someKey_R2_of_cutoff_eq
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
              origin family n xi epsilon J 2)) ≤
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
          origin family n xi epsilon J 2) hmass
    change
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF J)
          (shortAtom.indicator
            (lemma79HoldPathCutoffTailMomentENN
              origin family n xi epsilon J 2)) ≤
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
    let B := p + (gap + 1) + J
    let longAtom :=
      lemma79KeyAtom Set.univ
        (lemma79HoldPathHeadKey origin family J)
        (some (p, entryPoint))
    let White : Set (ℕ × ℤ) :=
      {x | taoSection7SourceActualW n xi epsilon
        (lemma77RenewalPointOfRelativeEndpoint entry x)}
    let endpointWeight : List TaoSection7RenewalPoint -> ENNReal :=
      fun full =>
        lemma79R2EndpointWeight White
          (lemma77CanonicalStoppedEndpoint entry gap
            ((full.drop p).take (gap + 1)))
    let prefactor : ENNReal :=
      ENNReal.ofReal (Real.exp (-(p.pred : ℝ) + 2 * epsilon))
    have hJB : J ≤ B := by omega
    have hroom : p + (gap + 1) ≤ B := by omega
    have hpair : TaoSection7TriangleFamilyPairwiseDisjoint family := by
      simpa [family] using
        taoSection7CanonicalTriangleFamily_pairwiseDisjoint hxi hscalar
    have hcover :
        TaoSection7TriangleFamilyCoverBlack
          (taoSection7SourceBlackInDomain n xi epsilon J) family := by
      simpa [family, hJ] using
        taoSection7CanonicalTriangleFamily_cover hxi hscalar
    have hvalue : ∀ full : List TaoSection7RenewalPoint,
        taoSection7HoldListPMF B full ≠ 0 ->
        longAtom.indicator
            (lemma79HoldPathCutoffTailMomentENN
              origin family n xi epsilon J 2) full ≤
          longAtom.indicator endpointWeight full * prefactor := by
      intro full hfull
      by_cases hatom : full ∈ longAtom
      · have hkey :
          lemma79HoldPathHeadKey origin family J full =
            some (p, entryPoint) := hatom.2
        have hkeyEntry :
            lemma79BoundedInclusiveTraceHeadKey
                (lemma79HoldPathPointAt origin full) family J =
              some (p, entry.toPoint) := by
          simpa [family, entry, lemma79HoldPathHeadKey] using hkey
        rcases lemma79_exists_canonicalTrace_cons_of_headKey
            hxi hscalar hkey hDelta hDeltaMem with
          ⟨rest, htrace⟩
        have hlenB : full.length = B := by
          by_contra hne
          exact hfull
            (taoSection7HoldListPMF_apply_eq_zero_of_length_ne B full hne)
        have hlenJ : J ≤ full.length := by rw [hlenB]; exact hJB
        let block := (full.drop p).take (gap + 1)
        let K := lemma79VerticalFirstPassageCut entry gap block
        have hroomMaster :
            p + lemma79EntryVerticalGap Delta entry.toPoint + 1 ≤ B := by
          change p + lemma79EntryVerticalGap Delta entryPoint + 1 ≤ B
          dsimp [B, gap]
          omega
        have hdata :
            K = lemma79HoldFirstExitCut origin full p gap ∧
              Lemma79FirstExitCertificate
                (lemma79HoldPathPointAt origin full) Delta p (p + K) ∧
              lemma77RenewalPointOfRelativeEndpoint entry
                  (lemma77CanonicalStoppedEndpoint entry gap block) =
                taoSection7RenewalPathPoint origin full (p + K) ∧
              K ≤ gap + 1 := by
          simpa [entry, gap, B, block, K] using
            (lemma79CanonicalFirstExitData_of_holdListPMF_ne_zero
              (family := family) (C := J) Delta hfull hkeyEntry
              (by simpa [entry] using hDeltaMem)
              hroomMaster)
        rcases hdata with ⟨_hcut, hexit, hendpoint, _hKle⟩
        rw [Set.indicator_of_mem hatom, Set.indicator_of_mem hatom]
        by_cases hdead : J ≤ p + K
        · have hzero :
              lemma79CutoffTailMoment
                  (lemma79HoldPathPointAt origin full)
                  family n xi epsilon J 2 = 0 :=
            lemma79CutoffTailMoment_two_eq_zero_of_cutoff_le_firstExit
              (n := n) (C := J) (p := p) (k1 := p + K)
              (xi := xi) (epsilon := epsilon) (family := family)
              (old := Delta) (rest := rest)
              hpair (by simpa [family] using htrace) hexit hdead
          simp [lemma79HoldPathCutoffTailMomentENN, hzero]
        · have hreal :=
            lemma79HoldPathCutoffTailMoment_two_le_firstExitWeight
              hpair hcover hlenJ hexit htrace
          have hrestart :
              lemma79HoldPathRestartPointAt origin full p K =
                (lemma77RenewalPointOfRelativeEndpoint entry
                  (lemma77CanonicalStoppedEndpoint entry gap block)).toPoint := by
            rw [lemma79HoldPathRestartPointAt_eq]
            unfold lemma79HoldPathPointAt
            exact congrArg TaoSection7RenewalPoint.toPoint hendpoint.symm
          have hwhiteIff :
              lemma77CanonicalStoppedEndpoint entry gap block ∈ White ↔
                taoSection7SourceWhiteWCutoff n xi epsilon J
                  ((lemma79HoldPathRestartPointAt origin full p K).j : ℕ)
                  (lemma79HoldPathRestartPointAt origin full p K).l := by
            rw [hrestart]
            simp [White, taoSection7SourceActualW,
              taoSection7SourceWhiteRenewal, hJ]
          by_cases hwhite :
              lemma77CanonicalStoppedEndpoint entry gap block ∈ White
          · have hwhiteGlobal := hwhiteIff.mp hwhite
            have hreal' :
                lemma79CutoffTailMoment
                    (lemma79HoldPathPointAt origin full)
                    family n xi epsilon J 2 ≤
                  Real.exp (-(p.pred : ℝ) + 2 * epsilon) *
                    Real.exp (-1) := by
              rw [if_pos hwhiteGlobal] at hreal
              exact hreal
            unfold lemma79HoldPathCutoffTailMomentENN
            calc
              ENNReal.ofReal
                  (lemma79CutoffTailMoment
                    (lemma79HoldPathPointAt origin full)
                    family n xi epsilon J 2) ≤
                  ENNReal.ofReal
                    (Real.exp (-(p.pred : ℝ) + 2 * epsilon) *
                      Real.exp (-1)) :=
                ENNReal.ofReal_le_ofReal hreal'
              _ = ENNReal.ofReal
                    (Real.exp (-(p.pred : ℝ) + 2 * epsilon)) *
                  ENNReal.ofReal (Real.exp (-1)) := by
                rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
              _ = endpointWeight full * prefactor := by
                simp [endpointWeight, lemma79R2EndpointWeight,
                  hwhite, prefactor, block]
                ac_rfl
          · have hwhiteGlobal :
                ¬ taoSection7SourceWhiteWCutoff n xi epsilon J
                  ((lemma79HoldPathRestartPointAt origin full p K).j : ℕ)
                  (lemma79HoldPathRestartPointAt origin full p K).l :=
              fun h => hwhite (hwhiteIff.mpr h)
            have hreal' :
                lemma79CutoffTailMoment
                    (lemma79HoldPathPointAt origin full)
                    family n xi epsilon J 2 ≤
                  Real.exp (-(p.pred : ℝ) + 2 * epsilon) := by
              rw [if_neg hwhiteGlobal, mul_one] at hreal
              exact hreal
            unfold lemma79HoldPathCutoffTailMomentENN
            calc
              ENNReal.ofReal
                  (lemma79CutoffTailMoment
                    (lemma79HoldPathPointAt origin full)
                    family n xi epsilon J 2) ≤
                  ENNReal.ofReal
                    (Real.exp (-(p.pred : ℝ) + 2 * epsilon)) :=
                ENNReal.ofReal_le_ofReal hreal'
              _ = endpointWeight full * prefactor := by
                simp [endpointWeight, lemma79R2EndpointWeight,
                  hwhite, prefactor, block]
      · simp [Set.indicator, hatom]
    have hsummand : ∀ full : List TaoSection7RenewalPoint,
        taoSection7HoldListPMF B full *
            longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J 2) full ≤
          taoSection7HoldListPMF B full *
            (longAtom.indicator endpointWeight full * prefactor) := by
      intro full
      by_cases hfull : taoSection7HoldListPMF B full = 0
      · simp [hfull]
      · exact mul_le_mul_left' (hvalue full hfull) _
    have htoWeight :
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J 2)) ≤
          lemma79PMFENNExpectation
              (taoSection7HoldListPMF B)
              (longAtom.indicator endpointWeight) * prefactor := by
      calc
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J 2)) ≤
            lemma79PMFENNExpectation
              (taoSection7HoldListPMF B)
              (fun full => longAtom.indicator endpointWeight full * prefactor) := by
          unfold lemma79PMFENNExpectation
          exact ENNReal.tsum_le_tsum hsummand
        _ = lemma79PMFENNExpectation
              (taoSection7HoldListPMF B)
              (longAtom.indicator endpointWeight) * prefactor :=
          lemma79PMFENNExpectation_mul_const
            (taoSection7HoldListPMF B)
            (longAtom.indicator endpointWeight) prefactor
    have hgap : lemma79EntryVerticalGap Delta entry.toPoint = gap := by
      simp [entry, gap]
    have hendpointBound :
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator endpointWeight) ≤
          (taoSection7HoldListPMF B).toOuterMeasure longAtom *
            ENNReal.ofReal lemma79R2ContractionFactor := by
      simpa [family, longAtom, endpointWeight, White, entry, gap] using
        (lemma79_holdList_firstEntryKey_r2EndpointWeight_le_contraction
          hxi hscalar hDelta hpJ hroom
          (by simpa [entry] using hDeltaMem) hgap
          (hlocalizedMass entry gap) hcollar)
    have hscalarReal :
        Real.exp (-(p.pred : ℝ) + 2 * epsilon) *
            lemma79R2ContractionFactor ≤
          Real.exp epsilon := by
      exact
        (lemma79_exp_add_two_epsilon_mul_r2Contraction_le
          (x := -(p.pred : ℝ)) hscalar).trans
          (Real.exp_le_exp.mpr (by
            have hpred : 0 ≤ (p.pred : ℝ) := Nat.cast_nonneg _
            linarith))
    have hscalarENN :
        prefactor * ENNReal.ofReal lemma79R2ContractionFactor ≤
          ENNReal.ofReal (Real.exp epsilon) := by
      dsimp [prefactor]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal hscalarReal
    have hlong :
        lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J 2)) ≤
          (taoSection7HoldListPMF B).toOuterMeasure longAtom *
            ENNReal.ofReal (Real.exp epsilon) := by
      calc
        _ ≤ lemma79PMFENNExpectation
              (taoSection7HoldListPMF B)
              (longAtom.indicator endpointWeight) * prefactor := htoWeight
        _ ≤ ((taoSection7HoldListPMF B).toOuterMeasure longAtom *
              ENNReal.ofReal lemma79R2ContractionFactor) * prefactor :=
          mul_le_mul_right' hendpointBound prefactor
        _ = (taoSection7HoldListPMF B).toOuterMeasure longAtom *
              (prefactor * ENNReal.ofReal lemma79R2ContractionFactor) := by
          ac_rfl
        _ ≤ (taoSection7HoldListPMF B).toOuterMeasure longAtom *
              ENNReal.ofReal (Real.exp epsilon) :=
          mul_le_mul_left' hscalarENN _
    have hExpPull :=
      lemma79_holdList_keyAtom_cutoffTailMomentENN_expectation_eq_of_le
        hJB origin family hpair (some (p, entryPoint))
        (n := n) (R := 2) (xi := xi) (epsilon := epsilon)
    have hMassPull :=
      lemma79_holdList_keyAtom_mass_eq_of_le
        hJB origin family (some (p, entryPoint))
    calc
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF J)
          (shortAtom.indicator
            (lemma79HoldPathCutoffTailMomentENN
              origin family n xi epsilon J 2)) =
          lemma79PMFENNExpectation
            (taoSection7HoldListPMF B)
            (longAtom.indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J 2)) := by
        simpa [shortAtom, longAtom] using hExpPull.symm
      _ ≤ (taoSection7HoldListPMF B).toOuterMeasure longAtom *
          ENNReal.ofReal (Real.exp epsilon) := hlong
      _ = (taoSection7HoldListPMF J).toOuterMeasure shortAtom *
          ENNReal.ofReal (Real.exp epsilon) := by
        rw [hMassPull]

/-- Every canonical semantic `some` key satisfies the killed `R=2` bound. -/
theorem lemma79_canonical_someKey_R2
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
    (origin : TaoSection7RenewalPoint) :
    let J := n / 2
    let family := taoSection7CanonicalTriangleFamily hxi hscalar
    ∀ key : ℕ × TaoSection7Point,
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF J)
          ((lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey origin family J) (some key)).indicator
              (lemma79HoldPathCutoffTailMomentENN
                origin family n xi epsilon J 2)) ≤
        (taoSection7HoldListPMF J).toOuterMeasure
            (lemma79KeyAtom Set.univ
              (lemma79HoldPathHeadKey origin family J) (some key)) *
          ENNReal.ofReal (Real.exp epsilon) := by
  dsimp only
  rintro ⟨p, entryPoint⟩
  exact lemma79_canonical_someKey_R2_of_cutoff_eq
    L hlocalizedMass hxi hscalar hcollar origin rfl p entryPoint

/-- The complete canonical killed `R=2` cutoff expectation is bounded by
`exp epsilon`. -/
theorem lemma79_canonical_R2
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
    (origin : TaoSection7RenewalPoint) :
    let J := n / 2
    let family := taoSection7CanonicalTriangleFamily hxi hscalar
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF J)
        (lemma79HoldPathCutoffTailMomentENN
          origin family n xi epsilon J 2) ≤
      ENNReal.ofReal (Real.exp epsilon) := by
  dsimp only
  exact lemma79_holdList_cutoffTailMomentENN_two_le_of_someKey_bounds
    (n / 2) origin (taoSection7CanonicalTriangleFamily hxi hscalar)
    n xi epsilon
    (lemma79_canonical_someKey_R2
      L hlocalizedMass hxi hscalar hcollar origin)

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
