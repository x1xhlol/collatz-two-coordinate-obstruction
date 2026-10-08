import Erdos1135.Tao.Renewal.Lemma79R3MasterAtom
import Erdos1135.Tao.Renewal.Lemma79R3Pointwise
import Erdos1135.Tao.Renewal.Lemma79R2PositiveKey

/-!
# Lemma 7.9 Killed One-Step Supported-Atom Bound

This proof leaf converts the real first-exit recurrence into the native
stopped-prefix/fresh-tail integrand on one nonzero semantic-key atom.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- On one supported canonical semantic-key atom, killed `R` is bounded by
the first-exit prefix weight times killed `R-1` on the literal fresh tail. -/
theorem lemma79HoldPathCutoffTailMomentENN_le_firstPassagePair
    {n J B p gap R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hJ : J = n / 2)
    (hR : 2 ≤ R)
    {origin entry : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {Delta : TaoSection7Triangle}
    (hfull : taoSection7HoldListPMF B full ≠ 0)
    (hkey :
      lemma79HoldPathHeadKey origin
          (taoSection7CanonicalTriangleFamily hxi hscalar) J full =
        some (p, entry.toPoint))
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    (hentry : Delta.Mem entry.toPoint)
    (hgap : lemma79EntryVerticalGap Delta entry.toPoint = gap)
    (hroom : p + (gap + 1 + J) ≤ B) :
    let block := (full.drop p).take (gap + 1 + J)
    let pair :=
      lemma79VerticalFirstPassageFixedTailSplit J entry gap block
    let White : Set (ℕ × ℤ) :=
      {x | taoSection7SourceActualW n xi epsilon
        (lemma77RenewalPointOfRelativeEndpoint entry x)}
    lemma79HoldPathCutoffTailMomentENN
        origin (taoSection7CanonicalTriangleFamily hxi hscalar)
        n xi epsilon J R full ≤
      ENNReal.ofReal (Real.exp (-(p.pred : ℝ) + epsilon)) *
        (lemma79R2EndpointWeight White
            (lemma77EndpointOfPrefix entry pair.1) *
          lemma79HoldPathCutoffTailMomentENN
            (taoSection7RenewalPathPoint entry pair.1 pair.1.length)
            (taoSection7CanonicalTriangleFamily hxi hscalar)
            n xi epsilon J (R - 1) pair.2) := by
  dsimp only
  let family := taoSection7CanonicalTriangleFamily hxi hscalar
  let block := (full.drop p).take (gap + 1 + J)
  let K := lemma79VerticalFirstPassageCut entry gap block
  let pair := lemma79VerticalFirstPassageFixedTailSplit J entry gap block
  let endpointCoord := lemma77EndpointOfPrefix entry pair.1
  let endpoint := taoSection7RenewalPathPoint entry pair.1 pair.1.length
  let White : Set (ℕ × ℤ) :=
    {x | taoSection7SourceActualW n xi epsilon
      (lemma77RenewalPointOfRelativeEndpoint entry x)}
  let prefactor := ENNReal.ofReal
    (Real.exp (-(p.pred : ℝ) + epsilon))
  have hpJ : p < J :=
    (lemma79BoundedInclusiveTraceHeadKey_some_spec hkey).1
  have hpairwise : TaoSection7TriangleFamilyPairwiseDisjoint family := by
    simpa [family] using
      taoSection7CanonicalTriangleFamily_pairwiseDisjoint hxi hscalar
  have hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon J) family := by
    simpa [family, hJ] using
      taoSection7CanonicalTriangleFamily_cover hxi hscalar
  rcases lemma79_exists_canonicalTrace_cons_of_headKey
      hxi hscalar hkey hDelta hentry with ⟨rest, htrace⟩
  have hlenB : full.length = B := by
    by_contra hne
    exact hfull
      (taoSection7HoldListPMF_apply_eq_zero_of_length_ne B full hne)
  have hJB : J ≤ B := by omega
  have hlenJ : J ≤ full.length := by rw [hlenB]; exact hJB
  have hdata :
      Lemma79FirstExitCertificate
          (lemma79HoldPathPointAt origin full) Delta p (p + K) ∧
        endpoint = taoSection7RenewalPathPoint origin full (p + K) ∧
        pair.2 = (full.drop (p + K)).take J ∧
        K ≤ gap + 1 := by
    simpa [family, block, K, pair, endpoint,
      lemma79HoldPathHeadKey] using
      (lemma79FirstPassageFixedTailData_of_holdListPMF_ne_zero
        (family := family) (C := J) Delta hfull
        (by simpa [lemma79HoldPathHeadKey] using hkey)
        hentry hgap hroom)
  rcases hdata with ⟨hexit, hendpoint, hfresh, _hKLe⟩
  have hrelative :
      lemma77RenewalPointOfRelativeEndpoint entry endpointCoord =
        taoSection7RenewalPathPoint origin full (p + K) := by
    exact
      (lemma77RenewalPointOfRelativeEndpoint_endpointOfPrefix
        entry pair.1).trans hendpoint
  have hrestart :
      lemma79HoldPathRestartPointAt origin full p K =
        (lemma77RenewalPointOfRelativeEndpoint entry endpointCoord).toPoint := by
    rw [lemma79HoldPathRestartPointAt_eq]
    unfold lemma79HoldPathPointAt
    exact congrArg TaoSection7RenewalPoint.toPoint hrelative.symm
  have hwhiteIff :
      endpointCoord ∈ White ↔
        taoSection7SourceWhiteWCutoff n xi epsilon J
          ((lemma79HoldPathRestartPointAt origin full p K).j : ℕ)
          (lemma79HoldPathRestartPointAt origin full p K).l := by
    rw [hrestart]
    simp [White, taoSection7SourceActualW,
      taoSection7SourceWhiteRenewal, hJ]
  have hfutureEq :
      ENNReal.ofReal
          (lemma79CutoffTailMoment
            (lemma79HoldPathRestartPointAt origin full (p + K))
            family n xi epsilon J (R - 1)) =
        lemma79HoldPathCutoffTailMomentENN
          endpoint family n xi epsilon J (R - 1) pair.2 := by
    exact lemma79HoldPathCutoffTailMomentENN_restart_eq_freshTail
      hpairwise hendpoint hfresh
  by_cases hdead : J ≤ p + K
  · have hzero :
        lemma79CutoffTailMoment
            (lemma79HoldPathPointAt origin full)
            family n xi epsilon J R = 0 :=
      lemma79CutoffTailMoment_eq_zero_of_cutoff_le_firstExit
        (R := R) (by omega) hpairwise (by simpa [family] using htrace)
        hexit hdead
    change ENNReal.ofReal
        (lemma79CutoffTailMoment
          (lemma79HoldPathPointAt origin full)
          family n xi epsilon J R) ≤ _
    rw [hzero]
    simp only [ENNReal.ofReal_zero]
    exact bot_le
  · have hreal :=
      lemma79HoldPathCutoffTailMoment_le_firstExitWeight_mul_restart
        (R := R) hR hpairwise hcover hlenJ hexit
          (by simpa [family] using htrace)
    by_cases hwhite : endpointCoord ∈ White
    · have hwhiteGlobal := hwhiteIff.mp hwhite
      rw [ite_eq_left hwhiteGlobal] at hreal
      unfold lemma79HoldPathCutoffTailMomentENN
      calc
        ENNReal.ofReal
            (lemma79CutoffTailMoment
              (lemma79HoldPathPointAt origin full)
              family n xi epsilon J R) ≤
            ENNReal.ofReal
              ((Real.exp (-(p.pred : ℝ) + epsilon) * Real.exp (-1)) *
                lemma79CutoffTailMoment
                  (lemma79HoldPathRestartPointAt origin full (p + K))
                  family n xi epsilon J (R - 1)) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (Real.exp (-(p.pred : ℝ) + epsilon)) *
            (ENNReal.ofReal (Real.exp (-1)) *
              ENNReal.ofReal
                (lemma79CutoffTailMoment
                  (lemma79HoldPathRestartPointAt origin full (p + K))
                  family n xi epsilon J (R - 1))) := by
          rw [ENNReal.ofReal_mul
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          ac_rfl
        _ = prefactor *
            (lemma79R2EndpointWeight White endpointCoord *
              lemma79HoldPathCutoffTailMomentENN
                endpoint family n xi epsilon J (R - 1) pair.2) := by
          rw [hfutureEq]
          simp [prefactor, lemma79R2EndpointWeight, hwhite]
    · have hwhiteGlobal :
          ¬ taoSection7SourceWhiteWCutoff n xi epsilon J
            ((lemma79HoldPathRestartPointAt origin full p K).j : ℕ)
            (lemma79HoldPathRestartPointAt origin full p K).l :=
        fun h => hwhite (hwhiteIff.mpr h)
      rw [ite_eq_right hwhiteGlobal, mul_one] at hreal
      unfold lemma79HoldPathCutoffTailMomentENN
      calc
        ENNReal.ofReal
            (lemma79CutoffTailMoment
              (lemma79HoldPathPointAt origin full)
              family n xi epsilon J R) ≤
            ENNReal.ofReal
              (Real.exp (-(p.pred : ℝ) + epsilon) *
                lemma79CutoffTailMoment
                  (lemma79HoldPathRestartPointAt origin full (p + K))
                  family n xi epsilon J (R - 1)) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (Real.exp (-(p.pred : ℝ) + epsilon)) *
            ENNReal.ofReal
              (lemma79CutoffTailMoment
                (lemma79HoldPathRestartPointAt origin full (p + K))
                family n xi epsilon J (R - 1)) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        _ = prefactor *
            (lemma79R2EndpointWeight White endpointCoord *
              lemma79HoldPathCutoffTailMomentENN
                endpoint family n xi epsilon J (R - 1) pair.2) := by
          rw [hfutureEq]
          simp [prefactor, lemma79R2EndpointWeight, hwhite]

/-- The generic supported-atom step specialized to the first new canary
`R=3`. -/
theorem lemma79HoldPathCutoffTailMomentENN_three_le_firstPassagePair
    {n J B p gap : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hJ : J = n / 2)
    {origin entry : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {Delta : TaoSection7Triangle}
    (hfull : taoSection7HoldListPMF B full ≠ 0)
    (hkey :
      lemma79HoldPathHeadKey origin
          (taoSection7CanonicalTriangleFamily hxi hscalar) J full =
        some (p, entry.toPoint))
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    (hentry : Delta.Mem entry.toPoint)
    (hgap : lemma79EntryVerticalGap Delta entry.toPoint = gap)
    (hroom : p + (gap + 1 + J) ≤ B) :
    let block := (full.drop p).take (gap + 1 + J)
    let pair :=
      lemma79VerticalFirstPassageFixedTailSplit J entry gap block
    let White : Set (ℕ × ℤ) :=
      {x | taoSection7SourceActualW n xi epsilon
        (lemma77RenewalPointOfRelativeEndpoint entry x)}
    lemma79HoldPathCutoffTailMomentENN
        origin (taoSection7CanonicalTriangleFamily hxi hscalar)
        n xi epsilon J 3 full ≤
      ENNReal.ofReal (Real.exp (-(p.pred : ℝ) + epsilon)) *
        (lemma79R2EndpointWeight White
            (lemma77EndpointOfPrefix entry pair.1) *
          lemma79HoldPathCutoffTailMomentENN
            (taoSection7RenewalPathPoint entry pair.1 pair.1.length)
            (taoSection7CanonicalTriangleFamily hxi hscalar)
            n xi epsilon J 2 pair.2) := by
  exact lemma79HoldPathCutoffTailMomentENN_le_firstPassagePair
    hxi hscalar hJ (R := 3) (by omega) hfull hkey hDelta hentry hgap hroom

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
