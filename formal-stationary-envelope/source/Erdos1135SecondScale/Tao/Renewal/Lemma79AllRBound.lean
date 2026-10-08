/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
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

import Erdos1135SecondScale.Tao.Renewal.Lemma79OneStepBound

/-!
# Lemma 7.9 Killed Native Bounds for Every R

The generic one-step estimate is first instantiated at `R=3` against the
checked `R=2` theorem, then iterated by strong induction uniformly over the
initial renewal point.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A pointwise native bound integrates under any PMF with no finiteness
assumption on the sample type. -/
theorem lemma79PMFENNExpectation_le_const
    {Omega : Type*} (mu : PMF Omega)
    (F : Omega -> ENNReal) (C : ENNReal)
    (hF : ∀ omega, F omega ≤ C) :
    lemma79PMFENNExpectation mu F ≤ C := by
  calc
    lemma79PMFENNExpectation mu F ≤
        lemma79PMFENNExpectation mu (fun _ => C) := by
      unfold lemma79PMFENNExpectation
      apply ENNReal.tsum_le_tsum
      intro omega
      exact mul_le_mul_right (hF omega) _
    _ = (∑' omega, mu omega) * C := by
      unfold lemma79PMFENNExpectation
      exact ENNReal.tsum_mul_right
    _ = C := by rw [PMF.tsum_coe, one_mul]

/-- The canonical killed `R=0` expectation vanishes. -/
theorem lemma79_canonical_R0
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (origin : TaoSection7RenewalPoint) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF (n / 2))
        (lemma79HoldPathCutoffTailMomentENN origin
          (taoSection7CanonicalTriangleFamily hxi hscalar)
          n xi epsilon (n / 2) 0) ≤
      ENNReal.ofReal (Real.exp epsilon) := by
  apply lemma79PMFENNExpectation_le_const
  intro full
  simp [lemma79HoldPathCutoffTailMomentENN]

/-- The canonical killed `R=1` expectation follows from the checked
pointwise total bound. -/
theorem lemma79_canonical_R1
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (origin : TaoSection7RenewalPoint) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF (n / 2))
        (lemma79HoldPathCutoffTailMomentENN origin
          (taoSection7CanonicalTriangleFamily hxi hscalar)
          n xi epsilon (n / 2) 1) ≤
      ENNReal.ofReal (Real.exp epsilon) := by
  let family := taoSection7CanonicalTriangleFamily hxi hscalar
  have hpair : TaoSection7TriangleFamilyPairwiseDisjoint family := by
    simpa [family] using
      taoSection7CanonicalTriangleFamily_pairwiseDisjoint hxi hscalar
  have hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family := by
    simpa [family] using
      taoSection7CanonicalTriangleFamily_cover hxi hscalar
  apply lemma79PMFENNExpectation_le_const
  intro full
  unfold lemma79HoldPathCutoffTailMomentENN
  exact ENNReal.ofReal_le_ofReal
    (lemma79HoldPathCutoffTailMoment_one_le_exp_total hpair hcover)

/-- The first genuinely restarted case follows from the global checked
`R=2` theorem and the generic one-step interface. -/
theorem lemma79_canonical_R3
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
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF (n / 2))
        (lemma79HoldPathCutoffTailMomentENN origin
          (taoSection7CanonicalTriangleFamily hxi hscalar)
          n xi epsilon (n / 2) 3) ≤
      ENNReal.ofReal (Real.exp epsilon) := by
  apply lemma79_canonical_step
    L hlocalizedMass hxi hscalar hcollar (R := 3) (by omega)
  intro endpoint
  simpa using
    (lemma79_canonical_R2
      L hlocalizedMass hxi hscalar hcollar endpoint)

/-- The repaired canonical killed expectation is bounded by `exp epsilon` for
every index and every initial renewal point. -/
theorem lemma79_canonical_all_R
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
        taoSection7TriangleSeparation epsilon ^ 2) :
    ∀ R : ℕ, ∀ origin : TaoSection7RenewalPoint,
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF (n / 2))
          (lemma79HoldPathCutoffTailMomentENN origin
            (taoSection7CanonicalTriangleFamily hxi hscalar)
            n xi epsilon (n / 2) R) ≤
        ENNReal.ofReal (Real.exp epsilon) := by
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      intro origin
      match R with
      | 0 => exact lemma79_canonical_R0 hxi hscalar origin
      | 1 => exact lemma79_canonical_R1 hxi hscalar origin
      | R + 2 =>
          apply lemma79_canonical_step
            L hlocalizedMass hxi hscalar hcollar (R := R + 2) (by omega)
          intro endpoint
          exact ih (R + 1) (by omega) endpoint

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
