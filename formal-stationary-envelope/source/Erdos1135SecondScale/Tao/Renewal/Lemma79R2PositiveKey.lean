/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Lemma74CanonicalFamily
import Erdos1135SecondScale.Tao.Fourier.Lemma74ClaimStarScalars
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2Aggregation
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2MasterAtom

/-!
# Lemma 7.9 Killed R=2 Positive-Key Witnesses

This proof leaf turns positive mass of a semantic first-entry fiber into one
supported Hold sample.  For the canonical triangle family it also records the
unique triangle containing the entry point.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A positive first-entry key fiber contains a supported Hold sample whose
head key has the advertised first-hit semantics. -/
theorem lemma79_exists_supported_firstEntry_of_keyAtom_ne_zero
    (J : ℕ) (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (p : ℕ) (entryPoint : TaoSection7Point)
    (hmass :
      (taoSection7HoldListPMF J).toOuterMeasure
          (lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey start family J)
            (some (p, entryPoint))) ≠ 0) :
    ∃ full : List TaoSection7RenewalPoint,
      taoSection7HoldListPMF J full ≠ 0 ∧
        lemma79HoldPathHeadKey start family J full =
          some (p, entryPoint) ∧
        p < J ∧
        entryPoint = lemma79HoldPathPointAt start full p ∧
        Lemma79FirstTriangleHitFromZero
          (lemma79HoldPathPointAt start full) family p := by
  let mu := taoSection7HoldListPMF J
  let atom :=
    lemma79KeyAtom Set.univ
      (lemma79HoldPathHeadKey start family J)
      (some (p, entryPoint))
  have hnotDisjoint : ¬ Disjoint mu.support atom := by
    intro hdisjoint
    exact hmass
      ((PMF.toOuterMeasure_apply_eq_zero_iff mu atom).2 hdisjoint)
  rcases Set.not_disjoint_iff.mp hnotDisjoint with
    ⟨full, hfull, hatom⟩
  have hkey :
      lemma79HoldPathHeadKey start family J full =
        some (p, entryPoint) := by
    exact hatom.2
  have hspec := lemma79BoundedInclusiveTraceHeadKey_some_spec hkey
  exact ⟨full, hfull, hkey, hspec.1, hspec.2.1, hspec.2.2⟩

/-- Positive mass of a canonical semantic key determines a supported sample
and the unique canonical triangle containing its first-entry point. -/
theorem lemma79_exists_supported_firstEntry_unique_canonicalTriangle
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (J : ℕ) (start : TaoSection7RenewalPoint)
    (p : ℕ) (entryPoint : TaoSection7Point)
    (hmass :
      (taoSection7HoldListPMF J).toOuterMeasure
          (lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey start
              (taoSection7CanonicalTriangleFamily hxi hscalar) J)
            (some (p, entryPoint))) ≠ 0) :
    ∃ full : List TaoSection7RenewalPoint,
      taoSection7HoldListPMF J full ≠ 0 ∧
        lemma79HoldPathHeadKey start
            (taoSection7CanonicalTriangleFamily hxi hscalar) J full =
          some (p, entryPoint) ∧
        p < J ∧
        entryPoint = lemma79HoldPathPointAt start full p ∧
        ∃ Delta : TaoSection7Triangle,
          Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar ∧
          Delta.Mem entryPoint ∧
          ∀ Gamma : TaoSection7Triangle,
            Gamma ∈ taoSection7CanonicalTriangleFamily hxi hscalar ->
            Gamma.Mem entryPoint -> Gamma = Delta := by
  rcases lemma79_exists_supported_firstEntry_of_keyAtom_ne_zero
      J start (taoSection7CanonicalTriangleFamily hxi hscalar)
      p entryPoint hmass with
    ⟨full, hfull, hkey, hpJ, hentry, hfirst⟩
  rcases hfirst.1 with ⟨Delta, hDelta, hDeltaMem⟩
  refine ⟨full, hfull, hkey, hpJ, hentry, Delta, hDelta, ?_, ?_⟩
  · simpa [hentry] using hDeltaMem
  · intro Gamma hGamma hGammaMem
    exact
      (taoSection7CanonicalTriangleFamily_eq_of_common_mem
        hxi hscalar hGamma hDelta hGammaMem
          (by simpa [hentry] using hDeltaMem))

/-- A present canonical semantic key exposes the canonical cutoff trace with
its uniquely determined entry triangle at the head. -/
theorem lemma79_exists_canonicalTrace_cons_of_headKey
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {C p : ℕ} {entryPoint : TaoSection7Point}
    {Delta : TaoSection7Triangle}
    (hkey :
      lemma79HoldPathHeadKey start
          (taoSection7CanonicalTriangleFamily hxi hscalar) C full =
        some (p, entryPoint))
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    (hDeltaMem : Delta.Mem entryPoint) :
    ∃ rest : List (ℕ × TaoSection7Triangle),
      Lemma79BoundedInclusiveTrace
        (lemma79HoldPathPointAt start full)
        (taoSection7CanonicalTriangleFamily hxi hscalar) C
        ((p, Delta) :: rest) := by
  let pointAt := lemma79HoldPathPointAt start full
  let family := taoSection7CanonicalTriangleFamily hxi hscalar
  let steps := lemma79CutoffTrace pointAt family C
  have htrace := lemma79CutoffTrace_spec pointAt family C
  change Lemma79BoundedInclusiveTrace pointAt family C steps at htrace
  have hhead : lemma79InclusiveTraceHeadKey pointAt steps =
      some (p, entryPoint) := by
    simpa [pointAt, family, steps, lemma79CutoffTrace,
      lemma79HoldPathHeadKey, lemma79BoundedInclusiveTraceHeadKey] using hkey
  cases hsteps : steps with
  | nil =>
      rw [hsteps] at hhead
      simp at hhead
  | cons step rest =>
      rcases step with ⟨q, Gamma⟩
      rw [hsteps] at hhead htrace
      simp only [lemma79InclusiveTraceHeadKey_cons,
        Option.some.injEq, Prod.mk.injEq] at hhead
      rcases hhead with ⟨rfl, hentry⟩
      cases hprefix : htrace.trace_prefix with
      | cons hfirst hGamma hGammaMem htail =>
          have hGammaEq : Gamma = Delta :=
            taoSection7CanonicalTriangleFamily_eq_of_common_mem
              hxi hscalar hGamma hDelta hGammaMem
                (by simpa [hentry] using hDeltaMem)
          subst Gamma
          exact ⟨rest, htrace⟩

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
