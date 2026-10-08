/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma77KernelTail

/-!
# Lemma 7.7 Source-Fiber Producer Surface

This module isolates the first producer-facing step for the Lemma 7.7
canonical-bin source package.  The checked bridge below does not prove Tao's
first-passage endpoint law or the horizontal marginal estimate.  Instead, it
records the exact shape those inputs must feed: each canonical source bin must
be contained in a source endpoint/marginal event whose mass is bounded by the
exact two-term kernel summand.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

/--
Single-bin source-fiber bridge from a larger source endpoint/marginal event.

Future Lemma 7.7 work should prove `hbound` from the stopped endpoint law and
horizontal marginal summation, and `hsubset` from the deterministic
positive-side/rounding comparison for the canonical bin.
-/
theorem canonicalBinSourceFiber_le_of_eventBound
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m idx : ℕ} {a b K0 V delta : ℝ}
    {fiberEvent : Set Ωsrc}
    (hsubset :
      sampleOf ⁻¹' centeredHighTailBinEvent start K pre s m delta idx ⊆
        fiberEvent)
    (hbound :
      pmfProb ν fiberEvent ≤ exactKernelTailSummand a b K0 V delta s m idx) :
    pmfProb ν
        (sampleOf ⁻¹' centeredHighTailBinEvent start K pre s m delta idx) ≤
      exactKernelTailSummand a b K0 V delta s m idx :=
  le_trans (pmfProb_mono ν hsubset) hbound

/--
Single-bin source-fiber bridge from a larger target endpoint/marginal event
under the source pushforward law.

This is the shape needed when the future endpoint/marginal estimate is stated
on the sampled `Ω` law rather than directly on the source carrier.
-/
theorem canonicalBinSourceFiber_le_of_targetEventBound
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m idx : ℕ} {a b K0 V delta : ℝ}
    {targetEvent : Set Ω}
    (hsample : μ = ν.map sampleOf)
    (hsubset :
      centeredHighTailBinEvent start K pre s m delta idx ⊆ targetEvent)
    (hbound :
      pmfProb μ targetEvent ≤ exactKernelTailSummand a b K0 V delta s m idx) :
    pmfProb ν
        (sampleOf ⁻¹' centeredHighTailBinEvent start K pre s m delta idx) ≤
      exactKernelTailSummand a b K0 V delta s m idx := by
  have hprob_eq :
      pmfProb μ targetEvent = pmfProb ν (sampleOf ⁻¹' targetEvent) := by
    rw [hsample]
    exact pmfProb_map_preimage ν sampleOf targetEvent
  calc
    pmfProb ν
        (sampleOf ⁻¹' centeredHighTailBinEvent start K pre s m delta idx)
        ≤ pmfProb ν (sampleOf ⁻¹' targetEvent) :=
          pmfProb_mono ν (Set.preimage_mono hsubset)
    _ = pmfProb μ targetEvent := hprob_eq.symm
    _ ≤ exactKernelTailSummand a b K0 V delta s m idx := hbound

/--
Restricted-valid-source inputs for constructing the coherent canonical-bin
source package from source endpoint/marginal events.

The `validSource` field makes the source-domain policy explicit: every source
sample in the centered-tail preimage must have the intended valid
first-passage/stopped-endpoint provenance before the support bound is used.
The `fiberEvent` family is the future source-law surface: each canonical bin is
deterministically contained in the corresponding source event, and the event
has the exact two-term kernel mass bound.
-/
structure RestrictedExactKernelCanonicalBinSourceFiberInputs
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    (ν : PMF Ωsrc) (μ : PMF Ω) (sampleOf : Ωsrc → Ω)
    (start : Ω → TaoSection7RenewalPoint) (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s m N : ℕ) (a b K0 V delta : ℝ)
    (validSource : Set Ωsrc)
    (fiberEvent : ℕ → Set Ωsrc) : Prop where
  sample_law : μ = ν.map sampleOf
  centered_preimage_subset_valid :
    sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource
  support_on_valid :
    ∀ η, η ∈ validSource →
      sampleOf η ∈ centeredHighTailEvent start K pre s m →
        prefixIncrement start K pre (sampleOf η) <
          centeredHighTailBinBase s m delta + N
  canonical_subset :
    ∀ idx, idx ∈ Finset.range N →
      sampleOf ⁻¹' centeredHighTailBinEvent start K pre s m delta idx ⊆
        fiberEvent idx
  fiber_event_bound :
    ∀ idx, idx ∈ Finset.range N →
      pmfProb ν (fiberEvent idx) ≤
        exactKernelTailSummand a b K0 V delta s m idx

/--
The restricted-valid-source fiber inputs fill the existing coherent
canonical-bin source package.
-/
theorem exactKernelCanonicalBinSourceInputs_of_restrictedSourceFiberInputs
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta : ℝ}
    {validSource : Set Ωsrc}
    {fiberEvent : ℕ → Set Ωsrc}
    (hinputs :
      RestrictedExactKernelCanonicalBinSourceFiberInputs
        ν μ sampleOf start K pre s m N a b K0 V delta validSource fiberEvent) :
    ExactKernelCanonicalBinSourceInputs
      ν μ sampleOf start K pre s m N a b K0 V delta where
  sample_law := hinputs.sample_law
  support := by
    intro η hη
    exact
      hinputs.support_on_valid η
        (hinputs.centered_preimage_subset_valid hη) hη
  fiber := by
    intro idx hidx
    exact
      canonicalBinSourceFiber_le_of_eventBound
        (ν := ν) (sampleOf := sampleOf)
        (start := start) (K := K) (pre := pre)
        (s := s) (m := m) (idx := idx)
        (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
        (fiberEvent := fiberEvent idx)
        (hinputs.canonical_subset idx hidx)
        (hinputs.fiber_event_bound idx hidx)

/--
Restricted-valid-source inputs whose per-bin fiber estimates are supplied as
target endpoint/marginal event bounds under the pushforward law.

This is useful when the future first-passage or horizontal marginal theorem is
stated on the sampled renewal-path space `Ω`, while the coherent source
package still needs source preimage fiber bounds under `ν`.
-/
structure RestrictedExactKernelCanonicalBinTargetFiberInputs
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    (ν : PMF Ωsrc) (μ : PMF Ω) (sampleOf : Ωsrc → Ω)
    (start : Ω → TaoSection7RenewalPoint) (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s m N : ℕ) (a b K0 V delta : ℝ)
    (validSource : Set Ωsrc)
    (targetEvent : ℕ → Set Ω) : Prop where
  sample_law : μ = ν.map sampleOf
  centered_preimage_subset_valid :
    sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource
  support_on_valid :
    ∀ η, η ∈ validSource →
      sampleOf η ∈ centeredHighTailEvent start K pre s m →
        prefixIncrement start K pre (sampleOf η) <
          centeredHighTailBinBase s m delta + N
  canonical_subset :
    ∀ idx, idx ∈ Finset.range N →
      centeredHighTailBinEvent start K pre s m delta idx ⊆ targetEvent idx
  target_event_bound :
    ∀ idx, idx ∈ Finset.range N →
      pmfProb μ (targetEvent idx) ≤
        exactKernelTailSummand a b K0 V delta s m idx

/--
Target endpoint/marginal inputs fill the coherent canonical-bin source package
by transporting each target event bound across `μ = ν.map sampleOf`.
-/
theorem exactKernelCanonicalBinSourceInputs_of_restrictedTargetFiberInputs
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta : ℝ}
    {validSource : Set Ωsrc}
    {targetEvent : ℕ → Set Ω}
    (hinputs :
      RestrictedExactKernelCanonicalBinTargetFiberInputs
        ν μ sampleOf start K pre s m N a b K0 V delta validSource targetEvent) :
    ExactKernelCanonicalBinSourceInputs
      ν μ sampleOf start K pre s m N a b K0 V delta where
  sample_law := hinputs.sample_law
  support := by
    intro η hη
    exact
      hinputs.support_on_valid η
        (hinputs.centered_preimage_subset_valid hη) hη
  fiber := by
    intro idx hidx
    exact
      canonicalBinSourceFiber_le_of_targetEventBound
        (ν := ν) (μ := μ) (sampleOf := sampleOf)
        (start := start) (K := K) (pre := pre)
        (s := s) (m := m) (idx := idx)
        (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
        (targetEvent := targetEvent idx)
        hinputs.sample_law
        (hinputs.canonical_subset idx hidx)
        (hinputs.target_event_bound idx hidx)

end TaoSection7Lemma77

end

end Tao
end Erdos1135SecondScale
