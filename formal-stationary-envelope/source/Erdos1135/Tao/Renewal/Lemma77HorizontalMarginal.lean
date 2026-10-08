import Erdos1135.Tao.Renewal.Lemma77SourceFiber
import Erdos1135.Tao.Renewal.Lemma77PotentialCore

/-!
# Lemma 7.7 Horizontal-Marginal Event Bound Surface

This module names the horizontal marginal event used by the Lemma 7.7
canonical-bin source-fiber route and proves the finite summation step from
vertical endpoint fibers to that horizontal marginal.

It names the relative vertical overshoot coordinate, but does not prove Tao's
relative first-passage endpoint law, the vertical overshoot estimates, or the
positive-side/rounding comparison to the exact kernel summand.  Those remain
explicit inputs to the checked summation consumer below.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

/-- Horizontal marginal event for a fixed relative stopped-prefix displacement. -/
def relativeHorizontalEvent
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (r : ℕ) : Set Ω :=
  {ω | prefixIncrement start K pre ω = r}

/--
Two-dimensional relative endpoint fiber at horizontal displacement `r` and
vertical displacement `ell`.
-/
def relativeEndpointFiberEvent
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (r : ℕ) (ell : ℤ) : Set Ω :=
  {ω |
    prefixIncrement start K pre ω = r ∧
      prefixVerticalIncrement start K pre ω = ell}

/--
Vertical overshoot above Tao's first-passage threshold in relative
coordinates.

If `s = l_Delta - l` and `ell = l' - l`, then this is `l' - l_Delta`.
-/
def relativeVerticalOvershoot (s : ℕ) (ell : ℤ) : ℤ :=
  ell - (s : ℤ)

/-- Membership in an endpoint fiber rewrites the sample's vertical overshoot. -/
theorem relativeEndpointFiberEvent_verticalOvershoot_eq
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {r s : ℕ} {ell : ℤ} {ω : Ω}
    (hω : ω ∈ relativeEndpointFiberEvent start K pre r ell) :
    prefixVerticalIncrement start K pre ω - (s : ℤ) =
      relativeVerticalOvershoot s ell := by
  rw [relativeEndpointFiberEvent] at hω
  simp [relativeVerticalOvershoot, hω.2]

/--
If `lDelta = start.l + s`, the relative vertical overshoot is the endpoint
height above `lDelta`.
-/
theorem prefixVerticalOvershoot_eq_endpoint_l_sub_delta
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ} {lDelta : ℤ} {ω : Ω}
    (hDelta : lDelta = (start ω).l + (s : ℤ)) :
    prefixVerticalIncrement start K pre ω - (s : ℤ) =
      (taoSection7RenewalPathPoint (start ω) (pre ω) (K ω)).l -
        lDelta := by
  rw [hDelta]
  dsimp [prefixVerticalIncrement]
  ring

/-- Positivity of the overshoot is the shifted support condition `s < ell`. -/
theorem relativeVerticalOvershoot_pos_of_lt
    {s : ℕ} {ell : ℤ} (hlt : (s : ℤ) < ell) :
    0 < relativeVerticalOvershoot s ell := by
  exact sub_pos.mpr hlt

/--
A certified vertical first-passage prefix has positive relative vertical
overshoot at its endpoint.
-/
theorem verticalFirstPassagePrefix_prefixVerticalIncrement_gt
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ} {ω : Ω}
    (hfirst :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        (start ω) s (K ω) (pre ω)) :
    (s : ℤ) < prefixVerticalIncrement start K pre ω := by
  have hcross := hfirst.crosses
  dsimp [prefixVerticalIncrement] at *
  omega

/--
Endpoint-fiber membership rewrites the first-passage endpoint positivity into
the fiber's relative vertical coordinate.
-/
theorem relativeEndpointFiberEvent_positiveOvershoot_of_verticalFirstPassagePrefix
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {r s : ℕ} {ell : ℤ} {ω : Ω}
    (hfirst :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        (start ω) s (K ω) (pre ω))
    (hω : ω ∈ relativeEndpointFiberEvent start K pre r ell) :
    (s : ℤ) < ell := by
  rw [relativeEndpointFiberEvent] at hω
  simpa [hω.2] using
    verticalFirstPassagePrefix_prefixVerticalIncrement_gt
      (start := start) (K := K) (pre := pre) hfirst

/-- A canonical bin is the corresponding relative horizontal marginal event. -/
theorem centeredHighTailBinEvent_subset_relativeHorizontalEvent
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m idx : ℕ} {delta : ℝ} :
    centeredHighTailBinEvent start K pre s m delta idx ⊆
      relativeHorizontalEvent start K pre
        (centeredHighTailBinBase s m delta + idx) := by
  intro ω hω
  simpa [centeredHighTailBinEvent, relativeHorizontalEvent] using hω

/--
Finite vertical-fiber cover of a horizontal marginal event.

This is the formal summation step corresponding to "sum the two-dimensional
endpoint law in the vertical coordinate" before any analytic estimate is used.
-/
theorem relativeHorizontal_prob_le_sum_verticalFibers
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {r : ℕ}
    (verticals : Finset ℤ)
    (hcover :
      ∀ ω,
        ω ∈ relativeHorizontalEvent start K pre r →
          ∃ ell, ell ∈ verticals ∧
            ω ∈ relativeEndpointFiberEvent start K pre r ell) :
    pmfProb μ (relativeHorizontalEvent start K pre r) ≤
      verticals.sum fun ell =>
        pmfProb μ (relativeEndpointFiberEvent start K pre r ell) :=
  TaoSection7Lemma710.pmfProb_le_finset_sum_of_subset_exists
    μ verticals (fun ell => relativeEndpointFiberEvent start K pre r ell)
    (relativeHorizontalEvent start K pre r) hcover

/--
Deterministic cover of a horizontal marginal event by vertical endpoint fibers,
provided the chosen finite vertical set contains each sample's vertical
increment.
-/
theorem relativeHorizontalEvent_verticalFiberCover_of_prefixVertical_mem
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {r : ℕ} (verticals : Finset ℤ)
    (hmem :
      ∀ ω,
        ω ∈ relativeHorizontalEvent start K pre r →
          prefixVerticalIncrement start K pre ω ∈ verticals) :
    ∀ ω,
      ω ∈ relativeHorizontalEvent start K pre r →
        ∃ ell, ell ∈ verticals ∧
          ω ∈ relativeEndpointFiberEvent start K pre r ell := by
  intro ω hω
  refine ⟨prefixVerticalIncrement start K pre ω, hmem ω hω, ?_⟩
  exact
    ⟨by simpa [relativeHorizontalEvent] using hω, rfl⟩

/--
The finite set of vertical increments actually attained by samples in a fixed
relative horizontal marginal event.
-/
def relativeHorizontalVerticalSupport
    {Ω : Type*} [Fintype Ω]
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (r : ℕ) : Finset ℤ :=
  (Finset.univ.filter fun ω => prefixIncrement start K pre ω = r).image
    (fun ω => prefixVerticalIncrement start K pre ω)

/--
Every sample in a horizontal marginal event lies in its actual finite vertical
fiber support.

This is a deterministic finite-sample cover only; it is not Tao's
source-faithful vertical support estimate.
-/
theorem relativeHorizontalEvent_fintypeVerticalFiberCover
    {Ω : Type*} [Fintype Ω]
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {r : ℕ} :
    ∀ ω,
      ω ∈ relativeHorizontalEvent start K pre r →
        ∃ ell,
          ell ∈ relativeHorizontalVerticalSupport start K pre r ∧
            ω ∈ relativeEndpointFiberEvent start K pre r ell :=
  relativeHorizontalEvent_verticalFiberCover_of_prefixVertical_mem
    (start := start) (K := K) (pre := pre) (r := r)
    (relativeHorizontalVerticalSupport start K pre r)
    (by
      intro ω hω
      have hprefix : prefixIncrement start K pre ω = r := by
        simpa [relativeHorizontalEvent] using hω
      refine Finset.mem_image.mpr ?_
      exact ⟨ω, by simp [hprefix], rfl⟩)

/--
First-passage certificates on a horizontal marginal event imply positive
overshoot on its actual finite vertical support.
-/
theorem relativeHorizontalVerticalSupport_positiveOvershoot_of_verticalFirstPassage
    {Ω : Type*} [Fintype Ω]
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s r : ℕ}
    (hfirst :
      ∀ ω,
        ω ∈ relativeHorizontalEvent start K pre r →
          TaoSection7Lemma710.VerticalFirstPassagePrefix
            (start ω) s (K ω) (pre ω)) :
    ∀ ell,
      ell ∈ relativeHorizontalVerticalSupport start K pre r →
        (s : ℤ) < ell := by
  intro ell hell
  rw [relativeHorizontalVerticalSupport] at hell
  rcases Finset.mem_image.mp hell with ⟨ω, hωmem, rfl⟩
  have hprefix : prefixIncrement start K pre ω = r :=
    (Finset.mem_filter.mp hωmem).2
  have hω : ω ∈ relativeHorizontalEvent start K pre r := by
    simpa [relativeHorizontalEvent] using hprefix
  exact
    verticalFirstPassagePrefix_prefixVerticalIncrement_gt
      (start := start) (K := K) (pre := pre) (hfirst ω hω)

/--
Horizontal marginal bound from finite vertical endpoint-fiber bounds and a
summed vertical kernel comparison.

The `hfiber` hypotheses are where the future relative first-passage endpoint
law enters.  The `hsum` hypothesis is where the vertical-overshoot summation
and positive-side/rounding comparison to `exactKernelTailSummand` enter.
-/
theorem relativeHorizontal_prob_le_exactKernelTailSummand_of_verticalFibers
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {r s m idx : ℕ} {a b K0 V delta : ℝ}
    (verticals : Finset ℤ)
    (fiberMass : ℤ → ℝ)
    (hcover :
      ∀ ω,
        ω ∈ relativeHorizontalEvent start K pre r →
          ∃ ell, ell ∈ verticals ∧
            ω ∈ relativeEndpointFiberEvent start K pre r ell)
    (hfiber :
      ∀ ell, ell ∈ verticals →
        pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          fiberMass ell)
    (hsum :
      verticals.sum fiberMass ≤
        exactKernelTailSummand a b K0 V delta s m idx) :
    pmfProb μ (relativeHorizontalEvent start K pre r) ≤
      exactKernelTailSummand a b K0 V delta s m idx := by
  calc
    pmfProb μ (relativeHorizontalEvent start K pre r)
        ≤ verticals.sum fun ell =>
            pmfProb μ (relativeEndpointFiberEvent start K pre r ell) :=
          relativeHorizontal_prob_le_sum_verticalFibers
            (μ := μ) (start := start) (K := K) (pre := pre)
            (r := r) verticals hcover
    _ ≤ verticals.sum fiberMass := by
          exact Finset.sum_le_sum fun ell hell => hfiber ell hell
    _ ≤ exactKernelTailSummand a b K0 V delta s m idx := hsum

/--
Horizontal marginal bound from vertical endpoint fibers whose estimates are
stated in Tao's shifted vertical overshoot coordinate.

This is the producer-facing version of
`relativeHorizontal_prob_le_exactKernelTailSummand_of_verticalFibers`: the
per-fiber estimate and vertical sum must use `relativeVerticalOvershoot s ell`,
not raw `ell`, and the positive-side support enters as `s < ell`.
-/
theorem relativeHorizontal_prob_le_exactKernelTailSummand_of_positiveOvershootVerticalFibers
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {r s m idx : ℕ} {a b K0 V delta : ℝ}
    (verticals : Finset ℤ)
    (overshootMass : ℤ → ℝ)
    (hcover :
      ∀ ω,
        ω ∈ relativeHorizontalEvent start K pre r →
          ∃ ell, ell ∈ verticals ∧
            ω ∈ relativeEndpointFiberEvent start K pre r ell)
    (hpositive :
      ∀ ell, ell ∈ verticals → (s : ℤ) < ell)
    (hfiber :
      ∀ ell, ell ∈ verticals →
        0 < relativeVerticalOvershoot s ell →
          pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
            overshootMass (relativeVerticalOvershoot s ell))
    (hsum :
      verticals.sum (fun ell => overshootMass (relativeVerticalOvershoot s ell)) ≤
        exactKernelTailSummand a b K0 V delta s m idx) :
    pmfProb μ (relativeHorizontalEvent start K pre r) ≤
      exactKernelTailSummand a b K0 V delta s m idx :=
  relativeHorizontal_prob_le_exactKernelTailSummand_of_verticalFibers
    (μ := μ) (start := start) (K := K) (pre := pre)
    (r := r) (s := s) (m := m) (idx := idx)
    (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
    verticals
    (fun ell => overshootMass (relativeVerticalOvershoot s ell))
    hcover
    (fun ell hell =>
      hfiber ell hell (relativeVerticalOvershoot_pos_of_lt (hpositive ell hell)))
    hsum

/--
Restricted target-fiber package from horizontal marginal bounds at the
canonical bin bases.

The hard analytic input is `hmarginal`: for each canonical horizontal value
`centeredHighTailBinBase s m delta + idx`, it should be proved from the
relative endpoint law after summing the vertical coordinate and comparing the
resulting marginal kernel to `exactKernelTailSummand`.
-/
theorem restrictedTargetFiberInputs_of_horizontalMarginalBounds
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta : ℝ}
    {validSource : Set Ωsrc}
    (hsample : μ = ν.map sampleOf)
    (hvalid :
      sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource)
    (hsupport :
      ∀ η, η ∈ validSource →
        sampleOf η ∈ centeredHighTailEvent start K pre s m →
          prefixIncrement start K pre (sampleOf η) <
            centeredHighTailBinBase s m delta + N)
    (hmarginal :
      ∀ idx, idx ∈ Finset.range N →
        pmfProb μ
            (relativeHorizontalEvent start K pre
              (centeredHighTailBinBase s m delta + idx)) ≤
          exactKernelTailSummand a b K0 V delta s m idx) :
    RestrictedExactKernelCanonicalBinTargetFiberInputs
      ν μ sampleOf start K pre s m N a b K0 V delta validSource
        (fun idx =>
          relativeHorizontalEvent start K pre
            (centeredHighTailBinBase s m delta + idx)) where
  sample_law := hsample
  centered_preimage_subset_valid := hvalid
  support_on_valid := hsupport
  canonical_subset := by
    intro idx _hidx
    exact centeredHighTailBinEvent_subset_relativeHorizontalEvent
  target_event_bound := hmarginal

/--
Restricted target-fiber package directly from vertical endpoint-fiber data at
each canonical bin.

This is the all-bin producer-facing form of the horizontal-marginal socket:
the remaining inputs are exactly a finite vertical cover, a per-vertical
relative endpoint bound, and a summed-kernel comparison for each canonical
horizontal value.
-/
theorem restrictedTargetFiberInputs_of_verticalFiberBounds
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta : ℝ}
    {validSource : Set Ωsrc}
    (verticals : ℕ → Finset ℤ)
    (fiberMass : ℕ → ℤ → ℝ)
    (hsample : μ = ν.map sampleOf)
    (hvalid :
      sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource)
    (hsupport :
      ∀ η, η ∈ validSource →
        sampleOf η ∈ centeredHighTailEvent start K pre s m →
          prefixIncrement start K pre (sampleOf η) <
            centeredHighTailBinBase s m delta + N)
    (hcover :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ω,
          ω ∈ relativeHorizontalEvent start K pre
              (centeredHighTailBinBase s m delta + idx) →
            ∃ ell, ell ∈ verticals idx ∧
              ω ∈ relativeEndpointFiberEvent start K pre
                (centeredHighTailBinBase s m delta + idx) ell)
    (hfiber :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ell, ell ∈ verticals idx →
          pmfProb μ
              (relativeEndpointFiberEvent start K pre
                (centeredHighTailBinBase s m delta + idx) ell) ≤
            fiberMass idx ell)
    (hsum :
      ∀ idx, idx ∈ Finset.range N →
        (verticals idx).sum (fiberMass idx) ≤
          exactKernelTailSummand a b K0 V delta s m idx) :
    RestrictedExactKernelCanonicalBinTargetFiberInputs
      ν μ sampleOf start K pre s m N a b K0 V delta validSource
        (fun idx =>
          relativeHorizontalEvent start K pre
            (centeredHighTailBinBase s m delta + idx)) :=
  restrictedTargetFiberInputs_of_horizontalMarginalBounds
    (ν := ν) (sampleOf := sampleOf) (μ := μ)
    (start := start) (K := K) (pre := pre)
    (s := s) (m := m) (N := N)
    (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
    (validSource := validSource)
    hsample hvalid hsupport
    (by
      intro idx hidx
      exact
        relativeHorizontal_prob_le_exactKernelTailSummand_of_verticalFibers
          (μ := μ) (start := start) (K := K) (pre := pre)
          (r := centeredHighTailBinBase s m delta + idx)
          (s := s) (m := m) (idx := idx)
          (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
          (verticals idx) (fiberMass idx)
          (hcover idx hidx)
          (hfiber idx hidx)
          (hsum idx hidx))

/--
Restricted target-fiber package from positive-overshoot vertical endpoint
fiber data at each canonical bin.

This is the source-faithful all-bin producer form for the Lemma 7.7
vertical-coordinate step: finite vertical covers may still be supplied
abstractly, but each per-fiber estimate and each vertical sum is indexed by
`relativeVerticalOvershoot s ell = ell - s`, with an explicit support proof
that the overshoot is positive.
-/
theorem restrictedTargetFiberInputs_of_positiveOvershootVerticalFiberBounds
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta : ℝ}
    {validSource : Set Ωsrc}
    (verticals : ℕ → Finset ℤ)
    (overshootMass : ℕ → ℤ → ℝ)
    (hsample : μ = ν.map sampleOf)
    (hvalid :
      sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource)
    (hsupport :
      ∀ η, η ∈ validSource →
        sampleOf η ∈ centeredHighTailEvent start K pre s m →
          prefixIncrement start K pre (sampleOf η) <
            centeredHighTailBinBase s m delta + N)
    (hcover :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ω,
          ω ∈ relativeHorizontalEvent start K pre
              (centeredHighTailBinBase s m delta + idx) →
            ∃ ell, ell ∈ verticals idx ∧
              ω ∈ relativeEndpointFiberEvent start K pre
                (centeredHighTailBinBase s m delta + idx) ell)
    (hpositive :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ell, ell ∈ verticals idx → (s : ℤ) < ell)
    (hfiber :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ell, ell ∈ verticals idx →
          0 < relativeVerticalOvershoot s ell →
            pmfProb μ
                (relativeEndpointFiberEvent start K pre
                  (centeredHighTailBinBase s m delta + idx) ell) ≤
              overshootMass idx (relativeVerticalOvershoot s ell))
    (hsum :
      ∀ idx, idx ∈ Finset.range N →
        (verticals idx).sum
            (fun ell => overshootMass idx (relativeVerticalOvershoot s ell)) ≤
          exactKernelTailSummand a b K0 V delta s m idx) :
    RestrictedExactKernelCanonicalBinTargetFiberInputs
      ν μ sampleOf start K pre s m N a b K0 V delta validSource
        (fun idx =>
          relativeHorizontalEvent start K pre
            (centeredHighTailBinBase s m delta + idx)) :=
  restrictedTargetFiberInputs_of_horizontalMarginalBounds
    (ν := ν) (sampleOf := sampleOf) (μ := μ)
    (start := start) (K := K) (pre := pre)
    (s := s) (m := m) (N := N)
    (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
    (validSource := validSource)
    hsample hvalid hsupport
    (by
      intro idx hidx
      exact
        relativeHorizontal_prob_le_exactKernelTailSummand_of_positiveOvershootVerticalFibers
          (μ := μ) (start := start) (K := K) (pre := pre)
          (r := centeredHighTailBinBase s m delta + idx)
          (s := s) (m := m) (idx := idx)
          (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
          (verticals idx) (overshootMass idx)
          (hcover idx hidx)
          (hpositive idx hidx)
          (hfiber idx hidx)
          (hsum idx hidx))

/--
Restricted target-fiber package using the actual finite vertical support of
each canonical horizontal marginal.

This removes only the deterministic `hcover` premise from the positive
overshoot all-bin socket.  The analytic endpoint-fiber estimates, positive
support, and vertical summation remain explicit hypotheses.
-/
theorem restrictedTargetFiberInputs_of_positiveOvershootFintypeVerticalSupportBounds
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta : ℝ}
    {validSource : Set Ωsrc}
    (overshootMass : ℕ → ℤ → ℝ)
    (hsample : μ = ν.map sampleOf)
    (hvalid :
      sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource)
    (hsupport :
      ∀ η, η ∈ validSource →
        sampleOf η ∈ centeredHighTailEvent start K pre s m →
          prefixIncrement start K pre (sampleOf η) <
            centeredHighTailBinBase s m delta + N)
    (hpositive :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ell,
          ell ∈ relativeHorizontalVerticalSupport start K pre
            (centeredHighTailBinBase s m delta + idx) →
            (s : ℤ) < ell)
    (hfiber :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ell,
          ell ∈ relativeHorizontalVerticalSupport start K pre
            (centeredHighTailBinBase s m delta + idx) →
          0 < relativeVerticalOvershoot s ell →
            pmfProb μ
                (relativeEndpointFiberEvent start K pre
                  (centeredHighTailBinBase s m delta + idx) ell) ≤
              overshootMass idx (relativeVerticalOvershoot s ell))
    (hsum :
      ∀ idx, idx ∈ Finset.range N →
        (relativeHorizontalVerticalSupport start K pre
            (centeredHighTailBinBase s m delta + idx)).sum
            (fun ell => overshootMass idx (relativeVerticalOvershoot s ell)) ≤
          exactKernelTailSummand a b K0 V delta s m idx) :
    RestrictedExactKernelCanonicalBinTargetFiberInputs
      ν μ sampleOf start K pre s m N a b K0 V delta validSource
        (fun idx =>
          relativeHorizontalEvent start K pre
            (centeredHighTailBinBase s m delta + idx)) :=
  restrictedTargetFiberInputs_of_positiveOvershootVerticalFiberBounds
    (ν := ν) (sampleOf := sampleOf) (μ := μ)
    (start := start) (K := K) (pre := pre)
    (s := s) (m := m) (N := N)
    (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
    (validSource := validSource)
    (fun idx =>
      relativeHorizontalVerticalSupport start K pre
        (centeredHighTailBinBase s m delta + idx))
    overshootMass
    hsample hvalid hsupport
    (by
      intro idx _hidx
      exact relativeHorizontalEvent_fintypeVerticalFiberCover)
    hpositive
    hfiber
    hsum

/--
Restricted target-fiber package using actual finite vertical support and a
first-passage certificate to provide positive overshoot.

This removes the positive-support premise from
`restrictedTargetFiberInputs_of_positiveOvershootFintypeVerticalSupportBounds`
only by replacing it with the source-shaped first-passage certificate on each
horizontal marginal sample.  Endpoint-fiber estimates and vertical summation
remain explicit inputs.
-/
theorem restrictedTargetFiberInputs_of_firstPassagePositiveOvershootFintypeVerticalSupportBounds
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta : ℝ}
    {validSource : Set Ωsrc}
    (overshootMass : ℕ → ℤ → ℝ)
    (hsample : μ = ν.map sampleOf)
    (hvalid :
      sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource)
    (hsupport :
      ∀ η, η ∈ validSource →
        sampleOf η ∈ centeredHighTailEvent start K pre s m →
          prefixIncrement start K pre (sampleOf η) <
            centeredHighTailBinBase s m delta + N)
    (hfirst :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ω,
          ω ∈ relativeHorizontalEvent start K pre
              (centeredHighTailBinBase s m delta + idx) →
            TaoSection7Lemma710.VerticalFirstPassagePrefix
              (start ω) s (K ω) (pre ω))
    (hfiber :
      ∀ idx, idx ∈ Finset.range N →
        ∀ ell,
          ell ∈ relativeHorizontalVerticalSupport start K pre
            (centeredHighTailBinBase s m delta + idx) →
          0 < relativeVerticalOvershoot s ell →
            pmfProb μ
                (relativeEndpointFiberEvent start K pre
                  (centeredHighTailBinBase s m delta + idx) ell) ≤
              overshootMass idx (relativeVerticalOvershoot s ell))
    (hsum :
      ∀ idx, idx ∈ Finset.range N →
        (relativeHorizontalVerticalSupport start K pre
            (centeredHighTailBinBase s m delta + idx)).sum
            (fun ell => overshootMass idx (relativeVerticalOvershoot s ell)) ≤
          exactKernelTailSummand a b K0 V delta s m idx) :
    RestrictedExactKernelCanonicalBinTargetFiberInputs
      ν μ sampleOf start K pre s m N a b K0 V delta validSource
        (fun idx =>
          relativeHorizontalEvent start K pre
            (centeredHighTailBinBase s m delta + idx)) :=
  restrictedTargetFiberInputs_of_positiveOvershootFintypeVerticalSupportBounds
    (ν := ν) (sampleOf := sampleOf) (μ := μ)
    (start := start) (K := K) (pre := pre)
    (s := s) (m := m) (N := N)
    (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
    (validSource := validSource)
    overshootMass
    hsample hvalid hsupport
    (by
      intro idx hidx
      exact
        relativeHorizontalVerticalSupport_positiveOvershoot_of_verticalFirstPassage
          (start := start) (K := K) (pre := pre)
          (s := s)
          (r := centeredHighTailBinBase s m delta + idx)
          (hfirst idx hidx))
    hfiber
    hsum

end TaoSection7Lemma77

end

end Tao
end Erdos1135
