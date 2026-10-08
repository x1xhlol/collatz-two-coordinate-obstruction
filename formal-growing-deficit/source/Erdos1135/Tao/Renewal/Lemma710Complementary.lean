import Erdos1135.Tao.Renewal.Lemma710EprimeProbability
import Erdos1135.Tao.Renewal.Lemma710KernelWindow

/-!
# Lemma 7.10 Complementary Outside-`E'` Probability Socket

This module records the route interface for the complementary Lemma 7.10
estimate `(7.62)`.

It separates three stages: an outside-`E'` event cover to finite `Sigma`
centers, the one-center `(7.48)` kernel summation over those centers, and the
final scale comparison to the displayed `A^2 * (1+p) / s'`-type budget.  It
does not prove the outside-`E'` geometry, the one-center kernel law, Gaussian
local averages, or the scale absorptions.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma710

def Lemma710EndpointNearCenterEvent
    {Ω : Type*}
    (endpoint : Ω → TaoSection7Point) (R : ℝ)
    (c : TaoSection7Point) : Set Ω :=
  {ω | (endpoint ω).distSq c ≤ R ^ 2}

/--
Restricted one-center event for the complementary outside-`E'` route.

This names the domain `largeEvent ∩ endpointNearCenter`.  It is useful when
sample/source data are only available after the outside-`E'` large-event
hypothesis, while the broad endpoint-near-center one-center estimate is still
kept separate.
-/
def Lemma710LargeEndpointNearCenterEvent
    {Ω : Type*}
    (endpoint : Ω → TaoSection7Point) (largeEvent : Set Ω) (R : ℝ)
    (c : TaoSection7Point) : Set Ω :=
  largeEvent ∩ Lemma710EndpointNearCenterEvent endpoint R c

theorem lemma710LargeEndpointNearCenterEvent_subset_endpointNearCenter
    {Ω : Type*}
    {endpoint : Ω → TaoSection7Point} {largeEvent : Set Ω} {R : ℝ}
    (c : TaoSection7Point) :
    Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R c ⊆
      Lemma710EndpointNearCenterEvent endpoint R c := by
  intro ω hω
  exact hω.2

theorem oneCenterJKernelBound_largeEndpointNearCenter_of_endpointNearCenter
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point} {largeEvent : Set Ω} {R : ℝ}
    {kernel : ℤ → ℝ} {L : ℝ}
    (h :
      OneCenterJKernelBound μ C
        (Lemma710EndpointNearCenterEvent endpoint R) kernel L) :
    OneCenterJKernelBound μ C
      (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R) kernel L :=
  oneCenterJKernelBound_mono_event (by
    intro c _hc
    exact lemma710LargeEndpointNearCenterEvent_subset_endpointNearCenter c) h

theorem pmfProb_le_finset_sum_of_subset_exists
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (μ : PMF Ω) (C : Finset ι) (event : ι → Set Ω)
    (largeEvent : Set Ω)
    (hcover :
      ∀ ω, ω ∈ largeEvent → ∃ c, c ∈ C ∧ ω ∈ event c) :
    pmfProb μ largeEvent ≤ C.sum fun c => pmfProb μ (event c) :=
  Erdos1135.Tao.pmfProb_le_finset_sum_of_subset_exists
    μ C event largeEvent hcover

/--
Event-to-geometry cover for the complementary outside-`E'` estimate.

The cover records both the finite center-event cover used by the probability
union bound and the `NearSigma` geometry that should be supplied by the
outside-`E'` endpoint controls `(7.63)/(7.64)` and lower-tip contradiction.
-/
structure Lemma710OutsideEprimeNearSigmaCover
    {Ω : Type*} [Fintype Ω]
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin Kgeo Bgeo R : ℝ}
    (C : Finset TaoSection7Point)
    (endpoint : Ω → TaoSection7Point)
    (largeEvent : Set Ω)
    (oneCenterEvent : TaoSection7Point → Set Ω) : Prop where
  center_mem_sigma :
    ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo
  cover :
    ∀ ω, ω ∈ largeEvent →
      ∃ c, c ∈ C ∧
        NearSigma R (Sigma family old sMin Kgeo Bgeo) (endpoint ω) ∧
          ω ∈ oneCenterEvent c

theorem lemma710OutsideEprimeNearSigmaCover_restrict_largeEvent
    {Ω : Type*} [Fintype Ω]
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin Kgeo Bgeo R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {oneCenterEvent : TaoSection7Point → Set Ω}
    (h :
      Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
        (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
        C endpoint largeEvent oneCenterEvent) :
    Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent (fun c => largeEvent ∩ oneCenterEvent c) where
  center_mem_sigma := h.center_mem_sigma
  cover := by
    intro ω hω
    rcases h.cover ω hω with ⟨c, hc, hnear, hevent⟩
    exact ⟨c, hc, hnear, ⟨hω, hevent⟩⟩

theorem lemma710OutsideEprimeNearSigmaCover_of_sourceHitData
    {Ω : Type*} [Fintype Ω]
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    (hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (hpoint :
      ∀ ω, ω ∈ largeEvent →
        ∃ new : TaoSection7Triangle,
          Lemma710OutsideEprimeSourceHitData family old new (endpoint ω)
            sMin gap Kgeo Bgeo J R ∧
            anchor old new ∈ C) :
    Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent (Lemma710EndpointNearCenterEvent endpoint R) where
  center_mem_sigma := hC
  cover := by
    intro ω hω
    rcases hpoint ω hω with ⟨new, hdata, hCnew⟩
    rcases lemma710_outsideEprimeSourceHitData_to_center_distSq hdata with
      ⟨c, hc_triangle, hdist⟩
    have hc_mem : c.point ∈ C := by
      simpa [Center.point, hc_triangle] using hCnew
    exact
      ⟨c.point, hc_mem, nearSigma_of_near_anchor c hdist, hdist⟩

/--
Finite center set generated by the selected outside-`E'` source-hit samples.

This is the first finite-`Sigma` producer surface: the finite set is not an
input, but the per-sample selected triangle/source-hit data still is.
-/
noncomputable def lemma710OutsideEprimeSampleAnchorFinset
    {Ω : Type*} [Fintype Ω]
    (largeEvent : Set Ω) [DecidablePred (fun ω => ω ∈ largeEvent)]
    (old : TaoSection7Triangle)
    (newOf : ∀ ω, ω ∈ largeEvent → TaoSection7Triangle) :
    Finset TaoSection7Point :=
  Finset.univ.image fun x : {ω // ω ∈ largeEvent} =>
    anchor old (newOf x.1 x.2)

/--
Finite-`Sigma` cover from per-sample source-hit witnesses.

This constructs the finite center set as the image of selected anchors over
the finite outside event.  It still assumes the pointwise source-hit data; it
does not produce source cuts, `¬E'`, current-scale estimates, or analytic
probability bounds.
-/
theorem lemma710OutsideEprimeNearSigmaCover_of_sampleSourceHitData_finset
    {Ω : Type*} [Fintype Ω]
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    [DecidablePred (fun ω => ω ∈ largeEvent)]
    (newOf : ∀ ω, ω ∈ largeEvent → TaoSection7Triangle)
    (hdata :
      ∀ ω (hω : ω ∈ largeEvent),
        Lemma710OutsideEprimeSourceHitData family old (newOf ω hω)
          (endpoint ω) sMin gap Kgeo Bgeo J R) :
    Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      (lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf)
      endpoint largeEvent (Lemma710EndpointNearCenterEvent endpoint R) := by
  classical
  refine
    lemma710OutsideEprimeNearSigmaCover_of_sourceHitData
      (family := family) (old := old) (sMin := sMin) (gap := gap)
      (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R) ?hC ?hpoint
  · intro c hc
    rcases Finset.mem_image.mp hc with ⟨x, _hx, rfl⟩
    rcases lemma710_outsideEprimeSourceHitData_to_center_distSq
        (hdata x.1 x.2) with
      ⟨center, hcenter, _hdist⟩
    simpa [Center.point, hcenter] using center_mem_sigma center
  · intro ω hω
    refine ⟨newOf ω hω, hdata ω hω, ?_⟩
    rw [lemma710OutsideEprimeSampleAnchorFinset]
    exact Finset.mem_image.mpr ⟨⟨ω, hω⟩, Finset.mem_univ _, rfl⟩

/--
Current-scale sample producer for the outside-`E'` `NearSigma` cover.

This composes the per-sample source-hit bridge with the neutral cover
constructor.  The theorem still exposes the sample-to-source-cut data,
endpoint identification, finite center membership, and scale/radius budgets
as hypotheses; it is not the one-center `(7.48)` estimate or the full
complementary bound `(7.62)`.
-/
theorem lemma710OutsideEprimeNearSigmaCover_of_currentScaleSamples
    {Ω : Type*} [Fintype Ω]
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {full : Ω → List TaoSection7RenewalPoint}
    {item : Ω → ℕ × List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (hcut :
      ∀ ω,
        Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
          firstBlock sourceSuffixes old q verticalGap start p
          (full ω) (item ω))
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
    (hlarge :
      ∀ ω, ω ∈ largeEvent →
        taoSection7Case3LargeTriangleEvent pointAt family
          ((hcut ω).first + p) sMin)
    (hendpoint :
      ∀ ω, ω ∈ largeEvent →
        endpoint ω = pointAt ((hcut ω).first + p))
    (hnotE :
      ∀ ω, ω ∈ largeEvent →
        ¬ EprimeSourceEvent start old horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold (full ω))
    (hcenter : horizontalCenter = (pointAt q).jReal + S / 4)
    (hV : verticalSourceThreshold ≤ Lerr)
    (hJ : horizontalSourceThreshold ≤ Jerr)
    (hgap0 : 0 ≤ gap)
    (hCL_nonneg : 0 ≤ CL)
    (hCJS_nonneg : 0 ≤ CJS)
    (hJscale : Jerr ≤ CJS * S ^ (3 / 5 : ℝ))
    (hJabsorb :
      CJS * ((Real.log 9 / Real.log 2) * M) ^ (3 / 5 : ℝ) ≤
        CJm * M ^ (3 / 5 : ℝ))
    (hLscale : Lerr ≤ CL * B)
    (hBscale : B ≤ CB * M ^ (3 / 5 : ℝ))
    (habsorb :
      CJm * M ^ (3 / 5 : ℝ) +
          (Real.log 2 / Real.log 9) * (CL * CB * M ^ (3 / 5 : ℝ)) + 1 ≤
        (M / (Real.log M)^2) *
          (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)))
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hold : old ∈ family)
    (hne :
      ∀ new : TaoSection7Triangle, new ∈ family → sMin ≤ new.size →
        new ≠ old)
    (hanchor :
      ∀ new : TaoSection7Triangle, new ∈ family → sMin ≤ new.size →
        anchor old new ∈ C)
    (hsourceJ : (Real.log 2 / Real.log 9) * (Kgeo * Bgeo + Kgeo * Bgeo) ≤ J)
    (hradius : J ^ 2 + (Kgeo * Bgeo) ^ 2 ≤ R ^ 2)
    (hgapKB : gap ≤ Kgeo * Bgeo)
    (hLerrKB : Lerr ≤ Kgeo * Bgeo) :
    Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent (Lemma710EndpointNearCenterEvent endpoint R) :=
  lemma710OutsideEprimeNearSigmaCover_of_sourceHitData hC (by
    intro ω hω
    exact
      lemma710OutsideEprimeSourceHitExists_of_currentScaleSample
        (hcut ω) hpoint_source hbase hscale hω (fun hω' => hlarge ω hω')
        (hendpoint ω hω) (hnotE ω hω) hcenter hV hJ hgap0
        hCL_nonneg hCJS_nonneg hJscale hJabsorb hLscale hBscale habsorb
        hpair hold hne hanchor hsourceJ hradius hgapKB hLerrKB)

/--
Sample-input contract form of the current-scale outside-`E'` cover.

This is a lighter consumer of the same cover constructor: all per-sample
source realization fields are bundled in
`Lemma710OutsideEprimeCurrentScaleSampleInputs`.  It still assumes those
records as input and therefore does not construct the finite PMF sample
producer, the one-center `(7.48)` estimate, or the full `(7.62)` bound.
-/
theorem lemma710OutsideEprimeNearSigmaCover_of_currentScaleSampleInputs
    {Ω : Type*} [Fintype Ω]
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    (hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
          largeEvent ω sMin gap Kgeo Bgeo J R) :
    Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent (Lemma710EndpointNearCenterEvent endpoint R) :=
  lemma710OutsideEprimeNearSigmaCover_of_sourceHitData hC (by
    intro ω hω
    exact lemma710OutsideEprimeSourceHitExists_of_currentScaleSampleInputs
      hω (hinputs ω hω))

/--
The stopped-cylinder mass used by the `(7.61)` post-`k` mass-link interface
is definitionally the same stopped-prefix/tail sum as the one-center
post-stopped mass used by the `(7.62)` kernel route.

This does not produce the event-identification inequality; it only prevents a
future source-law proof from having to bridge two names for the same cylinder
sum.
-/
theorem postStoppedOneCenterMass_eq_lemma710PostKStoppedCylinderMass
    {p : ℕ}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {EndpointNearCenter :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel EndpointNearCenter] :
    postStoppedOneCenterMass p S EndpointNearCenter =
      lemma710PostKStoppedCylinderMass p S EndpointNearCenter := by
  simp [postStoppedOneCenterMass, lemma710PostKStoppedCylinderMass]

theorem lemma710_largeTriangleOutsideEprime_subset_nearSigma
    {Ω : Type*} [Fintype Ω]
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin Kgeo Bgeo R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {oneCenterEvent : TaoSection7Point → Set Ω}
    (hcover :
      Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
        (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
        C endpoint largeEvent oneCenterEvent) :
    ∀ ω, ω ∈ largeEvent → ∃ c, c ∈ C ∧ ω ∈ oneCenterEvent c := by
  intro ω hω
  rcases hcover.cover ω hω with ⟨c, hc, _hnear, hωc⟩
  exact ⟨c, hc, hωc⟩

/--
Inputs for the complementary Lemma 7.10 estimate `(7.62)`.

The one-center field is the future `(7.48)` kernel/convolution input.  The
post-stopped one-center support socket is not a substitute for this field.
-/
structure Lemma710Complementary762Inputs
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin Kgeo Bgeo R : ℝ}
    (C : Finset TaoSection7Point)
    (endpoint : Ω → TaoSection7Point)
    (largeEvent : Set Ω)
    (oneCenterEvent : TaoSection7Point → Set Ω)
    (avgWindow : TaoSection7Point → Finset ℤ)
    (kernel : ℤ → ℝ)
    (L lambda M C0 A2pDivSPrime : ℝ) : Prop where
  outside_cover :
    Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent oneCenterEvent
  kernel_nonnegative : TaoSection7KernelNonnegative kernel
  L_nonneg : 0 ≤ L
  lambda_nonneg : 0 ≤ lambda
  one_center_748 : OneCenterJKernelBound μ C oneCenterEvent kernel L
  local_average :
    TaoSection7LocalAverageAtCenters C
      (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel lambda
  average_window_total :
    TaoSection7AverageWindowTotalBound C avgWindow kernel M
  scale_comparison : L * lambda * M ≤ C0 * A2pDivSPrime

/--
Producer-facing constructor for the complementary `(7.62)` input record.

This packages the finite sample-anchor cover together with the stopped-tail
one-center wrapper.  It still exposes the hard producers explicitly: the
per-sample source-hit data, event identification with the stopped-tail mass,
the stopped-tail law, near-window/kernel comparisons, local-average/window
total bounds, and the final scale comparison.
-/
theorem lemma710Complementary762Inputs_of_sampleSourceHitData_stoppedTail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    [DecidablePred (fun ω => ω ∈ largeEvent)]
    {newOf : ∀ ω, ω ∈ largeEvent → TaoSection7Triangle}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {nearWindow avgWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [hdec : ∀ c, DecidableRel (EndpointNearCenter c)]
    {bound : TaoSection7Point → ℝ}
    {L lambda M C0 A2pDivSPrime : ℝ}
    (hdata :
      ∀ ω (hω : ω ∈ largeEvent),
        Lemma710OutsideEprimeSourceHitData family old (newOf ω hω)
          (endpoint ω) sMin gap Kgeo Bgeo J R)
    (hprefixes : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hL : 0 ≤ L)
    (hlambda : 0 ≤ lambda)
    (hbound_nonneg :
      ∀ c ∈ lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf,
        0 ≤ bound c)
    (htail :
      ∀ c ∈ lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf,
        TaoSection7StoppedHoldTailBound p (EndpointNearCenter c) (bound c))
    (hidentify :
      ∀ c ∈ lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf,
        pmfProb μ (Lemma710EndpointNearCenterEvent endpoint R c) ≤
          postStoppedOneCenterMass p S (EndpointNearCenter c))
    (hbound_near :
      ∀ c ∈ lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf,
        bound c ≤ (nearWindow c).sum fun x => kernel x)
    (hnear :
      ∀ c ∈ lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf,
        (nearWindow c).sum (fun x => kernel x) ≤
          L * kernel (((c.j : ℕ) : ℤ)))
    (hlocal :
      TaoSection7LocalAverageAtCenters
        (lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf)
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel
        lambda)
    (htotal :
      TaoSection7AverageWindowTotalBound
        (lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf)
        avgWindow kernel M)
    (hscale : L * lambda * M ≤ C0 * A2pDivSPrime) :
    Lemma710Complementary762Inputs μ (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      (lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf)
      endpoint largeEvent (Lemma710EndpointNearCenterEvent endpoint R)
      avgWindow kernel L lambda M C0 A2pDivSPrime where
  outside_cover :=
    lemma710OutsideEprimeNearSigmaCover_of_sampleSourceHitData_finset
      (family := family) (old := old) (sMin := sMin) (gap := gap)
      (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
      (endpoint := endpoint) (largeEvent := largeEvent)
      (newOf := newOf) hdata
  kernel_nonnegative := hkernel
  L_nonneg := hL
  lambda_nonneg := hlambda
  one_center_748 :=
    oneCenterJKernelBound_of_stoppedTailBound_identification
      (μ := μ) (p := p)
      (C := lemma710OutsideEprimeSampleAnchorFinset largeEvent old newOf)
      (event := Lemma710EndpointNearCenterEvent endpoint R)
      (PrefixOK := PrefixOK) (S := S) (nearWindow := nearWindow)
      (kernel := kernel) (EndpointNearCenter := EndpointNearCenter)
      (bound := bound) (L := L) hprefixes hkernel hbound_nonneg htail
      hidentify hbound_near hnear
  local_average := hlocal
  average_window_total := htotal
  scale_comparison := hscale

/--
Deterministic source-cylinder cover for the restricted one-center event from
current-scale sample inputs.

This is the `hcover` shape consumed by
`oneCenterEventIdentification_of_sourceCylinderMassControl` for
`Lemma710LargeEndpointNearCenterEvent`.  It uses the checked endpoint-to-post
`k` event map, but still assumes the current-scale sample input and the
sample-to-source bookkeeping for the selected stopped-prefix family.  It is
not sample production, source-law mass control, event identification, `(7.62)`,
or Lemma 7.10.
-/
theorem lemma710LargeEndpointNearCenter_sourceCylinderCover_of_currentScaleSampleInputs
    {Ω : Type*}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint} {p : ℕ}
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          h.item ∈ S ∧ fullOf ω = h.full ∧ h.start = start ∧ h.p = p) :
    ∀ c ∈ C, ∀ ω,
      ω ∈ Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R c →
        ∃ item, item ∈ S ∧
          ∃ tail : List TaoSection7RenewalPoint,
            fullOf ω = item.2 ++ tail ∧
              Lemma710PostKEndpointNearCenter start p R c item.2 tail := by
  intro c _hc ω hω
  rcases hinputs ω hω.1 with ⟨h, hitem_mem, hfullOf, hstart, hp⟩
  rcases
    lemma710PostKEndpointNearCenter_of_currentScaleSampleInputs_endpointNearCenter
      h hω.2 with
    ⟨tail, hfull, hpost⟩
  refine ⟨h.item, hitem_mem, tail, ?_, ?_⟩
  · calc
      fullOf ω = h.full := hfullOf
      _ = h.item.2 ++ tail := hfull
  · simpa [hstart, hp] using hpost

/--
Concrete random-`k` support specialization of the restricted source-cylinder
cover.

When the current-scale sample inputs share a common source start, vertical gap,
source suffix list, and post-`k` horizon, membership in the concrete
`randomKVerticalFirstPassagePrefixFinset` is derived from the sample input's
source-cut ledger instead of being supplied as a separate hypothesis.
-/
theorem lemma710LargeEndpointNearCenter_sourceCylinderCover_of_currentScaleSampleInputs_verticalFirstPassageFinset
    {Ω : Type*}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint} {p verticalGap : ℕ}
    {sourceSuffixes : List (List ℕ)}
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          fullOf ω = h.full ∧ h.start = start ∧ h.p = p ∧
            h.verticalGap = verticalGap ∧ h.sourceSuffixes = sourceSuffixes) :
    ∀ c ∈ C, ∀ ω,
      ω ∈ Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R c →
        ∃ item,
          item ∈ randomKVerticalFirstPassagePrefixFinset start verticalGap
            sourceSuffixes ∧
          ∃ tail : List TaoSection7RenewalPoint,
            fullOf ω = item.2 ++ tail ∧
              Lemma710PostKEndpointNearCenter start p R c item.2 tail :=
  lemma710LargeEndpointNearCenter_sourceCylinderCover_of_currentScaleSampleInputs
    (family := family) (old := old) (sMin := sMin) (gap := gap)
    (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R) (C := C)
    (endpoint := endpoint) (largeEvent := largeEvent)
    (S := randomKVerticalFirstPassagePrefixFinset start verticalGap
      sourceSuffixes)
    (fullOf := fullOf) (start := start) (p := p) (by
      intro ω hω
      rcases hinputs ω hω with
        ⟨h, hfullOf, hstart, hp, hverticalGap, hsourceSuffixes⟩
      rcases
          lemma710OutsideEprimeCurrentScaleSampleInputs_to_sourceEndpointCenterCut
            hω h with
        ⟨_c, _hc, _hnear, hitem_mem, _hcut⟩
      have hitem_mem_common :
          h.item ∈
            randomKVerticalFirstPassagePrefixFinset start verticalGap
              sourceSuffixes := by
        simpa [hstart, hverticalGap, hsourceSuffixes] using hitem_mem
      exact ⟨h, hitem_mem_common, hfullOf, hstart, hp⟩)

/--
Source-cylinder mass control identifies the restricted one-center event used
by the current-scale complementary route with the canonical post-`k` stopped
tail cylinder.

This removes the free `hidentify` premise for the canonical
`Lemma710PostKEndpointNearCenter` tail predicate.  It still assumes the
source-law mass-control record and the per-sample source-cut bookkeeping; it
does not prove the source law, the sample producer, `(7.48)`, `(7.62)`, or
Lemma 7.10.
-/
theorem lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint}
    [∀ c, DecidableRel (Lemma710PostKEndpointNearCenter start p R c)]
    (hmass :
      Lemma710OneCenterSourceCylinderMassControl μ p S fullOf
        (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
        (fun c => Lemma710PostKEndpointNearCenter start p R c))
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          h.item ∈ S ∧ fullOf ω = h.full ∧ h.start = start ∧ h.p = p) :
    ∀ c ∈ C,
      pmfProb μ (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R c) ≤
        postStoppedOneCenterMass p S
          (Lemma710PostKEndpointNearCenter start p R c) :=
  oneCenterEventIdentification_of_sourceCylinderMassControl
    (μ := μ) (p := p) (C := C) (S := S) (fullOf := fullOf)
    (event := Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
    (EndpointNearCenter :=
      fun c => Lemma710PostKEndpointNearCenter start p R c)
    hmass
    (lemma710LargeEndpointNearCenter_sourceCylinderCover_of_currentScaleSampleInputs
      (family := family) (old := old) (sMin := sMin) (gap := gap)
      (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R) (C := C)
      (endpoint := endpoint) (largeEvent := largeEvent) (S := S)
      (fullOf := fullOf) (start := start) (p := p) hinputs)

/--
Restricted one-center event identification over the concrete vertical
first-passage prefix family.

This specializes
`lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs`
to `randomKVerticalFirstPassagePrefixFinset`, deriving selected-item
membership from each current-scale sample input's source-cut ledger.  The
finite-PMF source-law mass-control record remains an explicit input.
-/
theorem lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs_verticalFirstPassageFinset
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p verticalGap : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint}
    {sourceSuffixes : List (List ℕ)}
    [∀ c, DecidableRel (Lemma710PostKEndpointNearCenter start p R c)]
    (hmass :
      Lemma710OneCenterSourceCylinderMassControl μ p
        (randomKVerticalFirstPassagePrefixFinset start verticalGap
          sourceSuffixes)
        fullOf (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
        (fun c => Lemma710PostKEndpointNearCenter start p R c))
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          fullOf ω = h.full ∧ h.start = start ∧ h.p = p ∧
            h.verticalGap = verticalGap ∧ h.sourceSuffixes = sourceSuffixes) :
    ∀ c ∈ C,
      pmfProb μ (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R c) ≤
        postStoppedOneCenterMass p
          (randomKVerticalFirstPassagePrefixFinset start verticalGap
            sourceSuffixes)
          (Lemma710PostKEndpointNearCenter start p R c) :=
  oneCenterEventIdentification_of_sourceCylinderMassControl
    (μ := μ) (p := p) (C := C)
    (S := randomKVerticalFirstPassagePrefixFinset start verticalGap
      sourceSuffixes)
    (fullOf := fullOf)
    (event := Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
    (EndpointNearCenter :=
      fun c => Lemma710PostKEndpointNearCenter start p R c)
    hmass
    (lemma710LargeEndpointNearCenter_sourceCylinderCover_of_currentScaleSampleInputs_verticalFirstPassageFinset
      (family := family) (old := old) (sMin := sMin) (gap := gap)
      (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R) (C := C)
      (endpoint := endpoint) (largeEvent := largeEvent) (fullOf := fullOf)
      (start := start) (p := p) (verticalGap := verticalGap)
      (sourceSuffixes := sourceSuffixes) hinputs)

/--
Restricted one-center event identification from the lower stopped-cylinder
source-law socket.

This is the same canonical post-`k` identification as
`lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs`,
but it consumes the concrete stopped-cylinder source-law event bound instead
of the higher-level `Lemma710OneCenterSourceCylinderMassControl` record.
-/
theorem lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs_stoppedCylinderSourceLaw
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint}
    [∀ c, DecidableRel (Lemma710PostKEndpointNearCenter start p R c)]
    (hsource :
      Lemma710OneCenterStoppedCylinderSourceLaw μ p S fullOf
        (fun c => Lemma710PostKEndpointNearCenter start p R c))
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          h.item ∈ S ∧ fullOf ω = h.full ∧ h.start = start ∧ h.p = p) :
    ∀ c ∈ C,
      pmfProb μ (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R c) ≤
        postStoppedOneCenterMass p S
          (Lemma710PostKEndpointNearCenter start p R c) :=
  lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs
    (μ := μ) (p := p) (family := family) (old := old) (sMin := sMin)
    (gap := gap) (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
    (C := C) (endpoint := endpoint) (largeEvent := largeEvent) (S := S)
    (fullOf := fullOf) (start := start)
    (lemma710OneCenterSourceCylinderMassControl_of_stoppedCylinderSourceLaw
      hsource)
    hinputs

/--
Concrete vertical-first-passage support version of the stopped-cylinder
source-law identification bridge.
-/
theorem lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs_verticalFirstPassageStoppedCylinderSourceLaw
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p verticalGap : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint}
    {sourceSuffixes : List (List ℕ)}
    [∀ c, DecidableRel (Lemma710PostKEndpointNearCenter start p R c)]
    (hsource :
      Lemma710OneCenterStoppedCylinderSourceLaw μ p
        (randomKVerticalFirstPassagePrefixFinset start verticalGap
          sourceSuffixes)
        fullOf (fun c => Lemma710PostKEndpointNearCenter start p R c))
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          fullOf ω = h.full ∧ h.start = start ∧ h.p = p ∧
            h.verticalGap = verticalGap ∧ h.sourceSuffixes = sourceSuffixes) :
    ∀ c ∈ C,
      pmfProb μ (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R c) ≤
        postStoppedOneCenterMass p
          (randomKVerticalFirstPassagePrefixFinset start verticalGap
            sourceSuffixes)
          (Lemma710PostKEndpointNearCenter start p R c) :=
  lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs_verticalFirstPassageFinset
    (μ := μ) (p := p) (verticalGap := verticalGap) (family := family)
    (old := old) (sMin := sMin) (gap := gap) (Kgeo := Kgeo)
    (Bgeo := Bgeo) (J := J) (R := R) (C := C) (endpoint := endpoint)
    (largeEvent := largeEvent) (fullOf := fullOf) (start := start)
    (sourceSuffixes := sourceSuffixes)
    (lemma710OneCenterSourceCylinderMassControl_of_stoppedCylinderSourceLaw
      hsource)
    hinputs

/--
Consumer-facing constructor for `(7.62)` from bundled current-scale
outside-`E'` sample inputs.

This is only a packaging bridge: it consumes per-sample
`Lemma710OutsideEprimeCurrentScaleSampleInputs`, the stopped-tail one-center
bound, restricted event identification for `largeEvent ∩ endpointNearCenter`,
local-average/window-total estimates, and the final scale comparison.  It does
not produce the sample-input records, source-law mass control, event
identification, one-center `(7.48)`, or the complementary estimate itself.
-/
theorem lemma710Complementary762Inputs_of_currentScaleSampleInputs_nonempty_stoppedTail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {nearWindow avgWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [hdec : ∀ c, DecidableRel (EndpointNearCenter c)]
    {bound : TaoSection7Point → ℝ}
    {L lambda M C0 A2pDivSPrime : ℝ}
    (hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        Nonempty
          (Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R))
    (hprefixes : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hL : 0 ≤ L)
    (hlambda : 0 ≤ lambda)
    (hbound_nonneg : ∀ c ∈ C, 0 ≤ bound c)
    (htail :
      ∀ c ∈ C,
        TaoSection7StoppedHoldTailBound p (EndpointNearCenter c) (bound c))
    (hidentify :
      ∀ c ∈ C,
        pmfProb μ (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R c) ≤
          postStoppedOneCenterMass p S (EndpointNearCenter c))
    (hbound_near :
      ∀ c ∈ C, bound c ≤ (nearWindow c).sum fun x => kernel x)
    (hnear :
      ∀ c ∈ C,
        (nearWindow c).sum (fun x => kernel x) ≤
          L * kernel (((c.j : ℕ) : ℤ)))
    (hlocal :
      TaoSection7LocalAverageAtCenters C
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel
        lambda)
    (htotal : TaoSection7AverageWindowTotalBound C avgWindow kernel M)
    (hscale : L * lambda * M ≤ C0 * A2pDivSPrime) :
    Lemma710Complementary762Inputs μ (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent
      (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
      avgWindow kernel L lambda M C0 A2pDivSPrime := by
  classical
  let hcoverEndpoint :
      Lemma710OutsideEprimeNearSigmaCover (family := family) (old := old)
        (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
        C endpoint largeEvent (Lemma710EndpointNearCenterEvent endpoint R) :=
    lemma710OutsideEprimeNearSigmaCover_of_currentScaleSampleInputs hC
      (fun ω hω => Classical.choice (hinputs ω hω))
  refine
    { outside_cover := ?_
      kernel_nonnegative := hkernel
      L_nonneg := hL
      lambda_nonneg := hlambda
      one_center_748 := ?_
      local_average := hlocal
      average_window_total := htotal
      scale_comparison := hscale }
  · exact lemma710OutsideEprimeNearSigmaCover_restrict_largeEvent hcoverEndpoint
  · exact
      oneCenterJKernelBound_of_stoppedTailBound_identification
        (μ := μ) (p := p) (C := C)
        (event := Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
        (PrefixOK := PrefixOK) (S := S) (nearWindow := nearWindow)
        (kernel := kernel) (EndpointNearCenter := EndpointNearCenter)
        (bound := bound) (L := L)
        hprefixes hkernel hbound_nonneg htail hidentify hbound_near hnear

/--
Producer-facing constructor for `(7.62)` from current-scale sample inputs and
one-center source-cylinder mass control.

Compared with
`lemma710Complementary762Inputs_of_currentScaleSampleInputs_nonempty_stoppedTail`,
this version no longer asks for the event-identification inequality as a free
premise.  The source-law mass-control record and the sample-to-source-cut
membership/bookkeeping remain explicit, and the one-center stopped-tail,
near-window, local-average, window-total, and scale-comparison estimates are
still open inputs.
-/
theorem lemma710Complementary762Inputs_of_currentScaleSampleInputs_sourceMassControl_stoppedTail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint}
    {nearWindow avgWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {bound : TaoSection7Point → ℝ}
    {L lambda M C0 A2pDivSPrime : ℝ}
    [∀ c, DecidableRel (Lemma710PostKEndpointNearCenter start p R c)]
    (hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          h.item ∈ S ∧ fullOf ω = h.full ∧ h.start = start ∧ h.p = p)
    (hmass :
      Lemma710OneCenterSourceCylinderMassControl μ p S fullOf
        (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
        (fun c => Lemma710PostKEndpointNearCenter start p R c))
    (hprefixes : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hL : 0 ≤ L)
    (hlambda : 0 ≤ lambda)
    (hbound_nonneg : ∀ c ∈ C, 0 ≤ bound c)
    (htail :
      ∀ c ∈ C,
        TaoSection7StoppedHoldTailBound p
          (Lemma710PostKEndpointNearCenter start p R c) (bound c))
    (hbound_near :
      ∀ c ∈ C, bound c ≤ (nearWindow c).sum fun x => kernel x)
    (hnear :
      ∀ c ∈ C,
        (nearWindow c).sum (fun x => kernel x) ≤
          L * kernel (((c.j : ℕ) : ℤ)))
    (hlocal :
      TaoSection7LocalAverageAtCenters C
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel
        lambda)
    (htotal : TaoSection7AverageWindowTotalBound C avgWindow kernel M)
    (hscale : L * lambda * M ≤ C0 * A2pDivSPrime) :
    Lemma710Complementary762Inputs μ (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent
      (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
      avgWindow kernel L lambda M C0 A2pDivSPrime := by
  refine
    lemma710Complementary762Inputs_of_currentScaleSampleInputs_nonempty_stoppedTail
      (μ := μ) (p := p) (family := family) (old := old)
      (sMin := sMin) (gap := gap) (Kgeo := Kgeo) (Bgeo := Bgeo)
      (J := J) (R := R) (C := C) (endpoint := endpoint)
      (largeEvent := largeEvent) (PrefixOK := PrefixOK) (S := S)
      (nearWindow := nearWindow) (avgWindow := avgWindow) (kernel := kernel)
      (EndpointNearCenter :=
        fun c => Lemma710PostKEndpointNearCenter start p R c)
      (bound := bound) (L := L) (lambda := lambda) (M := M)
      (C0 := C0) (A2pDivSPrime := A2pDivSPrime)
      hC ?hinputs_nonempty hprefixes hkernel hL hlambda hbound_nonneg
      htail ?hidentify hbound_near hnear hlocal htotal hscale
  · intro ω hω
    exact ⟨(hinputs ω hω).choose⟩
  · exact
      lemma710LargeEndpointNearCenter_identification_of_currentScaleSampleInputs
        (μ := μ) (p := p) (family := family) (old := old)
        (sMin := sMin) (gap := gap) (Kgeo := Kgeo) (Bgeo := Bgeo)
        (J := J) (R := R) (C := C) (endpoint := endpoint)
        (largeEvent := largeEvent) (S := S) (fullOf := fullOf)
        (start := start) hmass hinputs

/--
Concrete vertical-first-passage support version of the source-mass-control
constructor for `(7.62)` inputs.

This removes the selected-item membership hypothesis by using each
current-scale sample input's source-cut ledger to place its item in
`randomKVerticalFirstPassagePrefixFinset start verticalGap sourceSuffixes`.
It still assumes source-law mass control, a stopped-prefix family over that
finite support, stopped-tail bounds, near-window/local-average/window-total
estimates, and the final scale comparison.
-/
theorem lemma710Complementary762Inputs_of_currentScaleSampleInputs_verticalFirstPassageSourceMassControl_stoppedTail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p verticalGap : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint}
    {sourceSuffixes : List (List ℕ)}
    {nearWindow avgWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {bound : TaoSection7Point → ℝ}
    {L lambda M C0 A2pDivSPrime : ℝ}
    [∀ c, DecidableRel (Lemma710PostKEndpointNearCenter start p R c)]
    (hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          fullOf ω = h.full ∧ h.start = start ∧ h.p = p ∧
            h.verticalGap = verticalGap ∧ h.sourceSuffixes = sourceSuffixes)
    (hmass :
      Lemma710OneCenterSourceCylinderMassControl μ p
        (randomKVerticalFirstPassagePrefixFinset start verticalGap
          sourceSuffixes)
        fullOf (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
        (fun c => Lemma710PostKEndpointNearCenter start p R c))
    (hprefixes :
      TaoSection7StoppedHoldVariablePrefixFamily PrefixOK
        (randomKVerticalFirstPassagePrefixFinset start verticalGap
          sourceSuffixes))
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hL : 0 ≤ L)
    (hlambda : 0 ≤ lambda)
    (hbound_nonneg : ∀ c ∈ C, 0 ≤ bound c)
    (htail :
      ∀ c ∈ C,
        TaoSection7StoppedHoldTailBound p
          (Lemma710PostKEndpointNearCenter start p R c) (bound c))
    (hbound_near :
      ∀ c ∈ C, bound c ≤ (nearWindow c).sum fun x => kernel x)
    (hnear :
      ∀ c ∈ C,
        (nearWindow c).sum (fun x => kernel x) ≤
          L * kernel (((c.j : ℕ) : ℤ)))
    (hlocal :
      TaoSection7LocalAverageAtCenters C
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel
        lambda)
    (htotal : TaoSection7AverageWindowTotalBound C avgWindow kernel M)
    (hscale : L * lambda * M ≤ C0 * A2pDivSPrime) :
    Lemma710Complementary762Inputs μ (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent
      (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
      avgWindow kernel L lambda M C0 A2pDivSPrime :=
  lemma710Complementary762Inputs_of_currentScaleSampleInputs_sourceMassControl_stoppedTail
    (μ := μ) (p := p) (family := family) (old := old) (sMin := sMin)
    (gap := gap) (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
    (C := C) (endpoint := endpoint) (largeEvent := largeEvent)
    (PrefixOK := PrefixOK)
    (S := randomKVerticalFirstPassagePrefixFinset start verticalGap
      sourceSuffixes)
    (fullOf := fullOf) (start := start) (nearWindow := nearWindow)
    (avgWindow := avgWindow) (kernel := kernel) (bound := bound) (L := L)
    (lambda := lambda) (M := M) (C0 := C0)
    (A2pDivSPrime := A2pDivSPrime) hC
    (by
      intro ω hω
      rcases hinputs ω hω with
        ⟨h, hfullOf, hstart, hp, hverticalGap, hsourceSuffixes⟩
      rcases
          lemma710OutsideEprimeCurrentScaleSampleInputs_to_sourceEndpointCenterCut
            hω h with
        ⟨_c, _hc, _hnear, hitem_mem, _hcut⟩
      have hitem_mem_common :
          h.item ∈
            randomKVerticalFirstPassagePrefixFinset start verticalGap
              sourceSuffixes := by
        simpa [hstart, hverticalGap, hsourceSuffixes] using hitem_mem
      exact ⟨h, hitem_mem_common, hfullOf, hstart, hp⟩)
    hmass hprefixes hkernel hL hlambda hbound_nonneg htail hbound_near
    hnear hlocal htotal hscale

/--
Convenience constructor for `(7.62)` from current-scale sample inputs and the
lower stopped-cylinder source-law socket.

This is the source-law-premise refinement of
`lemma710Complementary762Inputs_of_currentScaleSampleInputs_sourceMassControl_stoppedTail`:
it no longer takes `Lemma710OneCenterSourceCylinderMassControl` as input, but
it still assumes the concrete stopped-cylinder event source-law bound.  It is
not a producer for that bound.
-/
theorem lemma710Complementary762Inputs_of_currentScaleSampleInputs_stoppedCylinderSourceLaw_stoppedTail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint}
    {nearWindow avgWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {bound : TaoSection7Point → ℝ}
    {L lambda M C0 A2pDivSPrime : ℝ}
    [∀ c, DecidableRel (Lemma710PostKEndpointNearCenter start p R c)]
    (hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          h.item ∈ S ∧ fullOf ω = h.full ∧ h.start = start ∧ h.p = p)
    (hsource :
      Lemma710OneCenterStoppedCylinderSourceLaw μ p S fullOf
        (fun c => Lemma710PostKEndpointNearCenter start p R c))
    (hprefixes : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hL : 0 ≤ L)
    (hlambda : 0 ≤ lambda)
    (hbound_nonneg : ∀ c ∈ C, 0 ≤ bound c)
    (htail :
      ∀ c ∈ C,
        TaoSection7StoppedHoldTailBound p
          (Lemma710PostKEndpointNearCenter start p R c) (bound c))
    (hbound_near :
      ∀ c ∈ C, bound c ≤ (nearWindow c).sum fun x => kernel x)
    (hnear :
      ∀ c ∈ C,
        (nearWindow c).sum (fun x => kernel x) ≤
          L * kernel (((c.j : ℕ) : ℤ)))
    (hlocal :
      TaoSection7LocalAverageAtCenters C
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel
        lambda)
    (htotal : TaoSection7AverageWindowTotalBound C avgWindow kernel M)
    (hscale : L * lambda * M ≤ C0 * A2pDivSPrime) :
    Lemma710Complementary762Inputs μ (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent
      (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
      avgWindow kernel L lambda M C0 A2pDivSPrime :=
  lemma710Complementary762Inputs_of_currentScaleSampleInputs_sourceMassControl_stoppedTail
    (μ := μ) (p := p) (family := family) (old := old) (sMin := sMin)
    (gap := gap) (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
    (C := C) (endpoint := endpoint) (largeEvent := largeEvent)
    (PrefixOK := PrefixOK) (S := S) (fullOf := fullOf) (start := start)
    (nearWindow := nearWindow) (avgWindow := avgWindow) (kernel := kernel)
    (bound := bound) (L := L) (lambda := lambda) (M := M) (C0 := C0)
    (A2pDivSPrime := A2pDivSPrime) hC hinputs
    (lemma710OneCenterSourceCylinderMassControl_of_stoppedCylinderSourceLaw
      hsource)
    hprefixes hkernel hL hlambda hbound_nonneg htail hbound_near hnear
    hlocal htotal hscale

/--
Concrete vertical-first-passage support version of the stopped-cylinder
source-law `(7.62)` input constructor.  This consumes, but does not produce,
the stopped-cylinder source-law.
-/
theorem lemma710Complementary762Inputs_of_currentScaleSampleInputs_verticalFirstPassageStoppedCylinderSourceLaw_stoppedTail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p verticalGap : ℕ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {start : TaoSection7RenewalPoint}
    {sourceSuffixes : List (List ℕ)}
    {nearWindow avgWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {bound : TaoSection7Point → ℝ}
    {L lambda M C0 A2pDivSPrime : ℝ}
    [∀ c, DecidableRel (Lemma710PostKEndpointNearCenter start p R c)]
    (hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (hinputs :
      ∀ ω, ω ∈ largeEvent →
        ∃ h :
          Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
            largeEvent ω sMin gap Kgeo Bgeo J R,
          fullOf ω = h.full ∧ h.start = start ∧ h.p = p ∧
            h.verticalGap = verticalGap ∧ h.sourceSuffixes = sourceSuffixes)
    (hsource :
      Lemma710OneCenterStoppedCylinderSourceLaw μ p
        (randomKVerticalFirstPassagePrefixFinset start verticalGap
          sourceSuffixes)
        fullOf (fun c => Lemma710PostKEndpointNearCenter start p R c))
    (hprefixes :
      TaoSection7StoppedHoldVariablePrefixFamily PrefixOK
        (randomKVerticalFirstPassagePrefixFinset start verticalGap
          sourceSuffixes))
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hL : 0 ≤ L)
    (hlambda : 0 ≤ lambda)
    (hbound_nonneg : ∀ c ∈ C, 0 ≤ bound c)
    (htail :
      ∀ c ∈ C,
        TaoSection7StoppedHoldTailBound p
          (Lemma710PostKEndpointNearCenter start p R c) (bound c))
    (hbound_near :
      ∀ c ∈ C, bound c ≤ (nearWindow c).sum fun x => kernel x)
    (hnear :
      ∀ c ∈ C,
        (nearWindow c).sum (fun x => kernel x) ≤
          L * kernel (((c.j : ℕ) : ℤ)))
    (hlocal :
      TaoSection7LocalAverageAtCenters C
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel
        lambda)
    (htotal : TaoSection7AverageWindowTotalBound C avgWindow kernel M)
    (hscale : L * lambda * M ≤ C0 * A2pDivSPrime) :
    Lemma710Complementary762Inputs μ (family := family) (old := old)
      (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
      C endpoint largeEvent
      (Lemma710LargeEndpointNearCenterEvent endpoint largeEvent R)
      avgWindow kernel L lambda M C0 A2pDivSPrime :=
  lemma710Complementary762Inputs_of_currentScaleSampleInputs_verticalFirstPassageSourceMassControl_stoppedTail
    (μ := μ) (p := p) (verticalGap := verticalGap) (family := family)
    (old := old) (sMin := sMin) (gap := gap) (Kgeo := Kgeo)
    (Bgeo := Bgeo) (J := J) (R := R) (C := C) (endpoint := endpoint)
    (largeEvent := largeEvent) (PrefixOK := PrefixOK) (fullOf := fullOf)
    (start := start) (sourceSuffixes := sourceSuffixes)
    (nearWindow := nearWindow) (avgWindow := avgWindow) (kernel := kernel)
    (bound := bound) (L := L) (lambda := lambda) (M := M) (C0 := C0)
    (A2pDivSPrime := A2pDivSPrime) hC hinputs
    (lemma710OneCenterSourceCylinderMassControl_of_stoppedCylinderSourceLaw
      hsource)
    hprefixes hkernel hL hlambda hbound_nonneg htail hbound_near hnear
    hlocal htotal hscale

theorem lemma710_complementary_probability_bound_762
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin Kgeo Bgeo R : ℝ}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω}
    {oneCenterEvent : TaoSection7Point → Set Ω}
    {avgWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {L lambda M C0 A2pDivSPrime : ℝ}
    (h :
      Lemma710Complementary762Inputs μ (family := family) (old := old)
        (sMin := sMin) (Kgeo := Kgeo) (Bgeo := Bgeo) (R := R)
        C endpoint largeEvent oneCenterEvent avgWindow kernel
        L lambda M C0 A2pDivSPrime) :
    pmfProb μ largeEvent ≤ C0 * A2pDivSPrime := by
  have hcover :
      ∀ ω, ω ∈ largeEvent → ∃ c, c ∈ C ∧ ω ∈ oneCenterEvent c :=
    lemma710_largeTriangleOutsideEprime_subset_nearSigma h.outside_cover
  calc
    pmfProb μ largeEvent
        ≤ C.sum fun c => pmfProb μ (oneCenterEvent c) :=
          pmfProb_le_finset_sum_of_subset_exists μ C oneCenterEvent
            largeEvent hcover
    _ ≤ L * lambda * M :=
      oneCenterJKernel_finiteSigmaWindow_sum_le
        (family := family) (old := old) (sMin := sMin) (Kgeo := Kgeo)
        (Bgeo := Bgeo) μ C h.outside_cover.center_mem_sigma
        oneCenterEvent avgWindow kernel h.kernel_nonnegative h.L_nonneg
        h.lambda_nonneg h.one_center_748 h.local_average
        h.average_window_total
    _ ≤ C0 * A2pDivSPrime := h.scale_comparison

end TaoSection7Lemma710

end

end Tao
end Erdos1135
