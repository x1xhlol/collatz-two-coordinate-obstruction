/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma710PostStoppedKernel

/-!
# Lemma 7.10 Exceptional-Event Probability Socket

This module records a narrow probability-budget interface for Tao's Lemma
7.10 exceptional-event estimate `(7.61)`.

The interface keeps `(7.61)` separate from the one-center kernel-window route
for `(7.62)`: the exceptional event is bounded by residual mass, the two
first-passage `(7.48)` marginals, and the two post-`k` Lemma 2.2 tail inputs.
It does not prove Lemma 2.2, Lemma 7.7, `(7.48)`, parameter absorption, or
Lemma 7.10.
-/

namespace Erdos1135SecondScale
namespace Tao

namespace TaoSection7Lemma710

/-- The source-side exceptional event `E'`, as the union of vertical and horizontal alternatives. -/
def EprimeSourceEvent
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ)
    (full : List TaoSection7RenewalPoint) : Prop :=
  EprimeVerticalSourceEvent start old verticalSourceThreshold full ∨
    EprimeHorizontalSourceEvent start horizontalCenter horizontalSourceThreshold full

/--
Outside `E'`, the actual `k+p` source endpoint has only the upper vertical
and horizontal-center estimates.  The lower vertical endpoint estimate is a
separate first-passage/source-cut obligation, not a consequence of `¬ E'`.
-/
theorem lemma710OutsideEprimeKpEndpointUpperJ_of_notEprime
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      S Lerr Jerr : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
    (hcenter : horizontalCenter = (pointAt q).jReal + S / 4)
    (hV : verticalSourceThreshold ≤ Lerr)
    (hJ : horizontalSourceThreshold ≤ Jerr) :
    (pointAt (hcut.first + p)).lReal - (old.cornerL : ℝ) ≤ Lerr ∧
      |(pointAt (hcut.first + p)).jReal -
          ((pointAt q).jReal + S / 4)| ≤ Jerr := by
  have hpoint :
      pointAt (hcut.first + p) =
        (taoSection7RenewalPathPoint start full full.length).toPoint :=
    lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
      hcut hpoint_source
  have hnotV :
      ¬ EprimeVerticalSourceEvent start old verticalSourceThreshold full := by
    intro hsrc
    exact hnotE (Or.inl hsrc)
  have hnotH :
      ¬ EprimeHorizontalSourceEvent start horizontalCenter
        horizontalSourceThreshold full := by
    intro hsrc
    exact hnotE (Or.inr hsrc)
  have hVupper :
      (((taoSection7RenewalPathPoint start full full.length).l -
        old.cornerL : ℤ) : ℝ) ≤ Lerr := by
    have hlt :
        (((taoSection7RenewalPathPoint start full full.length).l -
          old.cornerL : ℤ) : ℝ) < verticalSourceThreshold := by
      exact lt_of_not_ge hnotV
    exact le_trans hlt.le hV
  have hJupper :
      |(((taoSection7RenewalPathPoint start full full.length).j : ℕ) : ℝ) -
          horizontalCenter| ≤ Jerr := by
    have hlt :
        |(((taoSection7RenewalPathPoint start full full.length).j : ℕ) : ℝ) -
            horizontalCenter| < horizontalSourceThreshold := by
      exact lt_of_not_ge hnotH
    exact le_trans hlt.le hJ
  constructor
  · simpa [hpoint, TaoSection7Point.lReal, TaoSection7RenewalPoint.toPoint,
      EprimeVerticalSourceEvent] using hVupper
  · simpa [hpoint, hcenter, TaoSection7Point.jReal,
      TaoSection7RenewalPoint.toPoint, EprimeHorizontalSourceEvent] using hJupper

/--
Large-triangle row data at the actual `k+p` endpoint, with the two
outside-`E'` endpoint estimates supplied by `¬ E'`.

The scalar margin is intentionally still explicit: it comes from parameter
absorption, not from the complement of `E'`.  The lower vertical endpoint
bound is supplied by source-cut first-passage provenance.
-/
theorem lemma710OutsideEprimeKpRowData_of_largeTriangle_notEprime
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin S Lerr Jerr gap : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
    (hbase : old.Mem (pointAt q))
    (hS : S = ((old.cornerL - (pointAt q).l : ℤ) : ℝ))
    (hlarge :
      taoSection7Case3LargeTriangleEvent pointAt family
        (hcut.first + p) sMin)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
    (hcenter : horizontalCenter = (pointAt q).jReal + S / 4)
    (hV : verticalSourceThreshold ≤ Lerr)
    (hJ : horizontalSourceThreshold ≤ Jerr)
    (hgap0 : 0 ≤ gap)
    (hmargin :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    ∃ new : TaoSection7Triangle,
      new ∈ family ∧
        sMin ≤ new.size ∧
          OutsideEprimeBadLowerTipRowData old new (pointAt q)
            (pointAt (hcut.first + p)) S Lerr Jerr gap := by
  have hendpoint :
      (pointAt (hcut.first + p)).lReal - (old.cornerL : ℝ) ≤ Lerr ∧
        |(pointAt (hcut.first + p)).jReal -
            ((pointAt q).jReal + S / 4)| ≤ Jerr :=
    lemma710OutsideEprimeKpEndpointUpperJ_of_notEprime
      hcut hpoint_source hnotE hcenter hV hJ
  have hlower :
      (old.cornerL : ℝ) ≤ (pointAt (hcut.first + p)).lReal :=
    lemma710SourceCutCandidateData_pointAt_first_add_p_lReal_lower
      hcut hpoint_source
  have hL0 : 0 ≤ Lerr := by
    have hdiff_nonneg :
        0 ≤ (pointAt (hcut.first + p)).lReal - (old.cornerL : ℝ) := by
      linarith
    exact le_trans hdiff_nonneg hendpoint.1
  have hJ0 : 0 ≤ Jerr := by
    exact le_trans (abs_nonneg _) hendpoint.2
  exact
    lemma710OutsideEprimeKpRowData_of_largeTriangleEndpointEstimates
      hcut hbase hS hlarge hlower hendpoint.1 hendpoint.2
      hgap0 hL0 hJ0 hmargin

/--
Source-scale variant of the outside-`E'` `k+p` row-data wrapper.

This replaces the raw scalar-margin premise with the checked source-scale
margin API.  The remaining scale hypotheses are still explicit source-facing
obligations.
-/
theorem lemma710OutsideEprimeKpRowData_of_largeTriangle_notEprime_sourceScale
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJ CL CB : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
    (hbase : old.Mem (pointAt q))
    (hS : S = ((old.cornerL - (pointAt q).l : ℤ) : ℝ))
    (hlarge :
      taoSection7Case3LargeTriangleEvent pointAt family
        (hcut.first + p) sMin)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
    (hcenter : horizontalCenter = (pointAt q).jReal + S / 4)
    (hV : verticalSourceThreshold ≤ Lerr)
    (hJ : horizontalSourceThreshold ≤ Jerr)
    (hgap0 : 0 ≤ gap)
    (hCL_nonneg : 0 ≤ CL)
    (hMlower : M / (Real.log M)^2 ≤ S)
    (hJscale : Jerr ≤ CJ * M ^ (3 / 5 : ℝ))
    (hLscale : Lerr ≤ CL * B)
    (hBscale : B ≤ CB * M ^ (3 / 5 : ℝ))
    (habsorb :
      CJ * M ^ (3 / 5 : ℝ) +
          (Real.log 2 / Real.log 9) * (CL * CB * M ^ (3 / 5 : ℝ)) + 1 ≤
        (M / (Real.log M)^2) *
          (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    ∃ new : TaoSection7Triangle,
      new ∈ family ∧
        sMin ≤ new.size ∧
          OutsideEprimeBadLowerTipRowData old new (pointAt q)
            (pointAt (hcut.first + p)) S Lerr Jerr gap := by
  have hmargin :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) :=
    lemma710_error_margin_of_sourceScale
      hCL_nonneg hMlower hJscale hLscale hBscale habsorb
  exact
    lemma710OutsideEprimeKpRowData_of_largeTriangle_notEprime
      hcut hpoint_source hbase hS hlarge hnotE hcenter hV hJ hgap0 hmargin

/--
Current-scale variant of the outside-`E'` `k+p` row-data wrapper.

The current-scale ledger supplies the `S` identity and converts an
old-height-scale horizontal error into the scalar row-margin premise.  The
remaining hypotheses are still source-facing scale and absorption obligations.
-/
theorem lemma710OutsideEprimeKpRowData_of_largeTriangle_notEprime_currentScale
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
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
      taoSection7Case3LargeTriangleEvent pointAt family
        (hcut.first + p) sMin)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
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
          (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    ∃ new : TaoSection7Triangle,
      new ∈ family ∧
        sMin ≤ new.size ∧
          OutsideEprimeBadLowerTipRowData old new (pointAt q)
            (pointAt (hcut.first + p)) S Lerr Jerr gap := by
  have hS : S = ((old.cornerL - (pointAt q).l : ℤ) : ℝ) := by
    simpa [TaoSection7Triangle.verticalDepth] using hscale.S_def
  have hmargin :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) :=
    hscale.error_margin_of_s_rpow_bound_absorb
      hCL_nonneg hCJS_nonneg hJscale hJabsorb hLscale hBscale habsorb
  exact
    lemma710OutsideEprimeKpRowData_of_largeTriangle_notEprime
      hcut hpoint_source hbase hS hlarge hnotE hcenter hV hJ hgap0 hmargin

/--
Package actual `k+p` row data as the source-hit surface consumed by the
outside-`E'` `(7.62)` cover.

This is deterministic geometry plumbing.  It keeps the finite center
membership, old/new distinctness, and radius/absorption budgets explicit; the
theorem only removes the intermediate raw-endpoint-data premise.
-/
theorem lemma710OutsideEprimeKpEndpointSourceHitExists_of_rowData
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {sMin S Lerr Jerr gap Kgeo Bgeo J R : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
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
    (hLerrKB : Lerr ≤ Kgeo * Bgeo)
    (hrow :
      ∃ new : TaoSection7Triangle,
        new ∈ family ∧
          sMin ≤ new.size ∧
            OutsideEprimeBadLowerTipRowData old new (pointAt q)
              (pointAt (hcut.first + p)) S Lerr Jerr gap) :
    ∃ new : TaoSection7Triangle,
      Nonempty
        (Lemma710OutsideEprimeKpEndpointSourceHitData PrefixOK pointAt
          j sourceHeight firstBlock sourceSuffixes old q verticalGap start p
          full family new (pointAt (hcut.first + p)) C
          sMin gap Kgeo Bgeo J R) := by
  rcases hrow with ⟨new, hnew, hsize, hdata⟩
  have hraw :
      RawOutsideEprimeCommonPointEndpointData old new
        (pointAt (hcut.first + p)) gap Kgeo Bgeo :=
    rawOutsideEprimeCommonPointEndpointData_of_rowData
      hdata hgapKB hLerrKB
  exact
    ⟨new,
      ⟨lemma710OutsideEprimeKpEndpointSourceHitData_of_rawPointAtFirstAddP
          hcut hpoint_source hpair hold hnew (hne new hnew hsize)
          hsize hsourceJ hradius hraw (hanchor new hnew hsize)⟩⟩

/--
Current-scale outside-`E'` wrapper all the way to the `k+p` source-hit
existential.

The theorem deliberately remains short of the full source producer: it still
assumes threshold absorptions, final large-`M` absorption, finite center
membership, old/new distinctness, and source-hit radius budgets.
-/
theorem lemma710OutsideEprimeKpEndpointSourceHitExists_of_largeTriangle_notEprime_currentScale
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
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
      taoSection7Case3LargeTriangleEvent pointAt family
        (hcut.first + p) sMin)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
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
    ∃ new : TaoSection7Triangle,
      Nonempty
        (Lemma710OutsideEprimeKpEndpointSourceHitData PrefixOK pointAt
          j sourceHeight firstBlock sourceSuffixes old q verticalGap start p
          full family new (pointAt (hcut.first + p)) C
          sMin gap Kgeo Bgeo J R) := by
  have hrow :
      ∃ new : TaoSection7Triangle,
        new ∈ family ∧
          sMin ≤ new.size ∧
            OutsideEprimeBadLowerTipRowData old new (pointAt q)
              (pointAt (hcut.first + p)) S Lerr Jerr gap :=
    lemma710OutsideEprimeKpRowData_of_largeTriangle_notEprime_currentScale
      hcut hpoint_source hbase hscale hlarge hnotE hcenter hV hJ
      hgap0 hCL_nonneg hCJS_nonneg hJscale hJabsorb hLscale hBscale
      habsorb
  exact
    lemma710OutsideEprimeKpEndpointSourceHitExists_of_rowData
      hcut hpoint_source hpair hold hne hanchor hsourceJ hradius
      hgapKB hLerrKB hrow

/--
Per-sample bridge from current-scale outside-`E'` endpoint data to the
`hpoint` input of `lemma710OutsideEprimeNearSigmaCover_of_sourceHitData`.

The sample-space endpoint is still explicit: callers must identify
`endpoint ω` with the checked `pointAt (first+p)` source-cut endpoint and
supply the sample-to-large-triangle event bridge.
-/
theorem lemma710OutsideEprimeSourceHitExists_of_currentScaleSample
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω} {ω : Ω}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
    (hsample : ω ∈ largeEvent)
    (hlarge_of_sample :
      ω ∈ largeEvent →
        taoSection7Case3LargeTriangleEvent pointAt family
          (hcut.first + p) sMin)
    (hendpoint : endpoint ω = pointAt (hcut.first + p))
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
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
    ∃ new : TaoSection7Triangle,
      Lemma710OutsideEprimeSourceHitData family old new (endpoint ω)
        sMin gap Kgeo Bgeo J R ∧
        anchor old new ∈ C := by
  rw [hendpoint]
  rcases
    lemma710OutsideEprimeKpEndpointSourceHitExists_of_largeTriangle_notEprime_currentScale
      hcut hpoint_source hbase hscale (hlarge_of_sample hsample) hnotE
      hcenter hV hJ hgap0 hCL_nonneg hCJS_nonneg hJscale hJabsorb
      hLscale hBscale habsorb hpair hold hne hanchor hsourceJ hradius
      hgapKB hLerrKB with
    ⟨new, hdata⟩
  exact lemma710OutsideEprimeSourceHitExists_of_nonempty_kpEndpointSourceHitData
    hdata

/--
Full-window source-path data supplies the `point_source` field on a bounded
source suffix horizon.

The extra hypothesis `q + sourceSuffixes.length < P` is the current honest
boundary: `TaoSection7Case3FullWindowSourcePathData` identifies `pointAt t`
only for strict post-`q` times below `P`, while the `point_source` field asks
for every `N <= sourceSuffixes.length`.
-/
theorem lemma710PointSource_of_fullWindowSourcePathData
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {start : TaoSection7RenewalPoint}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hwindow : q + sourceSuffixes.length < P) :
    ∀ N pre,
      N ≤ sourceSuffixes.length →
        pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
          pointAt (q + N) =
            (taoSection7RenewalPathPoint start pre N).toPoint := by
  intro N pre hN hpre
  by_cases hN0 : N = 0
  · subst N
    have hpre0 : pre = [] := by
      simpa [taoSection7HoldIncrementsOfPrefixes] using hpre
    rw [hpre0]
    simpa [hstart] using hfull.point_q
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    have hqN : q < q + N := by omega
    have hqN_ltP : q + N < P := by omega
    have hpoint_window :
        pointAt (q + N) =
          (taoSection7SourceHitPathPoint j sourceHeight firstBlock
            sourceSuffixes ((q + N) - q)).toPoint :=
      hfull.point_window (q + N) hqN hqN_ltP
    have hsub : (q + N) - q = N := Nat.add_sub_cancel_left q N
    have hsource_path :
        (taoSection7RenewalPathPoint start
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).toPoint =
          (taoSection7SourceHitPathPoint j sourceHeight firstBlock
            sourceSuffixes N).toPoint := by
      rw [hstart]
      exact
        taoSection7RenewalPathPoint_sourceHit_toPoint_eq j sourceHeight
          firstBlock sourceSuffixes N
    have htake :
        taoSection7RenewalPathPoint start pre N =
          taoSection7RenewalPathPoint start
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N := by
      rw [hpre]
      exact
        renewalPathPoint_take_eq_of_le start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N N le_rfl
    calc
      pointAt (q + N) =
          (taoSection7SourceHitPathPoint j sourceHeight firstBlock
            sourceSuffixes ((q + N) - q)).toPoint := hpoint_window
      _ =
          (taoSection7SourceHitPathPoint j sourceHeight firstBlock
            sourceSuffixes N).toPoint := by rw [hsub]
      _ =
          (taoSection7RenewalPathPoint start
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).toPoint :=
            hsource_path.symm
      _ = (taoSection7RenewalPathPoint start pre N).toPoint := by rw [htake]

/--
Local-horizon variant of the full-window source-path identification.

Unlike `lemma710PointSource_of_fullWindowSourcePathData`, this does not require
the whole source suffix list to lie below `P`; it identifies one fixed horizon
`N` whenever the corresponding time satisfies `q < q+N < P`.
-/
theorem lemma710PointSourceAt_of_fullWindowSourcePathData
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q N : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {start : TaoSection7RenewalPoint}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hqN : q < q + N)
    (hN_ltP : q + N < P) :
    pointAt (q + N) =
      (taoSection7RenewalPathPoint start
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).toPoint := by
  have hpoint_window :
      pointAt (q + N) =
        (taoSection7SourceHitPathPoint j sourceHeight firstBlock
          sourceSuffixes ((q + N) - q)).toPoint :=
    hfull.point_window (q + N) hqN hN_ltP
  have hsub : (q + N) - q = N := Nat.add_sub_cancel_left q N
  have hsource_path :
      (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).toPoint =
        (taoSection7SourceHitPathPoint j sourceHeight firstBlock
          sourceSuffixes N).toPoint := by
    rw [hstart]
    exact
      taoSection7RenewalPathPoint_sourceHit_toPoint_eq j sourceHeight
        firstBlock sourceSuffixes N
  calc
    pointAt (q + N) =
        (taoSection7SourceHitPathPoint j sourceHeight firstBlock
          sourceSuffixes ((q + N) - q)).toPoint := hpoint_window
    _ =
        (taoSection7SourceHitPathPoint j sourceHeight firstBlock
          sourceSuffixes N).toPoint := by rw [hsub]
    _ =
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).toPoint :=
          hsource_path.symm

/--
Source-cut endpoint identification from a local full-window horizon.

This is the fixed `K+p` endpoint version used when the source suffix list may
be longer than the active window.  The endpoint-time bounds stay explicit.
-/
theorem lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint_of_fullWindowSourcePathData
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hq_first_p : q < hcut.first + p)
    (hfirst_p_ltP : hcut.first + p < P) :
    pointAt (hcut.first + p) =
      (taoSection7RenewalPathPoint start full full.length).toPoint := by
  have hclock :
      q + (item.1 + p) = hcut.first + p := by
    calc
      q + (item.1 + p) = q + item.1 + p := by omega
      _ = hcut.first + p :=
        lemma710SourceCutCandidateData_q_add_item_add_p_eq_first_add_p hcut
  have hq_local : q < q + (item.1 + p) := by
    rw [hclock]
    exact hq_first_p
  have hlocal_ltP : q + (item.1 + p) < P := by
    rw [hclock]
    exact hfirst_p_ltP
  have hlocal :
      pointAt (q + (item.1 + p)) =
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes)
          (item.1 + p)).toPoint :=
    lemma710PointSourceAt_of_fullWindowSourcePathData hfull hstart
      hq_local hlocal_ltP
  calc
    pointAt (hcut.first + p) = pointAt (q + (item.1 + p)) := by
      rw [hclock]
    _ =
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes)
          (item.1 + p)).toPoint := hlocal
    _ =
        (taoSection7RenewalPathPoint start full full.length).toPoint :=
          (lemma710SourceCutCandidateData_fullEndpoint_toPoint_eq hcut).symm

/--
Endpoint compatibility from a local full-window horizon, without requiring the
whole source suffix list to fit below `P`.
-/
theorem lemma710OutsideEprimeEndpointEq_of_sourceCutFullEndpoint_localHorizon
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hq_first_p : q < hcut.first + p)
    (hfirst_p_ltP : hcut.first + p < P)
    (hendpoint_source :
      endpoint ω =
        (taoSection7RenewalPathPoint start full full.length).toPoint) :
    endpoint ω = pointAt (hcut.first + p) :=
  hendpoint_source.trans
    (lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint_of_fullWindowSourcePathData
      hfull hstart hcut hq_first_p hfirst_p_ltP).symm

/--
Endpoint compatibility from the checked source-cut full endpoint.

This removes one raw sample-space premise for later producers: if the sample
endpoint is the source full-path endpoint, the existing source-cut theorem
identifies it with `pointAt (first+p)`.
-/
theorem lemma710OutsideEprimeEndpointEq_of_sourceCutFullEndpoint
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
    (hendpoint_source :
      endpoint ω =
        (taoSection7RenewalPathPoint start full full.length).toPoint) :
    endpoint ω = pointAt (hcut.first + p) :=
  hendpoint_source.trans
    (lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
      hcut hpoint_source).symm

/--
Source-endpoint variant of the current-scale per-sample source-hit bridge.

Compared with `lemma710OutsideEprimeSourceHitExists_of_currentScaleSample`,
this theorem derives `endpoint ω = pointAt (first+p)` from the source-cut
full-endpoint identity.  It is still not a finite PMF sample producer: the
source-cut data, large-triangle fact, `¬E'` fact, and scalar/center budgets
remain explicit.
-/
theorem lemma710OutsideEprimeSourceHitExists_of_currentScaleSample_sourceEndpoint
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω} {ω : Ω}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
    (hsample : ω ∈ largeEvent)
    (hlarge_of_sample :
      ω ∈ largeEvent →
        taoSection7Case3LargeTriangleEvent pointAt family
          (hcut.first + p) sMin)
    (hendpoint_source :
      endpoint ω =
        (taoSection7RenewalPathPoint start full full.length).toPoint)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
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
    ∃ new : TaoSection7Triangle,
      Lemma710OutsideEprimeSourceHitData family old new (endpoint ω)
        sMin gap Kgeo Bgeo J R ∧
        anchor old new ∈ C :=
  lemma710OutsideEprimeSourceHitExists_of_currentScaleSample
    hcut hpoint_source hbase hscale hsample hlarge_of_sample
    (lemma710OutsideEprimeEndpointEq_of_sourceCutFullEndpoint
      hcut hpoint_source hendpoint_source)
    hnotE hcenter hV hJ hgap0 hCL_nonneg hCJS_nonneg hJscale hJabsorb
    hLscale hBscale habsorb hpair hold hne hanchor hsourceJ hradius
    hgapKB hLerrKB

/--
Per-sample input package for the current-scale outside-`E'` source-hit bridge.

Unlike the fixed-source cover adapter, this record indexes the source
realization data by the sample `ω`: each sample carries its own `pointAt`,
source suffixes, source-cut datum, endpoint equality, `¬ E'` fact, and
current-scale hypotheses.  It is still an input contract; it does not produce
those fields from the finite PMF sample.
-/
structure Lemma710OutsideEprimeCurrentScaleSampleInputs
    {Ω : Type*}
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (C : Finset TaoSection7Point)
    (endpoint : Ω → TaoSection7Point) (largeEvent : Set Ω) (ω : Ω)
    (sMin gap Kgeo Bgeo J R : ℝ) : Type where
  PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop
  pointAt : ℕ → TaoSection7Point
  j : ℕ+
  sourceHeight : ℕ
  firstBlock : List ℕ
  sourceSuffixes : List (List ℕ)
  q : ℕ
  verticalGap : ℕ
  p : ℕ
  n : ℕ
  start : TaoSection7RenewalPoint
  full : List TaoSection7RenewalPoint
  item : ℕ × List TaoSection7RenewalPoint
  horizontalCenter : ℝ
  verticalSourceThreshold : ℝ
  horizontalSourceThreshold : ℝ
  M : ℝ
  S : ℝ
  B : ℝ
  Lerr : ℝ
  Jerr : ℝ
  CJS : ℝ
  CJm : ℝ
  CL : ℝ
  CB : ℝ
  cut :
    Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start p full item
  point_source :
    ∀ N pre,
      N ≤ sourceSuffixes.length →
        pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
          pointAt (q + N) =
            (taoSection7RenewalPathPoint start pre N).toPoint
  base_mem : old.Mem (pointAt q)
  scale : TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S
  large :
    taoSection7Case3LargeTriangleEvent pointAt family (cut.first + p) sMin
  endpoint_eq : endpoint ω = pointAt (cut.first + p)
  notE :
    ¬ EprimeSourceEvent start old horizontalCenter
      verticalSourceThreshold horizontalSourceThreshold full
  center_eq : horizontalCenter = (pointAt q).jReal + S / 4
  vertical_threshold_le : verticalSourceThreshold ≤ Lerr
  horizontal_threshold_le : horizontalSourceThreshold ≤ Jerr
  gap_nonneg : 0 ≤ gap
  CL_nonneg : 0 ≤ CL
  CJS_nonneg : 0 ≤ CJS
  Jerr_scale : Jerr ≤ CJS * S ^ (3 / 5 : ℝ)
  Jerr_absorb :
    CJS * ((Real.log 9 / Real.log 2) * M) ^ (3 / 5 : ℝ) ≤
      CJm * M ^ (3 / 5 : ℝ)
  Lerr_scale : Lerr ≤ CL * B
  B_scale : B ≤ CB * M ^ (3 / 5 : ℝ)
  final_absorb :
    CJm * M ^ (3 / 5 : ℝ) +
        (Real.log 2 / Real.log 9) * (CL * CB * M ^ (3 / 5 : ℝ)) + 1 ≤
      (M / (Real.log M)^2) *
        (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))
  pairwiseDisjoint : TaoSection7TriangleFamilyPairwiseDisjoint family
  old_mem_family : old ∈ family
  new_ne_old :
    ∀ new : TaoSection7Triangle, new ∈ family → sMin ≤ new.size →
      new ≠ old
  anchor_mem :
    ∀ new : TaoSection7Triangle, new ∈ family → sMin ≤ new.size →
      anchor old new ∈ C
  sourceJ : (Real.log 2 / Real.log 9) * (Kgeo * Bgeo + Kgeo * Bgeo) ≤ J
  radius_absorbs : J ^ 2 + (Kgeo * Bgeo) ^ 2 ≤ R ^ 2
  gap_absorbs : gap ≤ Kgeo * Bgeo
  Lerr_absorbs : Lerr ≤ Kgeo * Bgeo

/--
Minimal full-window/source-endpoint provenance for a current-scale outside-`E'`
sample.

This stores only the data needed to derive the existing sample-input record's
`point_source` and `endpoint_eq` fields.  Source cuts, large-event facts,
`¬E'`, scale controls, center membership, and absorption inequalities remain
outside this packet, so this is not the finite-PMF sample producer.
-/
structure Lemma710OutsideEprimeCurrentScaleSampleFullWindowSourceEndpointProvenance
    {Ω : Type*}
    (endpoint : Ω → TaoSection7Point) (ω : Ω)
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (nSrc Jsrc A : ℕ) (xi : ZMod (3 ^ nSrc)) (epsilon : ℝ)
    (P threshold q : ℕ)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint) : Type where
  source_path :
    TaoSection7Case3FullWindowSourcePathData
      W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
      firstBlock sourceSuffixes
  start_eq : start = taoSection7SourceHitPoint j sourceHeight firstBlock
  source_window_ltP : q + sourceSuffixes.length < P
  endpoint_source :
    endpoint ω =
      (taoSection7RenewalPathPoint start full full.length).toPoint

/--
Construct minimal full-window/source-endpoint provenance from an ambient
endpoint equality at `first+p`.

This removes the direct `endpoint_source` premise once a source-cut datum and
the ambient endpoint equality are available.  It still assumes the source cut;
it does not produce sample-input data from the finite PMF.
-/
def lemma710OutsideEprimeCurrentScaleSampleFullWindowSourceEndpointProvenance_of_endpointAtAmbient
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hwindow : q + sourceSuffixes.length < P)
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hendpoint_ambient : endpoint ω = pointAt (hcut.first + p)) :
    Lemma710OutsideEprimeCurrentScaleSampleFullWindowSourceEndpointProvenance
      endpoint ω W pointAt nSrc Jsrc A xi epsilon P threshold q j
      sourceHeight firstBlock sourceSuffixes start full where
  source_path := hfull
  start_eq := hstart
  source_window_ltP := hwindow
  endpoint_source := by
    have hpoint_source :
        ∀ N pre,
          N ≤ sourceSuffixes.length →
            pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
              pointAt (q + N) =
                (taoSection7RenewalPathPoint start pre N).toPoint :=
      lemma710PointSource_of_fullWindowSourcePathData hfull hstart hwindow
    exact
      hendpoint_ambient.trans
        (lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
          hcut hpoint_source)

/--
Full-window/source-endpoint constructor for the current-scale sample-input
record.

This fills only the `point_source` and `endpoint_eq` fields from checked
full-window source-path support.  The hard sample, event, scale, center, and
absorption fields remain explicit hypotheses; in particular this is not the
actual finite PMF/sample producer for `(7.62)`.
-/
def lemma710OutsideEprimeCurrentScaleSampleInputs_of_fullWindowSourceEndpoint
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω} {ω : Ω}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hwindow : q + sourceSuffixes.length < P)
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
    (hlarge :
      taoSection7Case3LargeTriangleEvent pointAt family
        (hcut.first + p) sMin)
    (hendpoint_source :
      endpoint ω =
        (taoSection7RenewalPathPoint start full full.length).toPoint)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
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
    Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
      largeEvent ω sMin gap Kgeo Bgeo J R where
  PrefixOK := PrefixOK
  pointAt := pointAt
  j := j
  sourceHeight := sourceHeight
  firstBlock := firstBlock
  sourceSuffixes := sourceSuffixes
  q := q
  verticalGap := verticalGap
  p := p
  n := n
  start := start
  full := full
  item := item
  horizontalCenter := horizontalCenter
  verticalSourceThreshold := verticalSourceThreshold
  horizontalSourceThreshold := horizontalSourceThreshold
  M := M
  S := S
  B := B
  Lerr := Lerr
  Jerr := Jerr
  CJS := CJS
  CJm := CJm
  CL := CL
  CB := CB
  cut := hcut
  point_source :=
    lemma710PointSource_of_fullWindowSourcePathData hfull hstart hwindow
  base_mem := hbase
  scale := hscale
  large := hlarge
  endpoint_eq :=
    lemma710OutsideEprimeEndpointEq_of_sourceCutFullEndpoint
      hcut
      (lemma710PointSource_of_fullWindowSourcePathData hfull hstart hwindow)
      hendpoint_source
  notE := hnotE
  center_eq := hcenter
  vertical_threshold_le := hV
  horizontal_threshold_le := hJ
  gap_nonneg := hgap0
  CL_nonneg := hCL_nonneg
  CJS_nonneg := hCJS_nonneg
  Jerr_scale := hJscale
  Jerr_absorb := hJabsorb
  Lerr_scale := hLscale
  B_scale := hBscale
  final_absorb := habsorb
  pairwiseDisjoint := hpair
  old_mem_family := hold
  new_ne_old := hne
  anchor_mem := hanchor
  sourceJ := hsourceJ
  radius_absorbs := hradius
  gap_absorbs := hgapKB
  Lerr_absorbs := hLerrKB

/--
Constructor from minimal full-window/source-endpoint provenance to the existing
sample-input record.

This bundles only the derivation of `point_source` and `endpoint_eq`; all
source-cut, event, scale, center, and absorption data remain explicit inputs.
-/
def lemma710OutsideEprimeCurrentScaleSampleInputs_of_fullWindowSourceEndpointProvenance
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω} {ω : Ω}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hprov :
      Lemma710OutsideEprimeCurrentScaleSampleFullWindowSourceEndpointProvenance
        endpoint ω W pointAt nSrc Jsrc A xi epsilon P threshold q j
        sourceHeight firstBlock sourceSuffixes start full)
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
    (hlarge :
      taoSection7Case3LargeTriangleEvent pointAt family
        (hcut.first + p) sMin)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full)
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
    Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
      largeEvent ω sMin gap Kgeo Bgeo J R :=
  lemma710OutsideEprimeCurrentScaleSampleInputs_of_fullWindowSourceEndpoint
    (W := W) (PrefixOK := PrefixOK) (pointAt := pointAt)
    (nSrc := nSrc) (Jsrc := Jsrc) (A := A) (xi := xi)
    (epsilon := epsilon) (P := P) (threshold := threshold)
    (q := q) (j := j) (sourceHeight := sourceHeight)
    (firstBlock := firstBlock) (sourceSuffixes := sourceSuffixes)
    (old := old) (verticalGap := verticalGap) (p := p) (n := n)
    (start := start) (full := full) (item := item)
    (family := family) (C := C) (endpoint := endpoint)
    (largeEvent := largeEvent) (ω := ω)
    (horizontalCenter := horizontalCenter)
    (verticalSourceThreshold := verticalSourceThreshold)
    (horizontalSourceThreshold := horizontalSourceThreshold)
    (sMin := sMin) (M := M) (S := S) (B := B)
    (Lerr := Lerr) (Jerr := Jerr) (gap := gap)
    (CJS := CJS) (CJm := CJm) (CL := CL) (CB := CB)
    (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
    hprov.source_path hprov.start_eq hprov.source_window_ltP hcut hbase
    hscale hlarge hprov.endpoint_source hnotE hcenter hV hJ hgap0
    hCL_nonneg hCJS_nonneg hJscale hJabsorb hLscale hBscale habsorb
    hpair hold hne hanchor hsourceJ hradius hgapKB hLerrKB

/--
Source-run/event data for a current-scale outside-`E'` sample.

This replaces a direct `Lemma710SourceCutCandidateData` premise with the
underlying random-`k` ledger and q-relative fixed-`p` horizon, and replaces a
direct source-path endpoint equality with the ambient equality
`endpoint ω = pointAt (first+p)`.  It still supplies the large-triangle and
`¬E'` facts, so it is support for sample-input production, not the finite-PMF
producer itself.
-/
structure Lemma710OutsideEprimeSourceRunEventData
    {Ω : Type*}
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap p : ℕ)
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (endpoint : Ω → TaoSection7Point) (ω : Ω)
    (full : List TaoSection7RenewalPoint)
    (item : ℕ × List TaoSection7RenewalPoint)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ) : Type where
  first : ℕ
  ledger :
    RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q first item.1 verticalGap start item.2
  full_eq :
    full =
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (item.1 + p)
  horizon_le : item.1 + p ≤ sourceSuffixes.length
  large :
    taoSection7Case3LargeTriangleEvent pointAt family (first + p) sMin
  endpoint_at_ambient : endpoint ω = pointAt (first + p)
  notE :
    ¬ EprimeSourceEvent start old horizontalCenter
      verticalSourceThreshold horizontalSourceThreshold full

/--
Event-membership data used to derive the source-run packet's `large` and
`notE` fields.

This keeps the sample's membership in the large event and outside-`E'` event
visible, together with the maps from those event memberships to the concrete
per-sample facts.  The maps remain hypotheses; this is not the finite-PMF
sample producer.
-/
structure Lemma710OutsideEprimeSampleEventMembershipData
    {Ω : Type*}
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (largeEvent outsideEprimeEvent : Set Ω) (ω : Ω)
    (first p : ℕ) (sMin : ℝ)
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (full : List TaoSection7RenewalPoint)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ) :
    Prop where
  sample_mem : ω ∈ largeEvent
  outside_mem : ω ∈ outsideEprimeEvent
  large_of_sample :
    ω ∈ largeEvent →
      taoSection7Case3LargeTriangleEvent pointAt family (first + p) sMin
  notE_of_outside :
    ω ∈ outsideEprimeEvent →
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold full

/--
Event-domain maps for the current-scale outside-`E'` sample boundary.

This records that the abstract sample-space events are anchored to the
large-triangle and outside-`E'` pointwise facts through sample-indexed clocks
and source windows.  It is still a map surface: it does not prove the finite
PMF event law or produce membership in either event.
-/
structure Lemma710OutsideEprimeSampleEventDomainMaps
    {Ω : Type*}
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (largeEvent outsideEprimeEvent : Set Ω)
    (firstOf : Ω → ℕ)
    (fullOf : Ω → List TaoSection7RenewalPoint)
    (p : ℕ) (sMin : ℝ)
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ) :
    Prop where
  large_subset :
    ∀ ω, ω ∈ largeEvent →
      taoSection7Case3LargeTriangleEvent pointAt family
        (firstOf ω + p) sMin
  outside_subset :
    ∀ ω, ω ∈ outsideEprimeEvent →
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold (fullOf ω)

/--
Definitional large-triangle sample event for the current-scale outside-`E'`
boundary.

Membership is exactly the large-triangle fact at the sample-indexed ambient
clock `firstOf ω + p`.
-/
def Lemma710LargeTriangleSampleEvent
    {Ω : Type*}
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (firstOf : Ω → ℕ) (p : ℕ) (sMin : ℝ) : Set Ω :=
  {ω | taoSection7Case3LargeTriangleEvent pointAt family
    (firstOf ω + p) sMin}

/--
Definitional outside-`E'` sample event for the current-scale boundary.

Membership is exactly the complement of `EprimeSourceEvent` on the
sample-indexed source window `fullOf ω`.
-/
def Lemma710OutsideEprimeSampleEvent
    {Ω : Type*}
    (fullOf : Ω → List TaoSection7RenewalPoint)
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ) :
    Set Ω :=
  {ω | ¬ EprimeSourceEvent start old horizontalCenter
    verticalSourceThreshold horizontalSourceThreshold (fullOf ω)}

/--
The definitional large-triangle and outside-`E'` sample events supply the
event-domain maps by unfolding.

This anchors the abstract `largeEvent`/`outsideEprimeEvent` parameters to the
pointwise event facts, without proving membership in either event or any
finite-PMF law.
-/
def lemma710OutsideEprimeSampleEventDomainMaps_of_definitionalEvents
    {Ω : Type*}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {p : ℕ} {sMin : ℝ}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ} :
    Lemma710OutsideEprimeSampleEventDomainMaps pointAt family
      (Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin)
      (Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold)
      firstOf fullOf p sMin start old horizontalCenter
      verticalSourceThreshold horizontalSourceThreshold where
  large_subset := by
    intro ω hω
    exact hω
  outside_subset := by
    intro ω hω
    exact hω

/--
Source-cut-indexed sample decode data for the current-scale outside-`E'`
sample boundary.

The decode facts are tied to a concrete `Lemma710SourceCutCandidateData`
witness for the selected `item` and canonical `take (item.1+p)` source window.
This avoids silently decoding an independent sample clock/window that may not
cohere with the crossing-selected source cut.
-/
structure Lemma710OutsideEprimeSampleDecodeData
    {Ω : Type*}
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap p : ℕ)
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (endpoint : Ω → TaoSection7Point) (ω : Ω)
    (firstOf : Ω → ℕ)
    (fullOf : Ω → List TaoSection7RenewalPoint)
    (item : ℕ × List TaoSection7RenewalPoint)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ)
    (cut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
        item) : Prop where
  sample_mem :
    ω ∈
      Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
        Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold
  endpoint_eq : endpoint ω = pointAt (cut.first + p)
  firstOf_eq : firstOf ω = q + item.1
  fullOf_eq :
    fullOf ω =
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (item.1 + p)

/--
Selected source-cut sample decode data for the current-scale outside-`E'`
boundary.

This is the producer-facing packet shape: a future finite-PMF/source-sample
theorem should select one source-cut candidate and prove the four decode facts
for that same candidate.  It is still only a packet; it does not construct the
selected cut or decode facts from Tao's random sample.
-/
structure Lemma710OutsideEprimeSelectedSampleDecodeData
    {Ω : Type*}
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap p : ℕ)
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (endpoint : Ω → TaoSection7Point) (ω : Ω)
    (firstOf : Ω → ℕ)
    (fullOf : Ω → List TaoSection7RenewalPoint)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ) : Type where
  item : ℕ × List TaoSection7RenewalPoint
  cut :
    Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start p
      ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (item.1 + p))
      item
  decode :
    Lemma710OutsideEprimeSampleDecodeData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
      firstOf fullOf item horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold sMin cut

/--
Build source-cut-indexed decode data from pointwise event facts.

This is a support constructor for the future sample producer: it derives the
bundled `sample_mem` field from the large-triangle fact at the selected
source-cut endpoint, the outside-`E'` source-window fact, and the sample
clock/window identifications.  It still assumes the endpoint equality and the
sample clock/window equalities; it is not finite-PMF sample-decode production.
-/
def lemma710OutsideEprimeSampleDecodeData_of_pointwiseFacts
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ}
    {cut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
        item}
    (hlarge :
      taoSection7Case3LargeTriangleEvent pointAt family (cut.first + p) sMin)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p)))
    (hendpoint : endpoint ω = pointAt (cut.first + p))
    (hfirstOf : firstOf ω = q + item.1)
    (hfullOf :
      fullOf ω =
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p)) :
    Lemma710OutsideEprimeSampleDecodeData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
      firstOf fullOf item horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold sMin cut where
  sample_mem := by
    constructor
    · have hclock : firstOf ω + p = cut.first + p := by
        calc
          firstOf ω + p = (q + item.1) + p := by rw [hfirstOf]
          _ = cut.first + p := by
            rw [lemma710SourceCutCandidateData_q_add_item_eq_first cut]
      simpa [Lemma710LargeTriangleSampleEvent, hclock] using hlarge
    · simpa [Lemma710OutsideEprimeSampleEvent, hfullOf] using hnotE
  endpoint_eq := hendpoint
  firstOf_eq := hfirstOf
  fullOf_eq := hfullOf

/--
Selected-packet wrapper around the pointwise decode-data constructor.

This packages a selected canonical source cut together with decode data whose
event-membership field is derived from pointwise large/outside-`E'` facts.  It
still assumes the selected cut and sample endpoint/clock/window alignment, so
it is support for the eventual producer rather than producer evidence.
-/
def lemma710OutsideEprimeSelectedSampleDecodeData_of_pointwiseFacts
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ}
    (cut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
        item)
    (hlarge :
      taoSection7Case3LargeTriangleEvent pointAt family (cut.first + p) sMin)
    (hnotE :
      ¬ EprimeSourceEvent start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p)))
    (hendpoint : endpoint ω = pointAt (cut.first + p))
    (hfirstOf : firstOf ω = q + item.1)
    (hfullOf :
      fullOf ω =
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p)) :
    Lemma710OutsideEprimeSelectedSampleDecodeData PrefixOK pointAt j
      sourceHeight firstBlock sourceSuffixes old q verticalGap p start family
      endpoint ω firstOf fullOf horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold sMin where
  item := item
  cut := cut
  decode :=
    lemma710OutsideEprimeSampleDecodeData_of_pointwiseFacts
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (p := p) (start := start)
      (family := family) (endpoint := endpoint) (ω := ω)
      (firstOf := firstOf) (fullOf := fullOf) (item := item)
      (horizontalCenter := horizontalCenter)
      (verticalSourceThreshold := verticalSourceThreshold)
      (horizontalSourceThreshold := horizontalSourceThreshold)
      (sMin := sMin) (cut := cut)
      hlarge hnotE hendpoint hfirstOf hfullOf

/--
Build the pointwise event-membership packet from anchored event-domain maps.

The equalities identify the sample-indexed clock/window with the fixed
source-run packet currently being constructed.
-/
def lemma710OutsideEprimeSampleEventMembershipData_of_eventDomainMaps
    {Ω : Type*}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {largeEvent outsideEprimeEvent : Set Ω} {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {first p : ℕ} {sMin : ℝ}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {full : List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ}
    (hmaps :
      Lemma710OutsideEprimeSampleEventDomainMaps pointAt family
        largeEvent outsideEprimeEvent firstOf fullOf p sMin start old
        horizontalCenter verticalSourceThreshold horizontalSourceThreshold)
    (hmem : ω ∈ largeEvent ∩ outsideEprimeEvent)
    (hfirst : firstOf ω = first)
    (hfull : fullOf ω = full) :
    Lemma710OutsideEprimeSampleEventMembershipData pointAt family
      largeEvent outsideEprimeEvent ω first p sMin start old full
      horizontalCenter verticalSourceThreshold horizontalSourceThreshold where
  sample_mem := hmem.1
  outside_mem := hmem.2
  large_of_sample := by
    intro hlarge
    simpa [hfirst] using hmaps.large_subset ω hlarge
  notE_of_outside := by
    intro houtside
    simpa [hfull] using hmaps.outside_subset ω houtside

/--
Build source-run/event data from source-run horizon facts and event membership
maps.

This removes direct `large` and `notE` fields from this constructor boundary,
but it still assumes the event-membership-to-fact maps.
-/
def lemma710OutsideEprimeSourceRunEventData_of_eventMembership
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p first : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    {largeEvent outsideEprimeEvent : Set Ω}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ}
    (hledger :
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first item.1 verticalGap start item.2)
    (hfull :
      full =
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
    (hhorizon : item.1 + p ≤ sourceSuffixes.length)
    (hendpoint : endpoint ω = pointAt (first + p))
    (hevent :
      Lemma710OutsideEprimeSampleEventMembershipData pointAt family
        largeEvent outsideEprimeEvent ω first p sMin start old full
        horizontalCenter verticalSourceThreshold horizontalSourceThreshold) :
    Lemma710OutsideEprimeSourceRunEventData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
      full item horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin where
  first := first
  ledger := hledger
  full_eq := hfull
  horizon_le := hhorizon
  large := hevent.large_of_sample hevent.sample_mem
  endpoint_at_ambient := hendpoint
  notE := hevent.notE_of_outside hevent.outside_mem

/--
Build source-run/event data from a source-cut-indexed sample-decode packet.

This consumes decode facts tied to the exact source-cut witness.  It is still
only a packet consumer: it does not prove the sample decode facts from the
finite PMF or source construction.
-/
def lemma710OutsideEprimeSourceRunEventData_of_sampleDecodeData
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ}
    {cut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
        item}
    (hdecode :
      Lemma710OutsideEprimeSampleDecodeData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
        firstOf fullOf item horizontalCenter verticalSourceThreshold
        horizontalSourceThreshold sMin cut) :
    Lemma710OutsideEprimeSourceRunEventData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
      ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (item.1 + p))
      item horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin := by
  have hfirst : firstOf ω = cut.first := by
    calc
      firstOf ω = q + item.1 := hdecode.firstOf_eq
      _ = cut.first := lemma710SourceCutCandidateData_q_add_item_eq_first cut
  let hevent :=
    lemma710OutsideEprimeSampleEventMembershipData_of_eventDomainMaps
      (largeEvent :=
        Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
          Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold)
      (outsideEprimeEvent :=
        Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold)
      { large_subset := by
          intro ω hω
          exact hω.1
        outside_subset := by
          intro ω hω
          exact hω }
      ⟨hdecode.sample_mem, hdecode.sample_mem.2⟩ hfirst
      hdecode.fullOf_eq
  exact
    lemma710OutsideEprimeSourceRunEventData_of_eventMembership
      (full :=
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
      cut.ledger rfl
      (by simpa [cut.ledger.K_eq_first_sub_q] using cut.source_cut_le)
      hdecode.endpoint_eq hevent

/--
Build source-run/event data from a selected source-cut decode packet.

This is a thin consumer of `Lemma710OutsideEprimeSelectedSampleDecodeData`.
It preserves the selected item and canonical full window in the output so later
adapters do not need a universal decode premise over all possible source cuts.
-/
def lemma710OutsideEprimeSourceRunEventData_of_selectedSampleDecodeData
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ}
    (hsel :
      Lemma710OutsideEprimeSelectedSampleDecodeData PrefixOK pointAt j
        sourceHeight firstBlock sourceSuffixes old q verticalGap p start family
        endpoint ω firstOf fullOf horizontalCenter verticalSourceThreshold
        horizontalSourceThreshold sMin) :
    Lemma710OutsideEprimeSourceRunEventData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
      ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (hsel.item.1 + p))
      hsel.item horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin :=
  lemma710OutsideEprimeSourceRunEventData_of_sampleDecodeData
    (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
    (sourceHeight := sourceHeight) (firstBlock := firstBlock)
    (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
    (verticalGap := verticalGap) (p := p) (start := start)
    (family := family) (endpoint := endpoint) (ω := ω)
    (firstOf := firstOf) (fullOf := fullOf) (item := hsel.item)
    (horizontalCenter := horizontalCenter)
    (verticalSourceThreshold := verticalSourceThreshold)
    (horizontalSourceThreshold := horizontalSourceThreshold)
    (sMin := sMin) (cut := hsel.cut) hsel.decode

/--
Project a fixed-`p` source-run candidate into source-run/event data using
endpoint and event facts indexed by the candidate's hidden ambient `first`.

This is still support-only: it preserves the fixed candidate's q-relative
random-`k` clock and consumes supplied endpoint/event membership maps.
-/
theorem lemma710OutsideEprimeSourceRunEventData_nonempty_of_fixedPSourceRunCandidate_eventMembership
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    {largeEvent outsideEprimeEvent : Set Ω}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ}
    (hfix :
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hendpoint :
      ∀ first,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        endpoint ω = pointAt (first + p))
    (hevent :
      ∀ first,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        Lemma710OutsideEprimeSampleEventMembershipData pointAt family
          largeEvent outsideEprimeEvent ω first p sMin start old full
          horizontalCenter verticalSourceThreshold horizontalSourceThreshold) :
    Nonempty
      (Lemma710OutsideEprimeSourceRunEventData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
      full item horizontalCenter verticalSourceThreshold horizontalSourceThreshold
        sMin) := by
  rcases hfix.ledger with ⟨first, hledger⟩
  exact ⟨lemma710OutsideEprimeSourceRunEventData_of_eventMembership
    hledger hfix.full_eq hfix.horizon_le
    (hendpoint first hledger) (hevent first hledger)⟩

/--
Project a fixed-`p` source-run candidate into nonempty source-run/event data
from anchored event-domain maps.

This composes the event-domain map adapter with the fixed-`p`
event-membership projection.  It still assumes sample membership in the
intersection, endpoint identification, and the sample-indexed clock/window
identifications for the selected source-run ledger.
-/
theorem lemma710OutsideEprimeSourceRunEventData_nonempty_of_fixedPSourceRunCandidate_eventDomainMaps
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {endpoint : Ω → TaoSection7Point} {ω : Ω}
    {largeEvent outsideEprimeEvent : Set Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin : ℝ}
    (hfix :
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hmaps :
      Lemma710OutsideEprimeSampleEventDomainMaps pointAt family
        largeEvent outsideEprimeEvent firstOf fullOf p sMin start old
        horizontalCenter verticalSourceThreshold horizontalSourceThreshold)
    (hmem : ω ∈ largeEvent ∩ outsideEprimeEvent)
    (hendpoint :
      ∀ first,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        endpoint ω = pointAt (first + p))
    (hfirst :
      ∀ first,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        firstOf ω = first)
    (hfull : fullOf ω = full) :
    Nonempty
      (Lemma710OutsideEprimeSourceRunEventData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
      full item horizontalCenter verticalSourceThreshold horizontalSourceThreshold
        sMin) :=
  lemma710OutsideEprimeSourceRunEventData_nonempty_of_fixedPSourceRunCandidate_eventMembership
    hfix hendpoint
    (fun first hledger =>
      lemma710OutsideEprimeSampleEventMembershipData_of_eventDomainMaps
        hmaps hmem (hfirst first hledger) hfull)

/--
Build current-scale sample inputs from source-run/event data.

The constructor derives the source-cut datum from the random-`k` ledger and
fixed-`p` horizon, derives the minimal full-window/source-endpoint provenance
from the ambient endpoint equality, and then calls the existing
full-window/source-endpoint sample-input constructor.  Scale, center, family,
and absorption hypotheses remain explicit.
-/
def lemma710OutsideEprimeCurrentScaleSampleInputs_of_sourceRunEventData
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent : Set Ω} {ω : Ω}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hwindow : q + sourceSuffixes.length < P)
    (hsrc :
      Lemma710OutsideEprimeSourceRunEventData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap p start family endpoint ω
        full item horizontalCenter verticalSourceThreshold
        horizontalSourceThreshold sMin)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
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
    Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
      largeEvent ω sMin gap Kgeo Bgeo J R := by
  let hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item :=
    { first := hsrc.first
      ledger := hsrc.ledger
      source_cut := by
        simpa [hsrc.ledger.K_eq_first_sub_q] using hsrc.full_eq
      source_cut_le := by
        simpa [hsrc.ledger.K_eq_first_sub_q] using hsrc.horizon_le }
  have hendpoint :
      endpoint ω = pointAt (hcut.first + p) := by
    simpa [hcut] using hsrc.endpoint_at_ambient
  let hprov :=
    lemma710OutsideEprimeCurrentScaleSampleFullWindowSourceEndpointProvenance_of_endpointAtAmbient
      (W := W) (PrefixOK := PrefixOK) (pointAt := pointAt)
      (nSrc := nSrc) (Jsrc := Jsrc) (A := A) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (q := q) (j := j) (sourceHeight := sourceHeight)
      (firstBlock := firstBlock) (sourceSuffixes := sourceSuffixes)
      (old := old) (verticalGap := verticalGap) (p := p)
      (start := start) (full := full) (item := item)
      (endpoint := endpoint) (ω := ω)
      hfull hstart hwindow hcut hendpoint
  have hlarge :
      taoSection7Case3LargeTriangleEvent pointAt family (hcut.first + p)
        sMin := by
    simpa [hcut] using hsrc.large
  exact
    lemma710OutsideEprimeCurrentScaleSampleInputs_of_fullWindowSourceEndpointProvenance
      (W := W) (PrefixOK := PrefixOK) (pointAt := pointAt)
      (nSrc := nSrc) (Jsrc := Jsrc) (A := A) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (q := q) (j := j) (sourceHeight := sourceHeight)
      (firstBlock := firstBlock) (sourceSuffixes := sourceSuffixes)
      (old := old) (verticalGap := verticalGap) (p := p) (n := n)
      (start := start) (full := full) (item := item)
      (family := family) (C := C) (endpoint := endpoint)
      (largeEvent := largeEvent) (ω := ω)
      (horizontalCenter := horizontalCenter)
      (verticalSourceThreshold := verticalSourceThreshold)
      (horizontalSourceThreshold := horizontalSourceThreshold)
      (sMin := sMin) (M := M) (S := S) (B := B)
      (Lerr := Lerr) (Jerr := Jerr) (gap := gap)
      (CJS := CJS) (CJm := CJm) (CL := CL) (CB := CB)
      (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
      hprov hcut hbase hscale hlarge hsrc.notE hcenter hV hJ hgap0
      hCL_nonneg hCJS_nonneg hJscale hJabsorb hLscale hBscale habsorb
      hpair hold hne hanchor hsourceJ hradius hgapKB hLerrKB

/--
Build current-scale sample inputs from a selected source-cut decode packet.

This is the selected-packet counterpart of the crossing/post-room decode
wrapper.  It consumes one chosen decode packet and preserves the definitional
large/outside-`E'` sample event domain; it still does not produce the packet
from finite-PMF sample provenance.
-/
def lemma710OutsideEprimeCurrentScaleSampleInputs_of_selectedSampleDecodeData
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hwindow : q + sourceSuffixes.length < P)
    (hsel :
      Lemma710OutsideEprimeSelectedSampleDecodeData PrefixOK pointAt j
        sourceHeight firstBlock sourceSuffixes old q verticalGap p start family
        endpoint ω firstOf fullOf horizontalCenter verticalSourceThreshold
        horizontalSourceThreshold sMin)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
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
    Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
      (Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
        Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold)
      ω sMin gap Kgeo Bgeo J R :=
  lemma710OutsideEprimeCurrentScaleSampleInputs_of_sourceRunEventData
    (W := W) (PrefixOK := PrefixOK) (pointAt := pointAt)
    (nSrc := nSrc) (Jsrc := Jsrc) (A := A) (xi := xi)
    (epsilon := epsilon) (P := P) (threshold := threshold)
    (q := q) (j := j) (sourceHeight := sourceHeight)
    (firstBlock := firstBlock) (sourceSuffixes := sourceSuffixes)
    (old := old) (verticalGap := verticalGap) (p := p) (n := n)
    (start := start)
    (full :=
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (hsel.item.1 + p))
    (item := hsel.item) (family := family) (C := C) (endpoint := endpoint)
    (largeEvent :=
      Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
        Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold)
    (ω := ω)
    (horizontalCenter := horizontalCenter)
    (verticalSourceThreshold := verticalSourceThreshold)
    (horizontalSourceThreshold := horizontalSourceThreshold)
    (sMin := sMin) (M := M) (S := S) (B := B)
    (Lerr := Lerr) (Jerr := Jerr) (gap := gap)
    (CJS := CJS) (CJm := CJm) (CL := CL) (CB := CB)
    (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
    hfull hstart hwindow
    (lemma710OutsideEprimeSourceRunEventData_of_selectedSampleDecodeData hsel)
    hbase hscale hcenter hV hJ hgap0 hCL_nonneg hCJS_nonneg hJscale
    hJabsorb hLscale hBscale habsorb hpair hold hne hanchor hsourceJ
    hradius hgapKB hLerrKB

/--
Build nonempty current-scale sample inputs from a fixed-`p` source-run
candidate and anchored event-domain maps.

This is a support composition.  It still assumes the fixed-`p` candidate,
sample event membership, endpoint identification, sample clock/window
identifications, full-window provenance, scale controls, center/family data,
and final absorption inequalities.
-/
theorem lemma710OutsideEprimeCurrentScaleSampleInputs_nonempty_of_fixedPSourceRunCandidate_eventDomainMaps
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {largeEvent outsideEprimeEvent : Set Ω} {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hwindow : q + sourceSuffixes.length < P)
    (hfix :
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hmaps :
      Lemma710OutsideEprimeSampleEventDomainMaps pointAt family
        largeEvent outsideEprimeEvent firstOf fullOf p sMin start old
        horizontalCenter verticalSourceThreshold horizontalSourceThreshold)
    (hmem : ω ∈ largeEvent ∩ outsideEprimeEvent)
    (hendpoint :
      ∀ first,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        endpoint ω = pointAt (first + p))
    (hfirstOf : firstOf ω = q + item.1)
    (hfullOf : fullOf ω = full)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
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
    Nonempty
      (Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
        largeEvent ω sMin gap Kgeo Bgeo J R) := by
  rcases hfix.ledger with ⟨first, hledger⟩
  have hfirst : firstOf ω = first := by
    rw [hfirstOf]
    exact randomKSourceLedger_q_add_K_eq_first hledger
  let hevent :=
    lemma710OutsideEprimeSampleEventMembershipData_of_eventDomainMaps
      hmaps hmem hfirst hfullOf
  let hsrc :=
    lemma710OutsideEprimeSourceRunEventData_of_eventMembership
      hledger hfix.full_eq hfix.horizon_le
      (hendpoint first hledger) hevent
  exact
    ⟨lemma710OutsideEprimeCurrentScaleSampleInputs_of_sourceRunEventData
      (W := W) (PrefixOK := PrefixOK) (pointAt := pointAt)
      (nSrc := nSrc) (Jsrc := Jsrc) (A := A) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (q := q) (j := j) (sourceHeight := sourceHeight)
      (firstBlock := firstBlock) (sourceSuffixes := sourceSuffixes)
      (old := old) (verticalGap := verticalGap) (p := p) (n := n)
      (start := start) (full := full) (item := item)
      (family := family) (C := C) (endpoint := endpoint)
      (largeEvent := largeEvent) (ω := ω)
      (horizontalCenter := horizontalCenter)
      (verticalSourceThreshold := verticalSourceThreshold)
      (horizontalSourceThreshold := horizontalSourceThreshold)
      (sMin := sMin) (M := M) (S := S) (B := B)
      (Lerr := Lerr) (Jerr := Jerr) (gap := gap)
      (CJS := CJS) (CJm := CJm) (CL := CL) (CB := CB)
      (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
      hfull hstart hwindow hsrc
      hbase hscale hcenter hV hJ hgap0 hCL_nonneg hCJS_nonneg
      hJscale hJabsorb hLscale hBscale habsorb hpair hold hne hanchor
      hsourceJ hradius hgapKB hLerrKB⟩

/--
Build nonempty current-scale sample inputs for the intersection of the
definitional large-triangle and outside-`E'` sample events.

Compared with the event-domain-map composition, this removes the arbitrary
event-domain map premise while keeping the output event domain as the
outside-`E'` large-event intersection.  It still assumes event membership,
endpoint identification, clock/window identifications, the fixed-`p`
candidate, and the geometric and scale inputs.
-/
theorem lemma710OutsideEprimeCurrentScaleSampleInputs_nonempty_of_fixedPSourceRunCandidate_definitionalEvents
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hwindow : q + sourceSuffixes.length < P)
    (hfix :
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hmem :
      ω ∈
        Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
          Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold)
    (hendpoint :
      ∀ first,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        endpoint ω = pointAt (first + p))
    (hfirstOf : firstOf ω = q + item.1)
    (hfullOf : fullOf ω = full)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
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
    Nonempty
      (Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
        (Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
          Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold) ω
        sMin gap Kgeo Bgeo J R) :=
  lemma710OutsideEprimeCurrentScaleSampleInputs_nonempty_of_fixedPSourceRunCandidate_eventDomainMaps
    (largeEvent :=
      Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
        Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold)
    (outsideEprimeEvent :=
      Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold)
    hfull hstart hwindow hfix
    { large_subset := by
        intro ω hω
        exact hω.1
      outside_subset := by
        intro ω hω
        exact hω }
    ⟨hmem, hmem.2⟩ hendpoint hfirstOf hfullOf hbase hscale hcenter hV hJ hgap0
    hCL_nonneg hCJS_nonneg hJscale hJabsorb hLscale hBscale habsorb
    hpair hold hne hanchor hsourceJ hradius hgapKB hLerrKB

/--
Build nonempty current-scale sample inputs for the definitional large/outside
event from a real source-suffix crossing plus post-`p` room.

This removes the supplied `EprimeFixedPSourceRunCandidate` premise from
`lemma710OutsideEprimeCurrentScaleSampleInputs_nonempty_of_fixedPSourceRunCandidate_definitionalEvents`.
The selected random `k = item.1` and canonical full list are still existential:
callers must supply endpoint and sample-decode facts for whichever source-cut
datum the crossing/post-room producer extracts.  Event membership, full-window
source-path support, scale controls, center/family data, and absorption
inequalities remain explicit.
-/
theorem lemma710OutsideEprimeCurrentScaleSampleInputs_nonempty_of_sourceSuffixesCrossing_postRoom_definitionalEvents
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q N : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hwindow : q + sourceSuffixes.length < P)
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hcross :
      start.l + (verticalGap : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l)
    (hpost_room : N + p ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hmem :
      ω ∈
        Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
          Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold)
    (hendpoint :
      ∀ (item : ℕ × List TaoSection7RenewalPoint) first,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        endpoint ω = pointAt (first + p))
    (hfirstOf :
      ∀ item : ℕ × List TaoSection7RenewalPoint,
        Nonempty
          (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
            firstBlock sourceSuffixes old q verticalGap start p
            ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
              (item.1 + p))
            item) →
        firstOf ω = q + item.1)
    (hfullOf :
      ∀ item : ℕ × List TaoSection7RenewalPoint,
        Nonempty
          (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
            firstBlock sourceSuffixes old q verticalGap start p
            ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
              (item.1 + p))
            item) →
        fullOf ω =
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
            (item.1 + p))
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
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
    Nonempty
      (Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
        (Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
          Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold) ω
        sMin gap Kgeo Bgeo J R) := by
  rcases
    lemma710SourceCutCandidateData_nonempty_of_sourceSuffixes_crossing_at_postRoom
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (p := p) (start := start)
      hstart hpoint_q hverticalGap hNpos hNle hcross hpost_room
      hpoint_first hprefix_ok with
    ⟨item, hdata_nonempty⟩
  rcases hdata_nonempty with ⟨hdata⟩
  let hdata_nonempty :
      Nonempty
        (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
          firstBlock sourceSuffixes old q verticalGap start p
          ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
            (item.1 + p))
          item) := ⟨hdata⟩
  exact
    lemma710OutsideEprimeCurrentScaleSampleInputs_nonempty_of_fixedPSourceRunCandidate_definitionalEvents
      (W := W) (PrefixOK := PrefixOK) (pointAt := pointAt)
      (nSrc := nSrc) (Jsrc := Jsrc) (A := A) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (q := q) (j := j) (sourceHeight := sourceHeight)
      (firstBlock := firstBlock) (sourceSuffixes := sourceSuffixes)
      (old := old) (verticalGap := verticalGap) (p := p) (n := n)
      (start := start)
      (full :=
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
      (item := item) (family := family) (C := C) (endpoint := endpoint)
      (ω := ω) (firstOf := firstOf) (fullOf := fullOf)
      (horizontalCenter := horizontalCenter)
      (verticalSourceThreshold := verticalSourceThreshold)
      (horizontalSourceThreshold := horizontalSourceThreshold)
      (sMin := sMin) (M := M) (S := S) (B := B)
      (Lerr := Lerr) (Jerr := Jerr) (gap := gap)
      (CJS := CJS) (CJm := CJm) (CL := CL) (CB := CB)
      (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
      hfull hstart hwindow
      (lemma710SourceCutCandidateData_to_fixedPSourceRunCandidate hdata)
      hmem
      (fun first hledger => hendpoint item first hledger)
      (hfirstOf item hdata_nonempty)
      (hfullOf item hdata_nonempty)
      hbase hscale hcenter hV hJ hgap0 hCL_nonneg hCJS_nonneg hJscale
      hJabsorb hLscale hBscale habsorb hpair hold hne hanchor hsourceJ
      hradius hgapKB hLerrKB

/--
Build nonempty current-scale sample inputs from a real crossing plus a
source-cut-indexed sample-decode packet.

Compared with
`lemma710OutsideEprimeCurrentScaleSampleInputs_nonempty_of_sourceSuffixesCrossing_postRoom_definitionalEvents`,
this removes the separate event-membership, endpoint, `firstOf`, and `fullOf`
oracles and requires one decode packet tied to the exact source-cut witness
selected by the crossing/post-room producer.  The packet facts are still
assumptions; this is not actual finite-PMF sample-decode production.
-/
theorem lemma710OutsideEprimeCurrentScaleSampleInputs_nonempty_of_sourceSuffixesCrossing_postRoom_sampleDecodeData
    {Ω : Type*}
    {W : ℕ → Prop} {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {nSrc Jsrc A : ℕ} {xi : ZMod (3 ^ nSrc)} {epsilon : ℝ}
    {P threshold q N : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap p n : ℕ}
    {start : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point}
    {ω : Ω}
    {firstOf : Ω → ℕ}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin M S B Lerr Jerr gap CJS CJm CL CB Kgeo Bgeo J R : ℝ}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt nSrc Jsrc A xi epsilon P threshold q j sourceHeight
        firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hwindow : q + sourceSuffixes.length < P)
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hcross :
      start.l + (verticalGap : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l)
    (hpost_room : N + p ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hdecode :
      ∀ item : ℕ × List TaoSection7RenewalPoint,
        (cut :
          Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
            firstBlock sourceSuffixes old q verticalGap start p
            ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
              (item.1 + p))
            item) →
          Lemma710OutsideEprimeSampleDecodeData PrefixOK pointAt j
            sourceHeight firstBlock sourceSuffixes old q verticalGap p start
            family endpoint ω firstOf fullOf item horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold sMin cut)
    (hbase : old.Mem (pointAt q))
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
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
    Nonempty
      (Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
        (Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
          Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold) ω
        sMin gap Kgeo Bgeo J R) := by
  rcases
    lemma710SourceCutCandidateData_nonempty_of_sourceSuffixes_crossing_at_postRoom
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (p := p) (start := start)
      hstart hpoint_q hverticalGap hNpos hNle hcross hpost_room
      hpoint_first hprefix_ok with
    ⟨item, hdata_nonempty⟩
  rcases hdata_nonempty with ⟨hdata⟩
  let hsrc :=
    lemma710OutsideEprimeSourceRunEventData_of_sampleDecodeData
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (p := p) (start := start)
      (family := family) (endpoint := endpoint) (ω := ω)
      (firstOf := firstOf) (fullOf := fullOf) (item := item)
      (horizontalCenter := horizontalCenter)
      (verticalSourceThreshold := verticalSourceThreshold)
      (horizontalSourceThreshold := horizontalSourceThreshold)
      (sMin := sMin) (cut := hdata) (hdecode item hdata)
  exact
    ⟨lemma710OutsideEprimeCurrentScaleSampleInputs_of_sourceRunEventData
      (W := W) (PrefixOK := PrefixOK) (pointAt := pointAt)
      (nSrc := nSrc) (Jsrc := Jsrc) (A := A) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (q := q) (j := j) (sourceHeight := sourceHeight)
      (firstBlock := firstBlock) (sourceSuffixes := sourceSuffixes)
      (old := old) (verticalGap := verticalGap) (p := p) (n := n)
      (start := start)
      (full :=
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
      (item := item) (family := family) (C := C) (endpoint := endpoint)
      (largeEvent :=
        Lemma710LargeTriangleSampleEvent pointAt family firstOf p sMin ∩
          Lemma710OutsideEprimeSampleEvent fullOf start old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold)
      (ω := ω)
      (horizontalCenter := horizontalCenter)
      (verticalSourceThreshold := verticalSourceThreshold)
      (horizontalSourceThreshold := horizontalSourceThreshold)
      (sMin := sMin) (M := M) (S := S) (B := B)
      (Lerr := Lerr) (Jerr := Jerr) (gap := gap)
      (CJS := CJS) (CJm := CJm) (CL := CL) (CB := CB)
      (Kgeo := Kgeo) (Bgeo := Bgeo) (J := J) (R := R)
      hfull hstart hwindow hsrc
      hbase hscale hcenter hV hJ hgap0 hCL_nonneg hCJS_nonneg
      hJscale hJabsorb hLscale hBscale habsorb hpair hold hne hanchor
      hsourceJ hradius hgapKB hLerrKB⟩

theorem lemma710OutsideEprimeSourceHitExists_of_currentScaleSampleInputs
    {Ω : Type*}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point} {largeEvent : Set Ω} {ω : Ω}
    {sMin gap Kgeo Bgeo J R : ℝ}
    (hsample : ω ∈ largeEvent)
    (h :
      Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
        largeEvent ω sMin gap Kgeo Bgeo J R) :
    ∃ new : TaoSection7Triangle,
      Lemma710OutsideEprimeSourceHitData family old new (endpoint ω)
        sMin gap Kgeo Bgeo J R ∧
        anchor old new ∈ C :=
  lemma710OutsideEprimeSourceHitExists_of_currentScaleSample
    h.cut h.point_source h.base_mem h.scale hsample (fun _ => h.large)
    h.endpoint_eq h.notE h.center_eq h.vertical_threshold_le
    h.horizontal_threshold_le h.gap_nonneg h.CL_nonneg h.CJS_nonneg
    h.Jerr_scale h.Jerr_absorb h.Lerr_scale h.B_scale h.final_absorb
    h.pairwiseDisjoint h.old_mem_family h.new_ne_old h.anchor_mem
    h.sourceJ h.radius_absorbs h.gap_absorbs h.Lerr_absorbs

/--
Endpoint-near-center membership for a current-scale sample input gives the
post-`k` one-center tail predicate for the selected source cut.

This is deterministic event-map plumbing: it does not produce the sample-input
record or endpoint-near-center membership, but rewrites the sample endpoint
through the checked source-cut endpoint and then uses the existing source-cut
split into the selected stopped prefix and length-`p` tail.
-/
theorem lemma710PostKEndpointNearCenter_of_currentScaleSampleInputs_endpointNearCenter
    {Ω : Type*}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point} {largeEvent : Set Ω} {ω : Ω}
    {sMin gap Kgeo Bgeo J R : ℝ} {c : TaoSection7Point}
    (h :
      Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
        largeEvent ω sMin gap Kgeo Bgeo J R)
    (hnear : (endpoint ω).distSq c ≤ R ^ 2) :
    ∃ tail : List TaoSection7RenewalPoint,
      h.full = h.item.2 ++ tail ∧
        Lemma710PostKEndpointNearCenter h.start h.p R c h.item.2 tail := by
  have hendpoint_source :
      endpoint ω =
        (taoSection7RenewalPathPoint h.start h.full h.full.length).toPoint := by
    calc
      endpoint ω = h.pointAt (h.cut.first + h.p) := h.endpoint_eq
      _ =
          (taoSection7RenewalPathPoint h.start h.full h.full.length).toPoint :=
        lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
          h.cut h.point_source
  have hsource_near :
      Lemma710SourceEndpointNearCenter h.start R c h.full := by
    simpa [Lemma710SourceEndpointNearCenter, hendpoint_source] using hnear
  exact lemma710SourceCutCandidateData_postKEndpointNearCenter hsource_near
    h.cut

/--
Current-scale outside-`E'` sample inputs give the source-side one-center hit
and the source-cut data for the selected full list.

This theorem deliberately targets the lighter source-cut/near-center facts
stored in the sample-input record.  It does not reconstruct full-window source
path provenance and does not prove that the sample-input record itself is
available from the finite PMF.
-/
theorem lemma710OutsideEprimeCurrentScaleSampleInputs_to_sourceEndpointCenterCut
    {Ω : Type*}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {endpoint : Ω → TaoSection7Point} {largeEvent : Set Ω} {ω : Ω}
    {sMin gap Kgeo Bgeo J R : ℝ}
    (hsample : ω ∈ largeEvent)
    (h :
      Lemma710OutsideEprimeCurrentScaleSampleInputs family old C endpoint
        largeEvent ω sMin gap Kgeo Bgeo J R) :
    ∃ c, c ∈ C ∧
      Lemma710SourceEndpointNearCenter h.start R c h.full ∧
        h.item ∈
          randomKVerticalFirstPassagePrefixFinset h.start h.verticalGap
            h.sourceSuffixes ∧
          Nonempty
            (Lemma710SourceCutCandidateData h.PrefixOK h.pointAt h.j
              h.sourceHeight h.firstBlock h.sourceSuffixes old h.q
              h.verticalGap h.start h.p h.full h.item) := by
  rcases lemma710OutsideEprimeSourceHitExists_of_currentScaleSampleInputs
      hsample h with
    ⟨new, hhit, hanchor_mem⟩
  rcases lemma710_outsideEprimeSourceHitData_to_center_distSq hhit with
    ⟨center, hcenter_eq, hdist⟩
  refine ⟨center.point, ?_, ?_, ?_, ⟨h.cut⟩⟩
  · simpa [Center.point, hcenter_eq] using hanchor_mem
  · have hendpoint_source :
        endpoint ω =
          (taoSection7RenewalPathPoint h.start h.full h.full.length).toPoint := by
      calc
        endpoint ω = h.pointAt (h.cut.first + h.p) := h.endpoint_eq
        _ =
            (taoSection7RenewalPathPoint h.start h.full h.full.length).toPoint :=
          lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
            h.cut h.point_source
    simpa [Lemma710SourceEndpointNearCenter, hendpoint_source] using hdist
  · exact randomKSourceLedger_mem_verticalFirstPassagePrefixFinset h.cut.ledger

/--
Five-way exceptional-event cover used by the `(7.61)` budget.

The first-passage vertical/horizontal predicates are the `(7.48)` inputs; the
post-`k` vertical/horizontal predicates are the Lemma 2.2 tail inputs after the
source/tail routing layer.  `ResidualBad` is for source/provenance/headroom
failures that are paid separately.
-/
def Lemma710EprimeExceptionalUnion
    (ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
      FirstPassageHorizontalBad PostKHorizontalTailBad :
        List TaoSection7RenewalPoint → Prop)
    (full : List TaoSection7RenewalPoint) : Prop :=
  ResidualBad full ∨
    FirstPassageVerticalBad full ∨
      PostKVerticalTailBad full ∨
        FirstPassageHorizontalBad full ∨
          PostKHorizontalTailBad full

/--
Minimal event-mass algebra needed for the `(7.61)` union bound.

This is deliberately abstract: later finite-PMF, stopped-prefix, or source-law
instantiations can supply `eventMass`, monotonicity, and binary subadditivity
without changing the exceptional-event budget theorem.
-/
structure Lemma710EventMassAlgebra
    (eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ) : Prop where
  mono :
    ∀ {E F : List TaoSection7RenewalPoint → Prop},
      (∀ full, E full → F full) → eventMass E ≤ eventMass F
  union_le_add :
    ∀ E F : List TaoSection7RenewalPoint → Prop,
      eventMass (fun full => E full ∨ F full) ≤
        eventMass E + eventMass F

theorem lemma710EprimeExceptionalUnion_mass_le
    {eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ}
    (hmass : Lemma710EventMassAlgebra eventMass)
    (ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
      FirstPassageHorizontalBad PostKHorizontalTailBad :
        List TaoSection7RenewalPoint → Prop) :
    eventMass
        (Lemma710EprimeExceptionalUnion ResidualBad FirstPassageVerticalBad
          PostKVerticalTailBad FirstPassageHorizontalBad
          PostKHorizontalTailBad)
      ≤ eventMass ResidualBad +
        eventMass FirstPassageVerticalBad +
        eventMass PostKVerticalTailBad +
        eventMass FirstPassageHorizontalBad +
        eventMass PostKHorizontalTailBad := by
  let Rest₁ : List TaoSection7RenewalPoint → Prop :=
    fun full =>
      FirstPassageVerticalBad full ∨
        PostKVerticalTailBad full ∨
          FirstPassageHorizontalBad full ∨ PostKHorizontalTailBad full
  let Rest₂ : List TaoSection7RenewalPoint → Prop :=
    fun full =>
      PostKVerticalTailBad full ∨
        FirstPassageHorizontalBad full ∨ PostKHorizontalTailBad full
  let Rest₃ : List TaoSection7RenewalPoint → Prop :=
    fun full => FirstPassageHorizontalBad full ∨ PostKHorizontalTailBad full
  have h0 :
      eventMass
          (Lemma710EprimeExceptionalUnion ResidualBad FirstPassageVerticalBad
            PostKVerticalTailBad FirstPassageHorizontalBad
            PostKHorizontalTailBad)
        ≤ eventMass ResidualBad + eventMass Rest₁ := by
    simpa [Lemma710EprimeExceptionalUnion, Rest₁] using
      hmass.union_le_add ResidualBad Rest₁
  have h1 :
      eventMass Rest₁ ≤
        eventMass FirstPassageVerticalBad + eventMass Rest₂ := by
    simpa [Rest₁, Rest₂] using
      hmass.union_le_add FirstPassageVerticalBad Rest₂
  have h2 :
      eventMass Rest₂ ≤
        eventMass PostKVerticalTailBad + eventMass Rest₃ := by
    simpa [Rest₂, Rest₃] using
      hmass.union_le_add PostKVerticalTailBad Rest₃
  have h3 :
      eventMass Rest₃ ≤
        eventMass FirstPassageHorizontalBad +
          eventMass PostKHorizontalTailBad := by
    simpa [Rest₃] using
      hmass.union_le_add FirstPassageHorizontalBad PostKHorizontalTailBad
  linarith

/--
Inputs for the Lemma 7.10 exceptional-event estimate `(7.61)`.

The record carries the stopped-tail Lemma 2.2 input next to the two post-`k`
mass fields, but it does not derive those full-run mass inequalities from the
stopped-tail input.  That mass-link producer is a separate open gate.  The
first-passage pieces remain separate `(7.48)` marginal inputs.  The final
comparison field is the place for Tao's scale assumptions and absorption of
the exponential tails into the displayed `(7.61)` budget.
-/
structure Lemma710EprimeProbabilityInputs
    (p : ℕ)
    (VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ)
    (eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ)
    (ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
      FirstPassageHorizontalBad PostKHorizontalTailBad :
        List TaoSection7RenewalPoint → Prop)
    (targetBudget residualBudget firstPassageVerticalBudget
      postKVerticalBudget firstPassageHorizontalBudget postKHorizontalBudget :
        ℝ) : Prop where
  mass_algebra : Lemma710EventMassAlgebra eventMass
  event_subset :
    ∀ full,
      EprimeSourceEvent start old horizontalCenter verticalSourceThreshold
          horizontalSourceThreshold full →
        Lemma710EprimeExceptionalUnion ResidualBad FirstPassageVerticalBad
          PostKVerticalTailBad FirstPassageHorizontalBad
          PostKHorizontalTailBad full
  stopped_tail_input :
    TaoSection7Lemma710EprimeStoppedTailInput p VerticalTail HorizontalTail
      postKVerticalBudget postKHorizontalBudget
  residual_mass_le :
    eventMass ResidualBad ≤ residualBudget
  first_passage_vertical_748_le :
    eventMass FirstPassageVerticalBad ≤ firstPassageVerticalBudget
  postk_vertical_lemma22_le :
    eventMass PostKVerticalTailBad ≤ postKVerticalBudget
  first_passage_horizontal_748_le :
    eventMass FirstPassageHorizontalBad ≤ firstPassageHorizontalBudget
  postk_horizontal_lemma22_le :
    eventMass PostKHorizontalTailBad ≤ postKHorizontalBudget
  parameter_comparisons_le :
    residualBudget + firstPassageVerticalBudget + postKVerticalBudget +
        firstPassageHorizontalBudget + postKHorizontalBudget ≤ targetBudget

/-- Stopped-prefix/post-`k` cylinder mass for one tail predicate. -/
noncomputable def lemma710PostKStoppedCylinderMass
    (p : ℕ)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (TailBad :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel TailBad] : ℝ :=
  ∑ item ∈ S,
    ∑' tail : List TaoSection7RenewalPoint,
      if TailBad item.2 tail then
        (taoSection7HoldListPMF (item.1 + p) (item.2 ++ tail)).toReal
      else 0

/--
Named source-law/cylinder mass control for the post-`k` bad events in `(7.61)`.

This is the probability-space/source-law gate: once the full-run post-`k` bad
event is covered by stopped-prefix cylinders, this record bounds its
`eventMass` by the corresponding cylinder sum.  It is intentionally separate
from the stopped-tail summation theorem.
-/
structure Lemma710EprimePostKSourceCylinderMassControl
    (p : ℕ)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    (eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ)
    (PostKVerticalTailBad PostKHorizontalTailBad :
      List TaoSection7RenewalPoint → Prop) : Prop where
  vertical_event_mass_le :
    (∀ full, PostKVerticalTailBad full →
      ∃ item, item ∈ S ∧
        ∃ tail : List TaoSection7RenewalPoint,
          full = item.2 ++ tail ∧ VerticalTail item.2 tail) →
      eventMass PostKVerticalTailBad ≤
        lemma710PostKStoppedCylinderMass p S VerticalTail
  horizontal_event_mass_le :
    (∀ full, PostKHorizontalTailBad full →
      ∃ item, item ∈ S ∧
        ∃ tail : List TaoSection7RenewalPoint,
          full = item.2 ++ tail ∧ HorizontalTail item.2 tail) →
      eventMass PostKHorizontalTailBad ≤
        lemma710PostKStoppedCylinderMass p S HorizontalTail

/--
Vertical full-run post-`k` bad events are covered by stopped cylinders once
the vertical `E'` source coverage is available and residual cases are excluded.
-/
theorem lemma710_postk_vertical_cylinder_cover_of_sourceCoverage
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {sourceThreshold tailThreshold : ℝ} {p : ℕ}
    {ResidualBad PostKVerticalTailBad :
      List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {VerticalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    (hcoverage :
      EprimeVerticalSourceCoverage PrefixOK start old sourceThreshold
        tailThreshold p ResidualBad S)
    (hsource :
      ∀ full, PostKVerticalTailBad full →
        EprimeVerticalSourceEvent start old sourceThreshold full)
    (hnot_residual :
      ∀ full, PostKVerticalTailBad full → ¬ ResidualBad full)
    (htail :
      ∀ pre tail,
        EprimeVerticalTailEvent start p tailThreshold pre tail →
          VerticalTail pre tail) :
    ∀ full, PostKVerticalTailBad full →
      ∃ item, item ∈ S ∧
        ∃ tail : List TaoSection7RenewalPoint,
          full = item.2 ++ tail ∧ VerticalTail item.2 tail := by
  intro full hbad
  rcases hcoverage.cover_or_residual full (hsource full hbad) with hres | hhit
  · exact False.elim ((hnot_residual full hbad) hres)
  · rcases hhit with ⟨item, hitem, tail, hfull, htail_event⟩
    exact ⟨item, hitem, tail, hfull, htail item.2 tail htail_event⟩

/--
Horizontal full-run post-`k` bad events are covered by stopped cylinders once
the horizontal `E'` source coverage is available and residual cases are
excluded.
-/
theorem lemma710_postk_horizontal_cylinder_cover_of_sourceCoverage
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {start : TaoSection7RenewalPoint} {horizontalCenter : ℝ}
    {sourceThreshold tailThreshold : ℝ} {p : ℕ}
    {ResidualBad PostKHorizontalTailBad :
      List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    (hcoverage :
      EprimeHorizontalSourceCoverage PrefixOK start horizontalCenter
        sourceThreshold tailThreshold p ResidualBad S)
    (hsource :
      ∀ full, PostKHorizontalTailBad full →
        EprimeHorizontalSourceEvent start horizontalCenter sourceThreshold full)
    (hnot_residual :
      ∀ full, PostKHorizontalTailBad full → ¬ ResidualBad full)
    (htail :
      ∀ pre tail,
        EprimeHorizontalTailEvent start p tailThreshold pre tail →
          HorizontalTail pre tail) :
    ∀ full, PostKHorizontalTailBad full →
      ∃ item, item ∈ S ∧
        ∃ tail : List TaoSection7RenewalPoint,
          full = item.2 ++ tail ∧ HorizontalTail item.2 tail := by
  intro full hbad
  rcases hcoverage.cover_or_residual full (hsource full hbad) with hres | hhit
  · exact False.elim ((hnot_residual full hbad) hres)
  · rcases hhit with ⟨item, hitem, tail, hfull, htail_event⟩
    exact ⟨item, hitem, tail, hfull, htail item.2 tail htail_event⟩

/--
Mass-link data from stopped-tail Lemma 2.2 inputs to the full-run post-`k`
bad-event predicates used by the `(7.61)` union-bound socket.

The two event-mass-to-cylinder fields are the source/cylinder identification
obligations: they say that the full-run post-`k` bad events are covered by the
stopped-prefix family plus the corresponding tail predicate.  The checked
theorems below then apply the existing variable-prefix stopped-tail summation
bridge.
-/
structure Lemma710EprimePostKMassLinkInputs
    (p : ℕ)
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    (eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ)
    (PostKVerticalTailBad PostKHorizontalTailBad :
      List TaoSection7RenewalPoint → Prop)
    (bL bJ : ℝ) : Prop where
  prefixes : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S
  stopped_tail_input :
    TaoSection7Lemma710EprimeStoppedTailInput p VerticalTail HorizontalTail
      bL bJ
  vertical_budget_nonneg : 0 ≤ bL
  horizontal_budget_nonneg : 0 ≤ bJ
  vertical_event_mass_le_cylinder :
    eventMass PostKVerticalTailBad ≤
      lemma710PostKStoppedCylinderMass p S VerticalTail
  horizontal_event_mass_le_cylinder :
    eventMass PostKHorizontalTailBad ≤
      lemma710PostKStoppedCylinderMass p S HorizontalTail

theorem lemma710EprimePostKMassLinkInputs_of_sourceCoverage
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {ResidualBad PostKVerticalTailBad PostKHorizontalTailBad :
      List TaoSection7RenewalPoint → Prop}
    {eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ}
    {bL bJ : ℝ}
    (hprefixes : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (htails :
      TaoSection7Lemma710EprimeStoppedTailInput p VerticalTail HorizontalTail
        bL bJ)
    (hbL : 0 ≤ bL) (hbJ : 0 ≤ bJ)
    (hsourceLaw :
      Lemma710EprimePostKSourceCylinderMassControl p S VerticalTail
        HorizontalTail eventMass PostKVerticalTailBad PostKHorizontalTailBad)
    (hverticalCoverage :
      EprimeVerticalSourceCoverage PrefixOK start old verticalSourceThreshold
        verticalTailThreshold p ResidualBad S)
    (hhorizontalCoverage :
      EprimeHorizontalSourceCoverage PrefixOK start horizontalCenter
        horizontalSourceThreshold horizontalTailThreshold p ResidualBad S)
    (hvertical_source :
      ∀ full, PostKVerticalTailBad full →
        EprimeVerticalSourceEvent start old verticalSourceThreshold full)
    (hhorizontal_source :
      ∀ full, PostKHorizontalTailBad full →
        EprimeHorizontalSourceEvent start horizontalCenter
          horizontalSourceThreshold full)
    (hvertical_not_residual :
      ∀ full, PostKVerticalTailBad full → ¬ ResidualBad full)
    (hhorizontal_not_residual :
      ∀ full, PostKHorizontalTailBad full → ¬ ResidualBad full)
    (hvertical_tail :
      ∀ pre tail,
        EprimeVerticalTailEvent start p verticalTailThreshold pre tail →
          VerticalTail pre tail)
    (hhorizontal_tail :
      ∀ pre tail,
        EprimeHorizontalTailEvent start p horizontalTailThreshold pre tail →
          HorizontalTail pre tail) :
    Lemma710EprimePostKMassLinkInputs p PrefixOK S VerticalTail
      HorizontalTail eventMass PostKVerticalTailBad PostKHorizontalTailBad
      bL bJ where
  prefixes := hprefixes
  stopped_tail_input := htails
  vertical_budget_nonneg := hbL
  horizontal_budget_nonneg := hbJ
  vertical_event_mass_le_cylinder :=
    hsourceLaw.vertical_event_mass_le
      (lemma710_postk_vertical_cylinder_cover_of_sourceCoverage
        hverticalCoverage hvertical_source hvertical_not_residual
        hvertical_tail)
  horizontal_event_mass_le_cylinder :=
    hsourceLaw.horizontal_event_mass_le
      (lemma710_postk_horizontal_cylinder_cover_of_sourceCoverage
        hhorizontalCoverage hhorizontal_source hhorizontal_not_residual
        hhorizontal_tail)

theorem lemma710_postk_vertical_mass_le_of_stoppedTailInput
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    {eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ}
    {PostKVerticalTailBad PostKHorizontalTailBad :
      List TaoSection7RenewalPoint → Prop}
    {bL bJ : ℝ}
    (h :
      Lemma710EprimePostKMassLinkInputs p PrefixOK S VerticalTail
        HorizontalTail eventMass PostKVerticalTailBad PostKHorizontalTailBad
        bL bJ) :
    eventMass PostKVerticalTailBad ≤ bL :=
  le_trans h.vertical_event_mass_le_cylinder
    (by
      simpa [lemma710PostKStoppedCylinderMass] using
        taoSection7StoppedHoldVariablePrefixTail_tsum_le
          (p := p) (PrefixOK := PrefixOK) S h.prefixes VerticalTail
          h.vertical_budget_nonneg h.stopped_tail_input.vertical_tail)

theorem lemma710_postk_horizontal_mass_le_of_stoppedTailInput
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    {eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ}
    {PostKVerticalTailBad PostKHorizontalTailBad :
      List TaoSection7RenewalPoint → Prop}
    {bL bJ : ℝ}
    (h :
      Lemma710EprimePostKMassLinkInputs p PrefixOK S VerticalTail
        HorizontalTail eventMass PostKVerticalTailBad PostKHorizontalTailBad
        bL bJ) :
    eventMass PostKHorizontalTailBad ≤ bJ :=
  le_trans h.horizontal_event_mass_le_cylinder
    (by
      simpa [lemma710PostKStoppedCylinderMass] using
        taoSection7StoppedHoldVariablePrefixTail_tsum_le
          (p := p) (PrefixOK := PrefixOK) S h.prefixes HorizontalTail
          h.horizontal_budget_nonneg h.stopped_tail_input.horizontal_tail)

/--
Variant of the `(7.61)` input surface where the post-`k` mass fields are
supplied through the checked stopped-tail mass-link adapter.

This removes the two explicit post-`k` mass inequalities from
`Lemma710EprimeProbabilityInputs`; the remaining open producer obligations are
the event-mass-to-cylinder coverage fields inside `postk_mass_link`, the
first-passage `(7.48)` bounds, residual mass, and parameter absorption.
-/
structure Lemma710EprimeProbabilityWithPostKMassLinkInputs
    (p : ℕ)
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ)
    (eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ)
    (ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
      FirstPassageHorizontalBad PostKHorizontalTailBad :
        List TaoSection7RenewalPoint → Prop)
    (targetBudget residualBudget firstPassageVerticalBudget
      postKVerticalBudget firstPassageHorizontalBudget postKHorizontalBudget :
        ℝ) : Prop where
  mass_algebra : Lemma710EventMassAlgebra eventMass
  event_subset :
    ∀ full,
      EprimeSourceEvent start old horizontalCenter verticalSourceThreshold
          horizontalSourceThreshold full →
        Lemma710EprimeExceptionalUnion ResidualBad FirstPassageVerticalBad
          PostKVerticalTailBad FirstPassageHorizontalBad
          PostKHorizontalTailBad full
  postk_mass_link :
    Lemma710EprimePostKMassLinkInputs p PrefixOK S VerticalTail
      HorizontalTail eventMass PostKVerticalTailBad PostKHorizontalTailBad
      postKVerticalBudget postKHorizontalBudget
  residual_mass_le :
    eventMass ResidualBad ≤ residualBudget
  first_passage_vertical_748_le :
    eventMass FirstPassageVerticalBad ≤ firstPassageVerticalBudget
  first_passage_horizontal_748_le :
    eventMass FirstPassageHorizontalBad ≤ firstPassageHorizontalBudget
  parameter_comparisons_le :
    residualBudget + firstPassageVerticalBudget + postKVerticalBudget +
        firstPassageHorizontalBudget + postKHorizontalBudget ≤ targetBudget

theorem lemma710_eprime_probability_bound_761
    {p : ℕ}
    {VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ}
    {eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ}
    {ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
      FirstPassageHorizontalBad PostKHorizontalTailBad :
        List TaoSection7RenewalPoint → Prop}
    {targetBudget residualBudget firstPassageVerticalBudget
      postKVerticalBudget firstPassageHorizontalBudget postKHorizontalBudget :
        ℝ}
    (h :
      Lemma710EprimeProbabilityInputs p VerticalTail HorizontalTail start old
        horizontalCenter verticalSourceThreshold horizontalSourceThreshold
        eventMass ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
        FirstPassageHorizontalBad PostKHorizontalTailBad targetBudget
        residualBudget firstPassageVerticalBudget postKVerticalBudget
        firstPassageHorizontalBudget postKHorizontalBudget) :
    eventMass
        (EprimeSourceEvent start old horizontalCenter verticalSourceThreshold
          horizontalSourceThreshold)
      ≤ targetBudget := by
  calc
    eventMass
        (EprimeSourceEvent start old horizontalCenter verticalSourceThreshold
          horizontalSourceThreshold)
        ≤
      eventMass
        (Lemma710EprimeExceptionalUnion ResidualBad FirstPassageVerticalBad
          PostKVerticalTailBad FirstPassageHorizontalBad
          PostKHorizontalTailBad) := h.mass_algebra.mono h.event_subset
    _ ≤ eventMass ResidualBad +
        eventMass FirstPassageVerticalBad +
        eventMass PostKVerticalTailBad +
        eventMass FirstPassageHorizontalBad +
        eventMass PostKHorizontalTailBad :=
      lemma710EprimeExceptionalUnion_mass_le h.mass_algebra
        ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
        FirstPassageHorizontalBad PostKHorizontalTailBad
    _ ≤ residualBudget + firstPassageVerticalBudget + postKVerticalBudget +
        firstPassageHorizontalBudget + postKHorizontalBudget := by
      linarith [h.residual_mass_le, h.first_passage_vertical_748_le,
        h.postk_vertical_lemma22_le, h.first_passage_horizontal_748_le,
        h.postk_horizontal_lemma22_le]
    _ ≤ targetBudget := h.parameter_comparisons_le

theorem lemma710_eprime_probability_bound_761_of_postkMassLink
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {VerticalTail HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel VerticalTail] [DecidableRel HorizontalTail]
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ}
    {eventMass : (List TaoSection7RenewalPoint → Prop) → ℝ}
    {ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
      FirstPassageHorizontalBad PostKHorizontalTailBad :
        List TaoSection7RenewalPoint → Prop}
    {targetBudget residualBudget firstPassageVerticalBudget
      postKVerticalBudget firstPassageHorizontalBudget postKHorizontalBudget :
        ℝ}
    (h :
      Lemma710EprimeProbabilityWithPostKMassLinkInputs p PrefixOK S
        VerticalTail HorizontalTail start old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold eventMass
        ResidualBad FirstPassageVerticalBad PostKVerticalTailBad
        FirstPassageHorizontalBad PostKHorizontalTailBad targetBudget
        residualBudget firstPassageVerticalBudget postKVerticalBudget
        firstPassageHorizontalBudget postKHorizontalBudget) :
    eventMass
        (EprimeSourceEvent start old horizontalCenter verticalSourceThreshold
          horizontalSourceThreshold)
      ≤ targetBudget :=
  lemma710_eprime_probability_bound_761
    { mass_algebra := h.mass_algebra
      event_subset := h.event_subset
      stopped_tail_input := h.postk_mass_link.stopped_tail_input
      residual_mass_le := h.residual_mass_le
      first_passage_vertical_748_le := h.first_passage_vertical_748_le
      postk_vertical_lemma22_le :=
        lemma710_postk_vertical_mass_le_of_stoppedTailInput h.postk_mass_link
      first_passage_horizontal_748_le := h.first_passage_horizontal_748_le
      postk_horizontal_lemma22_le :=
        lemma710_postk_horizontal_mass_le_of_stoppedTailInput h.postk_mass_link
      parameter_comparisons_le := h.parameter_comparisons_le }

end TaoSection7Lemma710

end Tao
end Erdos1135SecondScale
