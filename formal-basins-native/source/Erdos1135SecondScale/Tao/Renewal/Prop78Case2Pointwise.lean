/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Prop78Case2EndpointSplit
import Erdos1135SecondScale.Tao.Renewal.Prop78Case2Geometry

/-!
# Proposition 7.8 Case 2 Pointwise Endpoint Bounds

This leaf gives every supported canonical endpoint the ordinary previous-tail
bound.  On the strict localized window, the active-cover collar and endpoint
split improve that bound by the required half-discount.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

/-- Ordinary previous-tail bound for every positive relative endpoint.

This includes endpoints with horizontal displacement at least `m`: saturated
subtraction makes their inverse-power factor equal to one.
-/
theorem taoSection7SourceActualQ_relativeEndpoint_le_case1InvPow_mul_qmPrev
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {start : TaoSection7RenewalPoint} {r : ℕ+} {ell : ℤ}
    (hstart : taoSection7QmBoundary (n / 2) m start) :
    taoSection7SourceActualQ n xi epsilon
        (lemma77RenewalPointOfRelativeEndpoint start ((r : ℕ), ell)) ≤
      taoSection7Case1InvPow A m r *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  let h : TaoSection7RenewalPoint := { j := r, l := ell }
  have habs :
      lemma77RenewalPointOfRelativeEndpoint start ((r : ℕ), ell) =
        start + h := by
    ext
    · apply PNat.eq
      simp [h]
    · simp [h]
  rw [habs]
  simpa [h] using
    (taoSection7SourceActualQ_add_hold_le_case1InvPow_mul_qmPrev
      (n := n) (A := A) (m := m) (xi := xi)
      (epsilon := epsilon) hepsilon hstart h)

/-- On the canonical localized endpoint window, the active-cover collar turns
the ordinary endpoint majorant into the repaired Case 2 half-discount. -/
theorem exists_taoSection7Prop78_case2_localizedEndpoint_discounted_threshold
    (B : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (A : ℕ) :
    ∃ C : ℕ,
      ∀ n : ℕ, ∀ xi : ZMod (3 ^ n),
      ∀ hactive : TaoSection7Prop78ActiveCoverData n xi epsilon,
      ∀ m ≥ C,
      ∀ Delta : TaoSection7Triangle, Delta ∈ hactive.family →
      ∀ start : TaoSection7RenewalPoint,
      ∀ s : ℕ, ∀ r : ℕ+, ∀ ell : ℤ,
        taoSection7QmBoundary (n / 2) m start →
        Delta.Mem start.toPoint →
        Delta.verticalDepth start.toPoint = (s : ℤ) →
        (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m →
        ((r : ℕ), ell) ∈ lemma77CanonicalLocalizedEndpointEvent s B →
        lemma77CanonicalFirstPassageEndpointPMF
            start s ((r : ℕ), ell) ≠ 0 →
        taoSection7SourceActualQ n xi epsilon
            (lemma77RenewalPointOfRelativeEndpoint
              start ((r : ℕ), ell)) ≤
          Real.exp (-(epsilon ^ 3 / 2)) *
            taoSection7Case1InvPow A m r *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  obtain ⟨Csplit, hsplit⟩ :=
    exists_taoSection7Prop78_case2_endpointSplit_uniform A hepsilon
  obtain ⟨C, hroom⟩ :=
    exists_taoSection7Prop78_localizedHorizontal_room_threshold B Csplit
  refine ⟨C, ?_⟩
  intro n xi hactive m hm Delta hDelta start s r ell hboundary hstart
    hdepth hnear hlocalized hne
  let endpoint :=
    lemma77RenewalPointOfRelativeEndpoint start ((r : ℕ), ell)
  have hj : (endpoint.j : ℕ) = (start.j : ℕ) + (r : ℕ) := by
    simp [endpoint]
  have hsupport :=
    lemma77CanonicalFirstPassageEndpointPMF_nonzero_support hne
  have hroom' := hroom m hm s (r : ℕ) hnear hlocalized.1
  have hr : (r : ℕ) < m := hroom'.1
  have hmargin : Csplit ≤ m - (r : ℕ) := hroom'.2
  have hlocalBoundary :
      taoSection7QmBoundary (n / 2) (m - (r : ℕ)) endpoint :=
    taoSection7QmBoundary_of_horizontalAdvance hboundary hj hr
  have hDomain : taoSection7SourcePointInDomain (n / 2) endpoint.toPoint :=
    taoSection7QmBoundary_toPoint_sourceDomain hlocalBoundary
  have hwhite : taoSection7SourceActualW n xi epsilon endpoint := by
    exact taoSection7SourceActualW_of_localizedEndpoint_activeCover
      hactive hDelta hstart hdepth hlocalized hsupport.2 hDomain hcollar
  rcases hsplit n xi m (r : ℕ) start endpoint hboundary hj with
    hover | hsmall | hnotWhite | hdiscount
  · omega
  · omega
  · exact (hnotWhite hwhite).elim
  · have hmono :
        taoSection7SourceActualQmAtCutoff
            n A (m - (r : ℕ) - 1) xi epsilon ≤
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon :=
      taoSection7SourceActualQmAtCutoff_mono_of_le hepsilon.le (by omega)
    have hfactor :
        0 ≤ Real.exp (-(epsilon ^ 3 / 2)) *
          ((((m - (r : ℕ) : ℕ) : ℝ) ^ A)⁻¹) := by positivity
    calc
      taoSection7SourceActualQ n xi epsilon endpoint ≤
          Real.exp (-(epsilon ^ 3 / 2)) *
            ((((m - (r : ℕ) : ℕ) : ℝ) ^ A)⁻¹) *
            taoSection7SourceActualQmAtCutoff
              n A (m - (r : ℕ) - 1) xi epsilon := hdiscount
      _ ≤ Real.exp (-(epsilon ^ 3 / 2)) *
            ((((m - (r : ℕ) : ℕ) : ℝ) ^ A)⁻¹) *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon :=
        mul_le_mul_of_nonneg_left hmono hfactor
      _ = Real.exp (-(epsilon ^ 3 / 2)) *
            taoSection7Case1InvPow A m r *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
        have hmax : max (m - (r : ℕ)) 1 = m - (r : ℕ) := by omega
        simp [taoSection7Case1InvPow, hmax, inv_pow]

end

end Tao
end Erdos1135SecondScale
