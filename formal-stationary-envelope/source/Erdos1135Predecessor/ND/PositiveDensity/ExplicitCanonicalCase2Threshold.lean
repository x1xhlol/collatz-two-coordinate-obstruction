/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCase2Moment
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCollar
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2Expectation

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77

open scoped BigOperators

noncomputable section

theorem explicitRenewal_localized_room {B C m s r : ℕ}
    (hm : 2 * (C + B ^ 2 + 1) + 4 ≤ m)
    (hs : (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m)
    (hh : |lemma77CenteredHorizontalDisplacement s r| <
      (B : ℝ) * Real.sqrt (1 + (s : ℝ))) :
    r < m ∧ C ≤ m - r := by
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (by omega : 4 ≤ m)
  have hlog : (1 : ℝ) ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hm4
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    norm_num at h2 h
    linarith
  have hlinear : 2 * (C + B ^ 2 + 1) ≤ m := by omega
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlogSq : (1 : ℝ) ≤ Real.log (m : ℝ) ^ 2 := by nlinarith
  have hthreshold : taoSection7Prop78BoundaryThreshold m ≤ (m : ℝ) := by
    unfold taoSection7Prop78BoundaryThreshold
    exact div_le_self hm0 hlogSq
  have hsm : (s : ℝ) ≤ m := hs.trans hthreshold
  have hcenter : (r : ℝ) - (s : ℝ) / 4 <
      (B : ℝ) * Real.sqrt (1 + (s : ℝ)) :=
    (le_abs_self _).trans_lt (by simpa [lemma77CenteredHorizontalDisplacement] using hh)
  have hsqrtSq : Real.sqrt (1 + (s : ℝ)) ^ 2 = 1 + (s : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtBound : (B : ℝ) * Real.sqrt (1 + (s : ℝ)) ≤
      (1 + (s : ℝ)) / 4 + (B : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (1 + (s : ℝ)) - 2 * (B : ℝ))]
  have hrUpper : (r : ℝ) < (m : ℝ) / 2 + (B : ℝ) ^ 2 + 1 / 4 := by nlinarith
  have hlinearReal : 2 * ((C : ℝ) + (B : ℝ) ^ 2 + 1) ≤ m := by exact_mod_cast hlinear
  have hroomReal : (r + C : ℕ) < (m : ℝ) := by push_cast; nlinarith
  have hroom : r + C < m := by exact_mod_cast hroomReal
  omega

def explicitRenewalCase2PointThreshold (A B E : ℕ) : ℕ :=
  2 * (explicitRenewalCase1Threshold A E + B ^ 2 + 1) + 4

theorem explicitRenewal_case2_localized {A B E n m s : ℕ}
    {xi : ZMod (3 ^ n)} (hactive : TaoSection7Prop78ActiveCoverData n xi (explicitRenewalEpsilon E))
    (hm : explicitRenewalCase2PointThreshold A B E ≤ m)
    {Delta : TaoSection7Triangle} (hDelta : Delta ∈ hactive.family)
    {start : TaoSection7RenewalPoint} {r : ℕ+} {ell : ℤ}
    (hboundary : taoSection7QmBoundary (n / 2) m start)
    (hstart : Delta.Mem start.toPoint) (hdepth : Delta.verticalDepth start.toPoint = (s : ℤ))
    (hnear : (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m)
    (hlocalized : ((r : ℕ), ell) ∈ lemma77CanonicalLocalizedEndpointEvent s B)
    (hne : lemma77CanonicalFirstPassageEndpointPMF start s ((r : ℕ), ell) ≠ 0)
    (hcollar : taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation (explicitRenewalEpsilon E) ^ 2) :
    taoSection7SourceActualQ n xi (explicitRenewalEpsilon E)
        (lemma77RenewalPointOfRelativeEndpoint start ((r : ℕ), ell)) ≤
      Real.exp (-((explicitRenewalEpsilon E) ^ 3 / 2)) * taoSection7Case1InvPow A m r *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi (explicitRenewalEpsilon E) := by
  let endpoint := lemma77RenewalPointOfRelativeEndpoint start ((r : ℕ), ell)
  have hj : (endpoint.j : ℕ) = (start.j : ℕ) + (r : ℕ) := by simp [endpoint]
  have heps : 0 < explicitRenewalEpsilon E := by unfold explicitRenewalEpsilon; positivity
  have hroom := explicitRenewal_localized_room hm hnear hlocalized.1
  have hlocalBoundary : taoSection7QmBoundary (n / 2) (m - (r : ℕ)) endpoint :=
    taoSection7QmBoundary_of_horizontalAdvance hboundary hj hroom.1
  have hDomain := taoSection7QmBoundary_toPoint_sourceDomain hlocalBoundary
  have hwhite : taoSection7SourceActualW n xi (explicitRenewalEpsilon E) endpoint :=
    taoSection7SourceActualW_of_localizedEndpoint_activeCover hactive hDelta hstart hdepth
      hlocalized (lemma77CanonicalFirstPassageEndpointPMF_nonzero_support hne).2 hDomain hcollar
  have hdiscount := explicitRenewal_case1_halfDiscount hroom.2 hlocalBoundary hwhite
  have hmono := taoSection7SourceActualQmAtCutoff_mono_of_le
    (n := n) (A := A) (xi := xi) heps.le (show m - (r : ℕ) - 1 ≤ m - 1 by omega)
  have hfactor : 0 ≤ Real.exp (-((explicitRenewalEpsilon E) ^ 3 / 2)) *
      (((m - (r : ℕ) : ℕ) : ℝ) ^ A)⁻¹ := by positivity
  have hbound := hdiscount.trans (mul_le_mul_of_nonneg_left hmono hfactor)
  have hmax : max (m - (r : ℕ)) 1 = m - (r : ℕ) := by omega
  simpa only [taoSection7Case1InvPow, hmax, ← inv_pow] using hbound

def explicitRenewalCase2Threshold (A B E : ℕ) : ℕ :=
  max (explicitRenewalCase2PointThreshold A B E)
    (max (explicitRenewalCase2MomentThreshold A E) 2)

theorem explicitRenewal_case2_endpointExpectation (A B E : ℕ)
    (hA : 1 ≤ A)
    (hmass : ∀ start s, (1 / 2 : ℝ) ≤
      ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        (lemma77CanonicalLocalizedEndpointEvent s B)).toReal)
    (hcollar : taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation (explicitRenewalEpsilon E) ^ 2) :
    ∀ n : ℕ, ∀ xi : ZMod (3 ^ n),
      ∀ hactive : TaoSection7Prop78ActiveCoverData n xi (explicitRenewalEpsilon E),
      ∀ m ≥ explicitRenewalCase2Threshold A B E,
      ∀ Delta : TaoSection7Triangle, Delta ∈ hactive.family →
      ∀ start : TaoSection7RenewalPoint, ∀ s : ℕ,
        taoSection7QmBoundary (n / 2) m start →
        Delta.Mem start.toPoint →
        Delta.verticalDepth start.toPoint = (s : ℤ) →
        (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m →
        (∑' x : ℕ × ℤ,
          (lemma77CanonicalFirstPassageEndpointPMF start s x).toReal *
            taoSection7SourceActualQ n xi (explicitRenewalEpsilon E)
              (lemma77RenewalPointOfRelativeEndpoint start x)) ≤
          ((m : ℝ)⁻¹ ^ A) *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi (explicitRenewalEpsilon E) := by
  let epsilon := explicitRenewalEpsilon E
  have hepsilon : 0 < epsilon := by dsimp [epsilon, explicitRenewalEpsilon]; positivity
  have hepsilon1 : epsilon ≤ 1 := by
    dsimp [epsilon, explicitRenewalEpsilon]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  intro n xi hactive m hm Delta hDelta start s hboundary hstart hdepth hnear
  have hmPoint : explicitRenewalCase2PointThreshold A B E ≤ m :=
    (le_max_left _ _).trans hm
  have hmMgf : explicitRenewalCase2MomentThreshold A E ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm2 : 2 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hscalar := explicitRenewal_case2_mgf hA hmMgf s hnear
  let p := lemma77CanonicalFirstPassageEndpointPMF start s
  let E := lemma77CanonicalLocalizedEndpointEvent s B
  let t := taoSection7Case1Rate A m
  let Qprev := taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon
  let Cbase := ((m : ℝ)⁻¹ ^ A) * Qprev
  let F : ℕ × ℤ → ℝ := fun x =>
    taoSection7SourceActualQ n xi epsilon
      (lemma77RenewalPointOfRelativeEndpoint start x)
  let g : ℕ × ℤ → ℝ := fun x => t * (x.1 : ℝ)
  have hQprev0 : 0 ≤ Qprev := by
    exact taoSection7SourceActualQmAtCutoff_nonneg hepsilon.le
  have hCbase0 : 0 ≤ Cbase := by
    dsimp [Cbase]
    positivity
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    exact taoSection7SourceActualQ_nonneg hepsilon.le _
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g, t]
    exact mul_nonneg hscalar.1 (by positivity)
  have hendpointMgf :=
    lemma77CanonicalFirstPassageEndpointPMF_horizontalExpMoment_le
      start s hscalar.1 hscalar.2.1
  have hordinary : ∀ x, p x ≠ 0 →
      F x ≤ Cbase * Real.exp (g x) := by
    rintro ⟨r, ell⟩ hne
    have hr := (lemma77CanonicalFirstPassageEndpointPMF_nonzero_support hne).1
    let rpos : ℕ+ := ⟨r, hr⟩
    have hQ :=
      taoSection7SourceActualQ_relativeEndpoint_le_case1InvPow_mul_qmPrev
        hepsilon.le (A := A) (xi := xi) hboundary (r := rpos) (ell := ell)
    have hinv := taoSection7Case1InvPow_le_expEnvelope A m rpos hm2
    calc
      F (r, ell) ≤ taoSection7Case1InvPow A m rpos * Qprev := hQ
      _ ≤ (((m : ℝ)⁻¹ ^ A) * Real.exp (t * (r : ℝ))) * Qprev :=
        mul_le_mul_of_nonneg_right hinv hQprev0
      _ = Cbase * Real.exp (g (r, ell)) := by
        dsimp [Cbase, g, t, Qprev, F, rpos]
        ring
  have hlocalized : ∀ x, p x ≠ 0 → x ∈ E →
      F x ≤ Cbase *
        (Real.exp (-(epsilon ^ 3 / 2)) * Real.exp (g x)) := by
    rintro ⟨r, ell⟩ hne hmem
    have hr := (lemma77CanonicalFirstPassageEndpointPMF_nonzero_support hne).1
    let rpos : ℕ+ := ⟨r, hr⟩
    have hQ := explicitRenewal_case2_localized (r := rpos) (ell := ell) hactive hmPoint hDelta
      hboundary hstart hdepth hnear hmem hne hcollar
    have hinv := taoSection7Case1InvPow_le_expEnvelope A m rpos hm2
    calc
      F (r, ell) ≤ Real.exp (-(epsilon ^ 3 / 2)) *
          taoSection7Case1InvPow A m rpos * Qprev := hQ
      _ ≤ Real.exp (-(epsilon ^ 3 / 2)) *
          ((((m : ℝ)⁻¹ ^ A) * Real.exp (t * (r : ℝ))) * Qprev) := by
        have hleft := mul_le_mul_of_nonneg_left hinv
          (Real.exp_nonneg (-(epsilon ^ 3 / 2)))
        have hright := mul_le_mul_of_nonneg_right hleft hQprev0
        simpa [mul_assoc] using hright
      _ = Cbase *
          (Real.exp (-(epsilon ^ 3 / 2)) * Real.exp (g (r, ell))) := by
        dsimp [Cbase, g, t, Qprev, F, rpos]
        ring
  have hraw := pmf_expectation_le_mul_sub_eventMass_of_branch_bounds
    p E F g hF0 hCbase0 (show 0 ≤ epsilon ^ 3 / 4 by positivity)
    (taoSection7Prop78_exp_neg_epsilon_cube_half_le hepsilon.le hepsilon1)
    hg0 (by simpa [p, g, t] using hendpointMgf.1)
    hordinary hlocalized
  have hbracket :
      (∑' x, (p x).toReal * Real.exp (g x)) -
          epsilon ^ 3 / 4 * (p.toOuterMeasure E).toReal ≤ 1 := by
    have hbase :
        (∑' x, (p x).toReal * Real.exp (g x)) ≤
          taoSection7Geom4ExpMoment t ^ (s + 1) := by
      simpa [p, g, t] using hendpointMgf.2
    have hmass' : (1 / 2 : ℝ) ≤ (p.toOuterMeasure E).toReal := by
      simpa [p, E] using hmass start s
    have hepsilonCube0 : 0 ≤ epsilon ^ 3 := by positivity
    nlinarith [hscalar.2.2]
  calc
    (∑' x : ℕ × ℤ, (p x).toReal * F x) ≤
        Cbase * ((∑' x, (p x).toReal * Real.exp (g x)) -
          epsilon ^ 3 / 4 * (p.toOuterMeasure E).toReal) := hraw
    _ ≤ Cbase * 1 := mul_le_mul_of_nonneg_left hbracket hCbase0
    _ = ((m : ℝ)⁻¹ ^ A) *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
      simp [Cbase, Qprev]

theorem explicitRenewal_case2_nearTop (A B E : ℕ)
    (hA : 1 ≤ A)
    (hmass : ∀ start s, (1 / 2 : ℝ) ≤
      ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        (lemma77CanonicalLocalizedEndpointEvent s B)).toReal)
    (hcollar : taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation (explicitRenewalEpsilon E) ^ 2) :
    ∀ n : ℕ, ∀ xi : ZMod (3 ^ n),
      ∀ hactive : TaoSection7Prop78ActiveCoverData n xi (explicitRenewalEpsilon E),
      ∀ m ≥ explicitRenewalCase2Threshold A B E, ∀ start : TaoSection7RenewalPoint,
        taoSection7QmBoundary (n / 2) m start →
        TaoSection7QmBoundaryNearTop (taoSection7Prop78BoundaryThreshold m) hactive.family start →
        taoSection7SourceActualQ n xi (explicitRenewalEpsilon E) start ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi (explicitRenewalEpsilon E) := by
  let epsilon := explicitRenewalEpsilon E
  have hepsilon : 0 < epsilon := by dsimp [epsilon, explicitRenewalEpsilon]; positivity
  have hC := explicitRenewal_case2_endpointExpectation A B E hA hmass hcollar
  intro n xi hactive m hm start hboundary hnear
  rcases hnear with ⟨Delta, hDelta, hstart, hdepthNear⟩
  have hdepth0 : 0 ≤ Delta.verticalDepth start.toPoint :=
    TaoSection7Triangle.verticalDepth_nonneg_of_mem hstart
  let s : ℕ := (Delta.verticalDepth start.toPoint).toNat
  have hdepth :
      Delta.verticalDepth start.toPoint = (s : ℤ) := by
    exact (Int.toNat_of_nonneg hdepth0).symm
  have hsNear : (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m := by
    rw [hdepth] at hdepthNear
    simpa using hdepthNear
  have hexpect := hC n xi hactive m hm Delta hDelta start s
    hboundary hstart hdepth hsNear
  calc
    taoSection7SourceActualQ n xi epsilon start ≤
        ∑' x : ℕ × ℤ,
          (lemma77CanonicalFirstPassageEndpointPMF start s x).toReal *
            taoSection7SourceActualQ n xi epsilon
              (lemma77RenewalPointOfRelativeEndpoint start x) :=
      taoSection7SourceActualQ_le_canonicalFirstPassageEndpointExpectation
        hepsilon.le start s
    _ ≤ ((m : ℝ)⁻¹ ^ A) *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := hexpect
    _ = ((m : ℝ) ^ A)⁻¹ *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
      rw [inv_pow]

end

end Erdos1135Predecessor.ND.PositiveDensity
