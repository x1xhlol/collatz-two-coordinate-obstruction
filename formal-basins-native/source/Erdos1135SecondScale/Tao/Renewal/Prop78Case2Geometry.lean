/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageLocalizedMass
import Erdos1135SecondScale.Tao.Renewal.Prop78ActiveCover

/-!
# Proposition 7.8 Case 2 Geometry

This deterministic leaf turns a supported endpoint in the canonical strict
window into a point outside but uniformly close to its starting triangle.  A
strict separation argument then makes that endpoint cutoff-white.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

/-- Horizontal slope of a Section 7 triangle row. -/
noncomputable def taoSection7Case2TopRowSlope : ℝ :=
  Real.log 2 / Real.log 9

/-- Positive drift between the triangle row slope and the first-passage
horizontal center `1/4`. -/
noncomputable def taoSection7Case2TopRowDrift : ℝ :=
  taoSection7Case2TopRowSlope - 1 / 4

theorem taoSection7Case2TopRowDrift_pos :
    0 < taoSection7Case2TopRowDrift := by
  simpa [taoSection7Case2TopRowDrift, taoSection7Case2TopRowSlope] using
    TaoSection7Lemma710.lemma710_log_margin_pos

/-- Clamp the available top-row advance by the endpoint displacement. -/
noncomputable def taoSection7Case2TopRowOffset (s r : ℕ) : ℕ :=
  min r (Nat.floor (taoSection7Case2TopRowSlope * (s : ℝ)))

/-- Absolute horizontal collar obtained from the floor error and square
completion. -/
noncomputable def taoSection7Case2HorizontalCollar (B : ℕ) : ℝ :=
  1 + taoSection7Case2TopRowDrift +
    (B : ℝ) ^ 2 / (4 * taoSection7Case2TopRowDrift)

theorem taoSection7Case2HorizontalCollar_pos (B : ℕ) :
    0 < taoSection7Case2HorizontalCollar B := by
  have hdelta := taoSection7Case2TopRowDrift_pos
  unfold taoSection7Case2HorizontalCollar
  positivity

/-- Top-row lattice witness obtained by advancing from `start` by the clamped
floor of the triangle row slope. -/
noncomputable def taoSection7Case2TopRowWitness
    (Delta : TaoSection7Triangle) (start : TaoSection7RenewalPoint)
    (s r : ℕ) : TaoSection7Point :=
  { j := taoSection7ShiftIndex start.j (taoSection7Case2TopRowOffset s r)
    l := Delta.cornerL }

/-- The floor/min top-row witness stays in the same triangle. -/
theorem taoSection7Case2TopRowWitness_mem
    {Delta : TaoSection7Triangle} {start : TaoSection7RenewalPoint}
    {s r : ℕ}
    (hstart : Delta.Mem start.toPoint)
    (hdepth : Delta.verticalDepth start.toPoint = (s : ℤ)) :
    Delta.Mem (taoSection7Case2TopRowWitness Delta start s r) := by
  let alpha := taoSection7Case2TopRowSlope
  let a := Nat.floor (alpha * (s : ℝ))
  let k := min r a
  let w := taoSection7Case2TopRowWitness Delta start s r
  have halpha0 : 0 ≤ alpha := by
    dsimp [alpha, taoSection7Case2TopRowSlope]
    positivity
  have has0 : 0 ≤ alpha * (s : ℝ) :=
    mul_nonneg halpha0 (Nat.cast_nonneg s)
  have hka : k ≤ a := min_le_right _ _
  have hfloor : (a : ℝ) ≤ alpha * (s : ℝ) := by
    simpa [a] using Nat.floor_le has0
  have hkreal : (k : ℝ) ≤ alpha * (s : ℝ) :=
    (Nat.cast_le.mpr hka).trans hfloor
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hklog : (k : ℝ) * Real.log 9 ≤ (s : ℝ) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hkreal hlog9.le
    dsimp [alpha, taoSection7Case2TopRowSlope] at hmul
    field_simp [ne_of_gt hlog9] at hmul
    nlinarith
  have hcornerStart : Delta.cornerJ ≤ start.toPoint.j := hstart.1
  have hcornerW : Delta.cornerJ ≤ w.j := by
    change Delta.cornerJ ≤ taoSection7ShiftIndex start.j k
    exact_mod_cast (le_trans (show (Delta.cornerJ : ℕ) ≤ (start.j : ℕ) by
      exact_mod_cast hcornerStart) (Nat.le_add_right _ _))
  refine ⟨hcornerW, by simp [taoSection7Case2TopRowWitness], ?_⟩
  have hstartDepth :
      ((Delta.verticalDepth start.toPoint : ℤ) : ℝ) = (s : ℝ) := by
    exact_mod_cast hdepth
  have hstartWeight := Delta.mem_weight_le_size hstart
  have hstartHorizontal :=
    Delta.horizontalDepth_real_eq_sub_of_cornerJ_le
      (lStar := start.toPoint.l) hcornerStart
  have hwHorizontal :=
    Delta.horizontalDepth_real_eq_sub_of_cornerJ_le
      (lStar := w.l) hcornerW
  rw [hstartHorizontal, hstartDepth] at hstartWeight
  rw [hwHorizontal]
  simp [w, taoSection7Case2TopRowWitness,
    show taoSection7Case2TopRowOffset s r = k by rfl,
    taoSection7ShiftIndex, TaoSection7Triangle.verticalDepth]
  have hstartWeight' :
      (((start.j : ℕ) : ℝ) - ((Delta.cornerJ : ℕ) : ℝ)) * Real.log 9 +
          (s : ℝ) * Real.log 2 ≤ Delta.size := by
    simpa using hstartWeight
  have hsplit :
      (((start.j : ℕ) : ℝ) + (k : ℝ) - ((Delta.cornerJ : ℕ) : ℝ)) *
          Real.log 9 =
        (((start.j : ℕ) : ℝ) - ((Delta.cornerJ : ℕ) : ℝ)) * Real.log 9 +
          (k : ℝ) * Real.log 9 := by ring
  rw [hsplit]
  linarith

/-- A localized supported endpoint is above the starting triangle and lies in
one absolute strict collar around an explicit member of that triangle. -/
theorem taoSection7Case2_exists_topRowWitness
    {Delta : TaoSection7Triangle} {start : TaoSection7RenewalPoint}
    {s r B : ℕ} {ell : ℤ}
    (hstart : Delta.Mem start.toPoint)
    (hdepth : Delta.verticalDepth start.toPoint = (s : ℤ))
    (hhorizontal :
      |lemma77CenteredHorizontalDisplacement s r| <
        (B : ℝ) * Real.sqrt (1 + (s : ℝ)))
    (hellLower : (s : ℤ) < ell)
    (hellUpper : ell < (s : ℤ) + (B : ℤ)) :
    let endpoint :=
      (lemma77RenewalPointOfRelativeEndpoint start (r, ell)).toPoint
    ∃ w : TaoSection7Point,
      Delta.Mem w ∧
      ¬ Delta.Mem endpoint ∧
      endpoint.distSq w <
        taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 := by
  let alpha := taoSection7Case2TopRowSlope
  let delta := taoSection7Case2TopRowDrift
  let a := Nat.floor (alpha * (s : ℝ))
  let k := min r a
  let D := taoSection7Case2HorizontalCollar B
  let endpoint :=
    (lemma77RenewalPointOfRelativeEndpoint start (r, ell)).toPoint
  let w := taoSection7Case2TopRowWitness Delta start s r
  have hdelta : 0 < delta := by
    simpa [delta] using taoSection7Case2TopRowDrift_pos
  have hD : 0 < D := by
    simpa [D] using taoSection7Case2HorizontalCollar_pos B
  have hw : Delta.Mem w := by
    simpa [w] using taoSection7Case2TopRowWitness_mem hstart hdepth
  have hcorner : Delta.cornerL = start.l + (s : ℤ) := by
    unfold TaoSection7Triangle.verticalDepth at hdepth
    simp only [TaoSection7RenewalPoint.toPoint_l] at hdepth
    omega
  have houtside : ¬ Delta.Mem endpoint := by
    intro hendpoint
    have hheight := hendpoint.2.1
    simp only [endpoint, lemma77RenewalPointOfRelativeEndpoint,
      TaoSection7RenewalPoint.toPoint_l] at hheight
    omega
  have hk : k ≤ r := min_le_left _ _
  have hgap : ((r - k : ℕ) : ℝ) < D := by
    by_cases hra : r ≤ a
    · have hkr : k = r := min_eq_left hra
      simp [hkr, hD]
    · have har : a < r := Nat.lt_of_not_ge hra
      have hkEq : k = a := min_eq_right har.le
      have halpha0 : 0 ≤ alpha := by
        dsimp [alpha, taoSection7Case2TopRowSlope]
        positivity
      have hfloorUpper : alpha * (s : ℝ) < (a : ℝ) + 1 := by
        simpa [a] using Nat.lt_floor_add_one (alpha * (s : ℝ))
      have hcenterUpper :
          (r : ℝ) - (s : ℝ) / 4 <
            (B : ℝ) * Real.sqrt (1 + (s : ℝ)) :=
        (le_abs_self _).trans_lt (by
          simpa [lemma77CenteredHorizontalDisplacement] using hhorizontal)
      have hsqrt0 : 0 ≤ Real.sqrt (1 + (s : ℝ)) := Real.sqrt_nonneg _
      have hsqrtSq : (Real.sqrt (1 + (s : ℝ))) ^ 2 = 1 + (s : ℝ) := by
        rw [Real.sq_sqrt]
        positivity
      let x := Real.sqrt (1 + (s : ℝ))
      let c := (B : ℝ) ^ 2 / (4 * delta)
      have hfourDelta : 0 < 4 * delta := by positivity
      have hfactor :
          0 ≤ 4 * delta * (delta * x ^ 2 - (B : ℝ) * x + c) := by
        calc
          0 ≤ (2 * delta * x - (B : ℝ)) ^ 2 := sq_nonneg _
          _ = 4 * delta * (delta * x ^ 2 - (B : ℝ) * x + c) := by
            dsimp [c]
            field_simp [ne_of_gt hdelta]
            ring
      have hbracket :
          0 ≤ delta * x ^ 2 - (B : ℝ) * x + c :=
        nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hfactor)
          (by simpa [mul_comm] using hfourDelta)
      have hcomplete :
          (B : ℝ) * Real.sqrt (1 + (s : ℝ)) - delta * (s : ℝ) ≤
            delta + (B : ℝ) ^ 2 / (4 * delta) := by
        dsimp [x, c] at hbracket
        nlinarith
      have hraw : (r : ℝ) - (a : ℝ) < D := by
        dsimp [D, taoSection7Case2HorizontalCollar]
        dsimp [delta, taoSection7Case2TopRowDrift,
          alpha, taoSection7Case2TopRowSlope] at hfloorUpper hcomplete ⊢
        linarith
      rw [hkEq, Nat.cast_sub har.le]
      exact hraw
  have hvertical0 : (0 : ℝ) < (ell - (s : ℤ) : ℤ) := by
    exact_mod_cast (sub_pos.mpr hellLower)
  have hverticalB : ((ell - (s : ℤ) : ℤ) : ℝ) < (B : ℝ) := by
    have hInt : ell - (s : ℤ) < (B : ℤ) := by omega
    exact_mod_cast hInt
  have hgap0 : 0 ≤ ((r - k : ℕ) : ℝ) := by positivity
  have hdist : endpoint.distSq w < D ^ 2 + (B : ℝ) ^ 2 := by
    have hhSq : ((r - k : ℕ) : ℝ) ^ 2 < D ^ 2 := by nlinarith
    have hvSq : (((ell - (s : ℤ) : ℤ) : ℝ)) ^ 2 < (B : ℝ) ^ 2 := by
      nlinarith
    have hendJ : endpoint.jReal = ((start.j : ℕ) : ℝ) + (r : ℝ) := by
      simp [endpoint, TaoSection7Point.jReal]
    have hwJ : w.jReal = ((start.j : ℕ) : ℝ) + (k : ℝ) := by
      simp [w, taoSection7Case2TopRowWitness, k, a, alpha,
        taoSection7Case2TopRowOffset, taoSection7Case2TopRowSlope,
        TaoSection7Point.jReal, taoSection7ShiftIndex]
    have hendL : endpoint.lReal = (start.l : ℝ) + (ell : ℝ) := by
      simp [endpoint, TaoSection7Point.lReal]
    have hwL : w.lReal = (Delta.cornerL : ℝ) := by
      rfl
    rw [TaoSection7Point.distSq, hendJ, hwJ, hendL, hwL, hcorner,
      Int.cast_add, Int.cast_natCast]
    rw [show ((start.j : ℕ) : ℝ) + r - (((start.j : ℕ) : ℝ) + k) =
      ((r - k : ℕ) : ℝ) by
        rw [Nat.cast_sub hk]
        ring]
    push_cast at hvSq
    ring_nf
    nlinarith
  exact ⟨w, hw, houtside, by simpa [endpoint, D] using hdist⟩

/-- Strict proximity to one active triangle forces source cutoff whiteness;
the stored cover and separation fields suffice without Claim Star. -/
theorem taoSection7SourceActualW_of_activeCover_distSq_lt
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    {Delta : TaoSection7Triangle} (hDelta : Delta ∈ hactive.family)
    {w : TaoSection7Point} (hw : Delta.Mem w)
    {endpoint : TaoSection7RenewalPoint}
    (hOutside : ¬ Delta.Mem endpoint.toPoint)
    (hDomain : taoSection7SourcePointInDomain (n / 2) endpoint.toPoint)
    (hclose : endpoint.toPoint.distSq w <
      taoSection7TriangleSeparation epsilon ^ 2) :
    taoSection7SourceActualW n xi epsilon endpoint := by
  have hwhite : taoSection7SourceWhitePoint n xi epsilon endpoint.toPoint := by
    apply taoSection7SourceWhitePoint_iff_not_blackPoint.mpr
    intro hblack
    rcases (hactive.cover endpoint.toPoint).mp ⟨hDomain, hblack⟩ with
      ⟨Gamma, hGamma, hendpointGamma⟩
    have hne : Delta ≠ Gamma := by
      intro hEq
      apply hOutside
      rw [hEq]
      exact hendpointGamma
    have hfar := hactive.separated hDelta hGamma hne
      w endpoint.toPoint hw hendpointGamma
    rw [TaoSection7Point.distSq_comm w endpoint.toPoint] at hfar
    exact (not_lt_of_ge hfar) hclose
  unfold taoSection7SourceActualW
  exact taoSection7SourceWhiteRenewal_cutoff_iff_toPoint.mpr
    ⟨hDomain, hwhite⟩

/-- A localized supported endpoint is cutoff-white once one absolute collar
fits inside the active family separation scale. -/
theorem taoSection7SourceActualW_of_localizedEndpoint_activeCover
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    {Delta : TaoSection7Triangle} (hDelta : Delta ∈ hactive.family)
    {start : TaoSection7RenewalPoint} {s r B : ℕ} {ell : ℤ}
    (hstart : Delta.Mem start.toPoint)
    (hdepth : Delta.verticalDepth start.toPoint = (s : ℤ))
    (hlocalized : (r, ell) ∈ lemma77CanonicalLocalizedEndpointEvent s B)
    (hsupport : (s : ℤ) < ell)
    (hDomain : taoSection7SourcePointInDomain (n / 2)
      (lemma77RenewalPointOfRelativeEndpoint start (r, ell)).toPoint)
    (hcollar : taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation epsilon ^ 2) :
    taoSection7SourceActualW n xi epsilon
      (lemma77RenewalPointOfRelativeEndpoint start (r, ell)) := by
  rcases taoSection7Case2_exists_topRowWitness hstart hdepth
      hlocalized.1 hsupport hlocalized.2 with ⟨w, hw, houtside, hdist⟩
  exact taoSection7SourceActualW_of_activeCover_distSq_lt
    hactive hDelta hw houtside hDomain (hdist.trans_le hcollar)

/-- At every sufficiently large boundary level, the localized horizontal
window leaves both positive endpoint room and any prescribed Case 1 margin. -/
theorem exists_taoSection7Prop78_localizedHorizontal_room_threshold
    (B C : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ s r : ℕ,
      (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m →
      |lemma77CenteredHorizontalDisplacement s r| <
          (B : ℝ) * Real.sqrt (1 + (s : ℝ)) →
      r < m ∧ C ≤ m - r := by
  have hlogEventually : ∀ᶠ m : ℕ in Filter.atTop,
      (1 : ℝ) ≤ Real.log (m : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hlinearEventually : ∀ᶠ m : ℕ in Filter.atTop,
      2 * (C + B ^ 2 + 1) ≤ m :=
    Filter.eventually_ge_atTop (2 * (C + B ^ 2 + 1))
  have hboth : ∀ᶠ m : ℕ in Filter.atTop,
      (1 : ℝ) ≤ Real.log (m : ℝ) ∧
        2 * (C + B ^ 2 + 1) ≤ m :=
    hlogEventually.and hlinearEventually
  rcases Filter.eventually_atTop.1 hboth with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm s r hs hhorizontal
  rcases hM m hm with ⟨hlog, hlinear⟩
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hlogSq : (1 : ℝ) ≤ (Real.log (m : ℝ)) ^ 2 := by nlinarith
  have hthreshold : taoSection7Prop78BoundaryThreshold m ≤ (m : ℝ) := by
    unfold taoSection7Prop78BoundaryThreshold
    exact div_le_self hm0 hlogSq
  have hsm : (s : ℝ) ≤ (m : ℝ) := hs.trans hthreshold
  have hcenterUpper :
      (r : ℝ) - (s : ℝ) / 4 <
        (B : ℝ) * Real.sqrt (1 + (s : ℝ)) :=
    (le_abs_self _).trans_lt (by
      simpa [lemma77CenteredHorizontalDisplacement] using hhorizontal)
  have hsqrt0 : 0 ≤ Real.sqrt (1 + (s : ℝ)) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (1 + (s : ℝ))) ^ 2 = 1 + (s : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtBound :
      (B : ℝ) * Real.sqrt (1 + (s : ℝ)) ≤
        (1 + (s : ℝ)) / 4 + (B : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (1 + (s : ℝ)) - 2 * (B : ℝ))]
  have hrUpper :
      (r : ℝ) < (m : ℝ) / 2 + (B : ℝ) ^ 2 + 1 / 4 := by
    nlinarith
  have hlinearReal :
      2 * ((C : ℝ) + (B : ℝ) ^ 2 + 1) ≤ (m : ℝ) := by
    exact_mod_cast hlinear
  have hroomReal : (r + C : ℕ) < (m : ℝ) := by
    push_cast
    nlinarith
  have hroom : r + C < m := by exact_mod_cast hroomReal
  omega

end

end Tao
end Erdos1135SecondScale
