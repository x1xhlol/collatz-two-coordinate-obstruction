import Erdos1135.Tao.Renewal.CanonicalFirstPassageExpMoment
import Erdos1135.Tao.Renewal.Prop78Case2Discount
import Erdos1135.Tao.Renewal.Prop78Case2MomentScalar
import Erdos1135.Tao.Renewal.Prop78Case2Pointwise
import Erdos1135.Tao.Renewal.QStoppedEndpoint

/-!
# Proposition 7.8 Case 2 Endpoint Expectation

This leaf integrates the supported ordinary and localized-discounted endpoint
bounds.  The endpoint MGF and localized mass gain are combined while the
possibly-zero previous `Q_m` value remains a multiplicative factor.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

/-- Integrate ordinary and event-localized pointwise bounds against a PMF.
Zero-mass atoms need no pointwise bound, which is essential for unsupported
coordinates in countable endpoint laws. -/
theorem pmf_expectation_le_mul_sub_eventMass_of_branch_bounds
    {alpha : Type*} (p : PMF alpha) (E : Set alpha)
    (F g : alpha → ℝ) {C d c : ℝ}
    (hF0 : ∀ x, 0 ≤ F x)
    (hC0 : 0 ≤ C)
    (hc0 : 0 ≤ c)
    (hdiscount : Real.exp (-d) ≤ 1 - c)
    (hg0 : ∀ x, 0 ≤ g x)
    (hsum : Summable fun x => (p x).toReal * Real.exp (g x))
    (hordinary : ∀ x, p x ≠ 0 → F x ≤ C * Real.exp (g x))
    (hlocalized : ∀ x, p x ≠ 0 → x ∈ E →
      F x ≤ C * (Real.exp (-d) * Real.exp (g x))) :
    (∑' x, (p x).toReal * F x) ≤
      C * ((∑' x, (p x).toReal * Real.exp (g x)) -
        c * (p.toOuterMeasure E).toReal) := by
  classical
  let discounted : alpha → ℝ := fun x =>
    (p x).toReal *
      (Real.exp (-(d * E.indicator (fun _ => (1 : ℝ)) x)) *
        Real.exp (g x))
  let base : alpha → ℝ := fun x => (p x).toReal * Real.exp (g x)
  have hdiscount_le_one : Real.exp (-d) ≤ 1 :=
    hdiscount.trans (sub_le_self 1 hc0)
  have hdiscounted0 : ∀ x, 0 ≤ discounted x := by
    intro x
    dsimp [discounted]
    positivity
  have hdiscounted_le : ∀ x, discounted x ≤ base x := by
    intro x
    dsimp [discounted, base]
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_mem hx, mul_one]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact mul_le_of_le_one_left (Real.exp_nonneg _) hdiscount_le_one
    · simp [Set.indicator, hx]
  have hdiscountedSum : Summable discounted :=
    Summable.of_nonneg_of_le hdiscounted0 hdiscounted_le (by
      simpa [base] using hsum)
  have hmajor : ∀ x,
      (p x).toReal * F x ≤ C * discounted x := by
    intro x
    by_cases hp : p x = 0
    · simp [hp, discounted]
    · have hbranch : F x ≤ C *
          (Real.exp (-(d * E.indicator (fun _ => (1 : ℝ)) x)) *
            Real.exp (g x)) := by
        by_cases hx : x ∈ E
        · have hloc := hlocalized x hp hx
          simpa [Set.indicator, hx] using hloc
        · have hord := hordinary x hp
          simpa [Set.indicator, hx] using hord
      calc
        (p x).toReal * F x ≤ (p x).toReal *
            (C * (Real.exp
              (-(d * E.indicator (fun _ => (1 : ℝ)) x)) *
                Real.exp (g x))) :=
          mul_le_mul_of_nonneg_left hbranch ENNReal.toReal_nonneg
        _ = C * discounted x := by
          dsimp [discounted]
          ring
  have hactualSum : Summable fun x => (p x).toReal * F x :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (hF0 x)) hmajor
      (hdiscountedSum.mul_left C)
  have hdiscBound := pmf_discounted_exp_expectation_le_sub_eventMass
    p E g hc0 hdiscount hg0 hsum
  calc
    (∑' x, (p x).toReal * F x) ≤
        ∑' x, C * discounted x :=
      hactualSum.tsum_le_tsum hmajor (hdiscountedSum.mul_left C)
    _ = C * ∑' x, discounted x := by rw [tsum_mul_left]
    _ ≤ C * ((∑' x, (p x).toReal * Real.exp (g x)) -
          c * (p.toOuterMeasure E).toReal) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      simpa [discounted] using hdiscBound

/-- The near-top canonical endpoint expectation has the required absorbed
`m^{-A} Q_{m-1}` bound, uniformly after one threshold chosen before all
ambient source parameters. -/
theorem exists_taoSection7Prop78_case2_endpointExpectation_threshold
    (B : ℕ)
    (hmass : ∀ start : TaoSection7RenewalPoint, ∀ s : ℕ,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s B)).toReal)
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1)
    (hcollar :
      taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (A : ℕ) :
    ∃ C : ℕ,
      ∀ n : ℕ, ∀ xi : ZMod (3 ^ n),
      ∀ hactive : TaoSection7Prop78ActiveCoverData n xi epsilon,
      ∀ m ≥ C,
      ∀ Delta : TaoSection7Triangle, Delta ∈ hactive.family →
      ∀ start : TaoSection7RenewalPoint, ∀ s : ℕ,
        taoSection7QmBoundary (n / 2) m start →
        Delta.Mem start.toPoint →
        Delta.verticalDepth start.toPoint = (s : ℤ) →
        (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m →
        (∑' x : ℕ × ℤ,
          (lemma77CanonicalFirstPassageEndpointPMF start s x).toReal *
            taoSection7SourceActualQ n xi epsilon
              (lemma77RenewalPointOfRelativeEndpoint start x)) ≤
          ((m : ℝ)⁻¹ ^ A) *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  obtain ⟨Cpoint, hpoint⟩ :=
    exists_taoSection7Prop78_case2_localizedEndpoint_discounted_threshold
      B hepsilon hcollar A
  obtain ⟨Cmgf, hmgf⟩ :=
    exists_taoSection7Prop78_nearTopGeom4ExpMoment_threshold A hepsilon
  refine ⟨max Cpoint (max Cmgf 2), ?_⟩
  intro n xi hactive m hm Delta hDelta start s hboundary hstart hdepth hnear
  have hmPoint : Cpoint ≤ m := le_trans (le_max_left _ _) hm
  have hmMgf : Cmgf ≤ m :=
    le_trans (le_max_left Cmgf 2) (le_trans (le_max_right Cpoint _) hm)
  have hm2 : 2 ≤ m :=
    le_trans (le_max_right Cmgf 2) (le_trans (le_max_right Cpoint _) hm)
  have hscalar := hmgf m hmMgf s hnear
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
    have hQ := hpoint n xi hactive m hmPoint Delta hDelta start s rpos ell
      hboundary hstart hdepth hnear hmem hne
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

/-- Parametric near-top Case 2 producer with `epsilon` fixed before `A` and
one common threshold fixed before `n`, `xi`, and the boundary level. -/
theorem exists_taoSection7Prop78_case2_nearTop_threshold
    (B : ℕ)
    (hmass : ∀ start : TaoSection7RenewalPoint, ∀ s : ℕ,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s B)).toReal)
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1)
    (hcollar :
      taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (A : ℕ) :
    ∃ C : ℕ,
      ∀ n : ℕ, ∀ xi : ZMod (3 ^ n),
      ∀ hactive : TaoSection7Prop78ActiveCoverData n xi epsilon,
      ∀ m ≥ C, ∀ start : TaoSection7RenewalPoint,
        taoSection7QmBoundary (n / 2) m start →
        TaoSection7QmBoundaryNearTop
            (taoSection7Prop78BoundaryThreshold m) hactive.family start →
        taoSection7SourceActualQ n xi epsilon start ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  obtain ⟨C, hC⟩ :=
    exists_taoSection7Prop78_case2_endpointExpectation_threshold
      B hmass hepsilon hepsilon1 hcollar A
  refine ⟨C, ?_⟩
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

end Tao
end Erdos1135
