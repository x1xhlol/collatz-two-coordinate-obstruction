import Erdos1135.Tao.Renewal.CanonicalFirstPassageTails
import Mathlib.Tactic

/-!
# Canonical First-Passage Localized Mass

This proof leaf combines the unconditional canonical horizontal and vertical
tails into one absolute central window of probability at least one half.  It
uses the same countable endpoint PMF in both coordinates.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

/-- A PMF gives mass at least one half to the complement of two events whose
real masses are each at most one quarter. -/
theorem pmf_compl_union_toReal_ge_half
    {α : Type*} (p : PMF α) (H V : Set α)
    (hH : (p.toOuterMeasure H).toReal ≤ 1 / 4)
    (hV : (p.toOuterMeasure V).toReal ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ (p.toOuterMeasure ((H ∪ V)ᶜ)).toReal := by
  have huniv : p.toOuterMeasure Set.univ = 1 :=
    (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hfinite (E : Set α) : p.toOuterMeasure E ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      p.toOuterMeasure E ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ E)
      _ = 1 := huniv
  have hbad : (p.toOuterMeasure (H ∪ V)).toReal ≤ 1 / 2 := by
    have hu := MeasureTheory.measure_union_le (μ := p.toOuterMeasure) H V
    have hu' :
        (p.toOuterMeasure (H ∪ V)).toReal ≤
          (p.toOuterMeasure H + p.toOuterMeasure V).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨hfinite H, hfinite V⟩) hu
    rw [ENNReal.toReal_add (hfinite H) (hfinite V)] at hu'
    linarith
  have hcar : p.toOuterMeasure.IsCaratheodory (H ∪ V) := by
    change @MeasurableSet α p.toOuterMeasure.caratheodory (H ∪ V)
    rw [PMF.toOuterMeasure_caratheodory]
    trivial
  have hsplitENN :
      p.toOuterMeasure Set.univ =
        p.toOuterMeasure (Set.univ ∩ (H ∪ V)) +
          p.toOuterMeasure (Set.univ \ (H ∪ V)) :=
    hcar Set.univ
  have hsplit :
      1 = (p.toOuterMeasure (H ∪ V)).toReal +
        (p.toOuterMeasure ((H ∪ V)ᶜ)).toReal := by
    have h := congrArg ENNReal.toReal hsplitENN
    simpa [huniv, ENNReal.toReal_add, hfinite, Set.diff_eq] using h
  linarith

/-- One absolute radius makes each canonical coordinate tail at most one
quarter, uniformly in the start and vertical depth. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_exists_quarterTailRadius :
    ∃ B : ℕ, 1 ≤ B ∧
      ∀ (start : TaoSection7RenewalPoint) (s : ℕ),
        (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
            (lemma77CanonicalHorizontalDeviationEvent s
              ((B : ℝ) * Real.sqrt (1 + (s : ℝ)))) ≤
            ENNReal.ofReal (1 / 4 : ℝ) ∧
          (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
            (lemma77CanonicalVerticalOvershootTailEvent s B) ≤
              ENNReal.ofReal (1 / 4 : ℝ) := by
  rcases lemma77CanonicalFirstPassageHorizontalPMF_deviationTail_commonConstants
    with ⟨Kh, ah, bh, hKh, hah, hbh, hHorizontal⟩
  rcases lemma77CanonicalFirstPassageEndpointPMF_verticalOvershootTail_commonRate
    with ⟨Kv, dv, hKv, hdv, hVertical⟩
  let c : ℝ := min ah bh
  have hc : 0 < c := lt_min hah hbh
  have hlinearTop : Filter.Tendsto (fun B : ℕ => c * (B : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hlinearNeg : Filter.Tendsto (fun B : ℕ => -(c * (B : ℝ)))
      Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hlinearTop
  have hHlim : Filter.Tendsto
      (fun B : ℕ => 2 * Kh * Real.exp (-(c * (B : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hlinearNeg).const_mul (2 * Kh)
  have hverticalTop : Filter.Tendsto (fun B : ℕ => dv * (B : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hdv
  have hverticalNeg : Filter.Tendsto (fun B : ℕ => -(dv * (B : ℝ)))
      Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hverticalTop
  have hVlim : Filter.Tendsto
      (fun B : ℕ => Kv * Real.exp (-(dv * (B : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hverticalNeg).const_mul Kv
  have hHsmall : ∀ᶠ B : ℕ in Filter.atTop,
      2 * Kh * Real.exp (-(c * (B : ℝ))) ≤ 1 / 4 := by
    exact ((tendsto_order.1 hHlim).2 (1 / 4) (by norm_num)).mono
      (fun _ h => h.le)
  have hVsmall : ∀ᶠ B : ℕ in Filter.atTop,
      Kv * Real.exp (-(dv * (B : ℝ))) ≤ 1 / 4 := by
    exact ((tendsto_order.1 hVlim).2 (1 / 4) (by norm_num)).mono
      (fun _ h => h.le)
  have hboth : ∀ᶠ B : ℕ in Filter.atTop,
      1 ≤ B ∧
        2 * Kh * Real.exp (-(c * (B : ℝ))) ≤ 1 / 4 ∧
        Kv * Real.exp (-(dv * (B : ℝ))) ≤ 1 / 4 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hHsmall, hVsmall]
      with B hB hHB hVB
    exact ⟨hB, hHB, hVB⟩
  rcases hboth.exists with ⟨B, hB, hHB, hVB⟩
  refine ⟨B, hB, ?_⟩
  intro start s
  let S : ℝ := 1 + (s : ℝ)
  let t : ℝ := (B : ℝ) * Real.sqrt S
  have hS : 0 < S := by positivity
  have hsqrt : 1 ≤ Real.sqrt S := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by
      dsimp [S]
      exact le_add_of_nonneg_right (Nat.cast_nonneg s))
  have hB0 : 0 ≤ (B : ℝ) := by positivity
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htB : (B : ℝ) ≤ t := by
    dsimp [t]
    nlinarith
  have hquad : t ^ 2 / S = (B : ℝ) ^ 2 := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt hS.le]
    field_simp
  have hBsq : (B : ℝ) ≤ (B : ℝ) ^ 2 := by nlinarith
  have hcah : c ≤ ah := min_le_left _ _
  have hcbh : c ≤ bh := min_le_right _ _
  have hgaussArg : c * (B : ℝ) ≤ ah * (t ^ 2 / S) := by
    rw [hquad]
    nlinarith [mul_le_mul_of_nonneg_right hcah hB0,
      mul_le_mul_of_nonneg_left hBsq hah.le]
  have hlinearArg : c * (B : ℝ) ≤ bh * t := by
    nlinarith [mul_le_mul_of_nonneg_right hcbh hB0,
      mul_le_mul_of_nonneg_left htB hbh.le]
  have hgaussExp : Real.exp (-ah * (t ^ 2 / S)) ≤
      Real.exp (-(c * (B : ℝ))) := by
    rw [Real.exp_le_exp]
    linarith
  have hlinearExp : Real.exp (-bh * t) ≤
      Real.exp (-(c * (B : ℝ))) := by
    rw [Real.exp_le_exp]
    linarith
  have hEnvelope : Kh *
      (Real.exp (-ah * (t ^ 2 / S)) + Real.exp (-bh * t)) ≤ 1 / 4 := by
    calc
      Kh * (Real.exp (-ah * (t ^ 2 / S)) + Real.exp (-bh * t)) ≤
          Kh * (2 * Real.exp (-(c * (B : ℝ)))) := by
        gcongr
        nlinarith
      _ = 2 * Kh * Real.exp (-(c * (B : ℝ))) := by ring
      _ ≤ 1 / 4 := hHB
  constructor
  · calc
      (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
          (lemma77CanonicalHorizontalDeviationEvent s
            ((B : ℝ) * Real.sqrt (1 + (s : ℝ)))) ≤
        ENNReal.ofReal
          (Kh * (Real.exp (-ah * (t ^ 2 / S)) + Real.exp (-bh * t))) := by
            simpa [t, S] using hHorizontal start s t ht0
      _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := ENNReal.ofReal_le_ofReal hEnvelope
  · have hVB' : Kv * Real.exp (-dv * (B : ℝ)) ≤ 1 / 4 := by
      simpa only [neg_mul] using hVB
    exact (hVertical start s B hB).trans
      (ENNReal.ofReal_le_ofReal hVB')

/-- Absolute central first-passage window. -/
def lemma77CanonicalLocalizedEndpointEvent
    (s B : ℕ) : Set (ℕ × ℤ) :=
  {x |
    |lemma77CenteredHorizontalDisplacement s x.1| <
      (B : ℝ) * Real.sqrt (1 + (s : ℝ)) ∧
    x.2 < (s : ℤ) + (B : ℤ)}

/-- The canonical first-passage endpoint has uniformly positive mass in one
absolute horizontal/vertical window. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_localized_absoluteMass :
    ∃ B : ℕ, 1 ≤ B ∧
      ∀ (start : TaoSection7RenewalPoint) (s : ℕ),
        (1 / 2 : ℝ) ≤
          ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
            (lemma77CanonicalLocalizedEndpointEvent s B)).toReal := by
  rcases lemma77CanonicalFirstPassageEndpointPMF_exists_quarterTailRadius with
    ⟨B, hB, htail⟩
  refine ⟨B, hB, ?_⟩
  intro start s
  let p := lemma77CanonicalFirstPassageEndpointPMF start s
  let horizontalBad : Set (ℕ × ℤ) :=
    Prod.fst ⁻¹' lemma77CanonicalHorizontalDeviationEvent s
      ((B : ℝ) * Real.sqrt (1 + (s : ℝ)))
  let verticalBad : Set (ℕ × ℤ) :=
    lemma77CanonicalVerticalOvershootTailEvent s B
  have hHorizontalLift : p.toOuterMeasure horizontalBad =
      (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent s
          ((B : ℝ) * Real.sqrt (1 + (s : ℝ)))) := by
    simpa [p, horizontalBad, lemma77CanonicalFirstPassageHorizontalPMF] using
      (PMF.toOuterMeasure_map_apply Prod.fst p
        (lemma77CanonicalHorizontalDeviationEvent s
          ((B : ℝ) * Real.sqrt (1 + (s : ℝ))))).symm
  have hH : (p.toOuterMeasure horizontalBad).toReal ≤ 1 / 4 := by
    rw [hHorizontalLift]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail start s).1 |>.trans_eq
      (ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hV : (p.toOuterMeasure verticalBad).toReal ≤ 1 / 4 := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail start s).2).trans_eq
      (ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hgood := pmf_compl_union_toReal_ge_half p horizontalBad verticalBad hH hV
  have hevent : lemma77CanonicalLocalizedEndpointEvent s B =
      (horizontalBad ∪ verticalBad)ᶜ := by
    ext x
    simp [lemma77CanonicalLocalizedEndpointEvent, horizontalBad, verticalBad,
      lemma77CanonicalHorizontalDeviationEvent,
      lemma77CanonicalVerticalOvershootTailEvent]
  rw [hevent]
  exact hgood

end TaoSection7Lemma77

end

end Tao
end Erdos1135
