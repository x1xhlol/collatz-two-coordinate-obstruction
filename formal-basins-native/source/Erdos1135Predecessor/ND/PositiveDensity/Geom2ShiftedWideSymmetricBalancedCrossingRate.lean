/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2OneLawGaussianBaseAdaptiveFirstHitRate

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

def ndGeom2ShiftedWideSymmetricWidth (b : ℕ) : ℕ := 3 * b / 5

def ndGeom2ShiftedWideSymmetricLower (b : ℕ) : ℕ :=
  b - ndGeom2ShiftedWideSymmetricWidth b

def ndGeom2ShiftedWideSymmetricHorizon (b : ℕ) : ℕ :=
  b + ndGeom2ShiftedWideSymmetricWidth b

def ndGeom2ShiftedWideSymmetricDepths (b : ℕ) : Finset ℕ :=
  Finset.Icc (ndGeom2ShiftedWideSymmetricLower b)
    (ndGeom2ShiftedWideSymmetricHorizon b)

def ndGeom2ShiftedWideSymmetricMarginNat (b : ℕ) : ℕ := b / 100

def ndGeom2ShiftedWideSymmetricGap (b : ℕ) : ℕ :=
  2 * ndGeom2ShiftedWideSymmetricWidth b -
    ndBalancedTotal (ndGeom2ShiftedWideSymmetricWidth b)

def ndGeom2ShiftedWideSymmetricShiftRadius (b : ℕ) : ℕ :=
  ndGeom2ShiftedWideSymmetricGap b -
    2 * ndGeom2ShiftedWideSymmetricMarginNat b

def ndGeom2ShiftedWideSymmetricShiftIndices (b : ℕ) : Finset ℕ :=
  Finset.Icc 0 (2 * ndGeom2ShiftedWideSymmetricShiftRadius b)

def ndGeom2ShiftedWideSymmetricHit
    (b a s : ℕ) (full : List ℕ+) : Prop :=
  2 * b + ndBalancedTotal (s - b) + a ≤
    Tao.taoTupleWeight (full.take s) + ndBalancedTotal (b - s) +
      ndGeom2ShiftedWideSymmetricShiftRadius b

def ndGeom2ShiftedWideSymmetricCrossing
    (b a : ℕ) (full : List ℕ+) : Prop :=
  ¬ndGeom2ShiftedWideSymmetricHit b a
      (ndGeom2ShiftedWideSymmetricLower b) full ∧
    ndFiniteAnyHit (ndGeom2ShiftedWideSymmetricDepths b)
      (ndGeom2ShiftedWideSymmetricHit b a) full

def ndGeom2ShiftedWideSymmetricMargin (b : ℕ) : ℝ :=
  ndGeom2ShiftedWideSymmetricMarginNat b

def ndGeom2ShiftedWideSymmetricCrossingError (b : ℕ) : ℝ :=
  2 * Real.exp
      (-min
        (ndGeom2ShiftedWideSymmetricMargin b ^ 2 /
          (32 * (ndGeom2ShiftedWideSymmetricLower b : ℝ)))
        (ndGeom2ShiftedWideSymmetricMargin b / 8)) +
    2 * Real.exp
      (-min
        (ndGeom2ShiftedWideSymmetricMargin b ^ 2 /
          (32 * (ndGeom2ShiftedWideSymmetricHorizon b : ℝ)))
        (ndGeom2ShiftedWideSymmetricMargin b / 8))

def ndGeom2ShiftedWideSymmetricCrossingProbability (b a : ℕ) : ℝ :=
  ((Tao.geom2PNatListPMF
      (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
    {full | ndGeom2ShiftedWideSymmetricCrossing b a full}).toReal

theorem ndGeom2ShiftedWideSymmetricWidth_le_base (b : ℕ) :
    ndGeom2ShiftedWideSymmetricWidth b ≤ b := by
  unfold ndGeom2ShiftedWideSymmetricWidth
  omega

theorem ndGeom2ShiftedWideSymmetricLower_le_horizon (b : ℕ) :
    ndGeom2ShiftedWideSymmetricLower b ≤
      ndGeom2ShiftedWideSymmetricHorizon b := by
  unfold ndGeom2ShiftedWideSymmetricLower
    ndGeom2ShiftedWideSymmetricHorizon
  omega

theorem ndGeom2ShiftedWideSymmetricHorizon_mem_depths (b : ℕ) :
    ndGeom2ShiftedWideSymmetricHorizon b ∈
      ndGeom2ShiftedWideSymmetricDepths b := by
  simp [ndGeom2ShiftedWideSymmetricDepths,
    ndGeom2ShiftedWideSymmetricLower_le_horizon]

@[simp] theorem ndGeom2ShiftedWideSymmetricLower_sub_base (b : ℕ) :
    ndGeom2ShiftedWideSymmetricLower b - b = 0 := by
  have hw := ndGeom2ShiftedWideSymmetricWidth_le_base b
  unfold ndGeom2ShiftedWideSymmetricLower
  omega

@[simp] theorem ndGeom2ShiftedWideSymmetricBase_sub_lower (b : ℕ) :
    b - ndGeom2ShiftedWideSymmetricLower b =
      ndGeom2ShiftedWideSymmetricWidth b := by
  have hw := ndGeom2ShiftedWideSymmetricWidth_le_base b
  unfold ndGeom2ShiftedWideSymmetricLower
  omega

@[simp] theorem ndGeom2ShiftedWideSymmetricHorizon_sub_base (b : ℕ) :
    ndGeom2ShiftedWideSymmetricHorizon b - b =
      ndGeom2ShiftedWideSymmetricWidth b := by
  unfold ndGeom2ShiftedWideSymmetricHorizon
  omega

@[simp] theorem ndGeom2ShiftedWideSymmetricBase_sub_horizon (b : ℕ) :
    b - ndGeom2ShiftedWideSymmetricHorizon b = 0 := by
  unfold ndGeom2ShiftedWideSymmetricHorizon
  omega

private theorem ndGeom2ShiftedWideSymmetricMarginNat_pos
    {b : ℕ} (hb : 200 ≤ b) :
    0 < ndGeom2ShiftedWideSymmetricMarginNat b := by
  unfold ndGeom2ShiftedWideSymmetricMarginNat
  omega

theorem ndGeom2ShiftedWideSymmetricMargin_pos
    {b : ℕ} (hb : 200 ≤ b) :
    0 < ndGeom2ShiftedWideSymmetricMargin b := by
  unfold ndGeom2ShiftedWideSymmetricMargin
  exact_mod_cast ndGeom2ShiftedWideSymmetricMarginNat_pos hb

private theorem ndGeom2ShiftedWideSymmetricGap_add_total (b : ℕ) :
    ndGeom2ShiftedWideSymmetricGap b +
        ndBalancedTotal (ndGeom2ShiftedWideSymmetricWidth b) =
      2 * ndGeom2ShiftedWideSymmetricWidth b := by
  unfold ndGeom2ShiftedWideSymmetricGap
  exact Nat.sub_add_cancel
    (ndBalancedTotal_le_two_mul
      (ndGeom2ShiftedWideSymmetricWidth b))

theorem ndGeom2ShiftedWideSymmetricShiftRadius_add_two_margin
    {b : ℕ} (hb : 200 ≤ b) :
    ndGeom2ShiftedWideSymmetricShiftRadius b +
        2 * ndGeom2ShiftedWideSymmetricMarginNat b =
      ndGeom2ShiftedWideSymmetricGap b := by
  let w := ndGeom2ShiftedWideSymmetricWidth b
  let m := ndGeom2ShiftedWideSymmetricMarginNat b
  let c := ndBalancedTotal w
  have hc : c ≤ 2 * w := by
    simpa only [c] using ndBalancedTotal_le_two_mul w
  have hslope : 5 * c ≤ 8 * w + 5 := by
    simpa only [c] using five_mul_ndBalancedTotal_le_eight_mul_add_five w
  have hroom : 10 * m + 5 ≤ 2 * w := by
    dsimp only [m, w]
    unfold ndGeom2ShiftedWideSymmetricMarginNat
      ndGeom2ShiftedWideSymmetricWidth
    omega
  have htwo : c + 2 * m ≤ 2 * w := by omega
  unfold ndGeom2ShiftedWideSymmetricShiftRadius
    ndGeom2ShiftedWideSymmetricGap
  dsimp only [w, m, c] at hc hslope hroom htwo ⊢
  omega

private theorem ndGeom2ShiftedWideSymmetric_endpoint_arithmetic
    {b a : ℕ} (hb : 200 ≤ b)
    (ha : a ≤ 2 * ndGeom2ShiftedWideSymmetricShiftRadius b) :
    let w := ndGeom2ShiftedWideSymmetricWidth b
    let l := ndGeom2ShiftedWideSymmetricLower b
    let u := ndGeom2ShiftedWideSymmetricHorizon b
    let m := ndGeom2ShiftedWideSymmetricMarginNat b
    let c := ndBalancedTotal w
    let r := ndGeom2ShiftedWideSymmetricShiftRadius b
    (2 * l + m + c + r < 2 * b + a) ∧
      (2 * b + c + a + m ≤ 2 * u + r) := by
  dsimp only
  have hw := ndGeom2ShiftedWideSymmetricWidth_le_base b
  have hlw :
      ndGeom2ShiftedWideSymmetricLower b +
          ndGeom2ShiftedWideSymmetricWidth b = b := by
    unfold ndGeom2ShiftedWideSymmetricLower
    exact Nat.sub_add_cancel hw
  have huw :
      ndGeom2ShiftedWideSymmetricHorizon b =
        b + ndGeom2ShiftedWideSymmetricWidth b := rfl
  have hgap := ndGeom2ShiftedWideSymmetricGap_add_total b
  have hr := ndGeom2ShiftedWideSymmetricShiftRadius_add_two_margin hb
  have hm := ndGeom2ShiftedWideSymmetricMarginNat_pos hb
  omega

private theorem centered_endpoint_bounds_imply_shiftedWide_crossing
    {b a : ℕ} (hb : 200 ≤ b)
    (ha : a ≤ 2 * ndGeom2ShiftedWideSymmetricShiftRadius b)
    {full : List ℕ+}
    (hlen : full.length = ndGeom2ShiftedWideSymmetricHorizon b)
    (hlower :
      |Tao.taoGeom2CenteredListWeight
          (full.take (ndGeom2ShiftedWideSymmetricLower b))| ≤
        ndGeom2ShiftedWideSymmetricMargin b)
    (hupper :
      |Tao.taoGeom2CenteredListWeight
          (full.take (ndGeom2ShiftedWideSymmetricHorizon b))| ≤
        ndGeom2ShiftedWideSymmetricMargin b) :
    ndGeom2ShiftedWideSymmetricCrossing b a full := by
  let l := ndGeom2ShiftedWideSymmetricLower b
  let u := ndGeom2ShiftedWideSymmetricHorizon b
  let w := ndGeom2ShiftedWideSymmetricWidth b
  let m := ndGeom2ShiftedWideSymmetricMarginNat b
  let c := ndBalancedTotal w
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  have hlu : l ≤ u := by
    simpa only [l, u] using ndGeom2ShiftedWideSymmetricLower_le_horizon b
  have htakeL : (full.take l).length = l := by
    rw [List.length_take, hlen]
    simpa only [l, u] using min_eq_left hlu
  have htakeU : (full.take u).length = u := by
    rw [List.length_take, hlen]
    simp only [u, min_self]
  have harith :
      (2 * l + m + c + r < 2 * b + a) ∧
        (2 * b + c + a + m ≤ 2 * u + r) := by
    simpa only [w, l, u, m, c, r] using
      ndGeom2ShiftedWideSymmetric_endpoint_arithmetic hb ha
  have hcenterLower :
      Tao.taoGeom2CenteredListWeight (full.take l) ≤ (m : ℝ) := by
    have := (le_abs_self _).trans hlower
    simpa only [ndGeom2ShiftedWideSymmetricMargin, m] using this
  have hcenterUpper :
      -(m : ℝ) ≤ Tao.taoGeom2CenteredListWeight (full.take u) := by
    have := (neg_le_neg hupper).trans (neg_abs_le _)
    simpa only [ndGeom2ShiftedWideSymmetricMargin, m] using this
  have hweightLowerReal :
      ((Tao.taoTupleWeight (full.take l) : ℕ) : ℝ) ≤
        2 * (l : ℝ) + (m : ℝ) := by
    unfold Tao.taoGeom2CenteredListWeight at hcenterLower
    rw [htakeL] at hcenterLower
    linarith
  have hweightLower :
      Tao.taoTupleWeight (full.take l) ≤ 2 * l + m := by
    exact_mod_cast hweightLowerReal
  have hweightUpperReal :
      2 * (u : ℝ) ≤
        (Tao.taoTupleWeight (full.take u) : ℝ) + (m : ℝ) := by
    unfold Tao.taoGeom2CenteredListWeight at hcenterUpper
    rw [htakeU] at hcenterUpper
    linarith
  have hweightUpper :
      2 * u ≤ Tao.taoTupleWeight (full.take u) + m := by
    exact_mod_cast hweightUpperReal
  have hlowerMiss :
      Tao.taoTupleWeight (full.take l) + c + r < 2 * b + a := by
    omega
  have hupperHit :
      2 * b + c + a ≤ Tao.taoTupleWeight (full.take u) + r := by
    omega
  constructor
  · unfold ndGeom2ShiftedWideSymmetricHit
    simpa only [l, w, c, r,
      ndGeom2ShiftedWideSymmetricLower_sub_base,
      ndGeom2ShiftedWideSymmetricBase_sub_lower,
      ndBalancedTotal_zero, Nat.add_zero] using
        (Nat.not_le_of_lt hlowerMiss)
  · refine ⟨u, ?_, ?_⟩
    · simpa only [u] using
        ndGeom2ShiftedWideSymmetricHorizon_mem_depths b
    · unfold ndGeom2ShiftedWideSymmetricHit
      simpa only [u, w, c, r,
        ndGeom2ShiftedWideSymmetricHorizon_sub_base,
        ndGeom2ShiftedWideSymmetricBase_sub_horizon,
        ndBalancedTotal_zero, Nat.add_zero] using hupperHit

private theorem shiftedWide_pmfOuterMass_toReal_mono
    {Omega : Type*} (p : PMF Omega) {E F : Set Omega}
    (hEF : E ⊆ F) :
    (p.toOuterMeasure E).toReal ≤ (p.toOuterMeasure F).toReal := by
  apply ENNReal.toReal_mono
  · apply ne_of_lt
    calc
      p.toOuterMeasure F ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ F)
      _ = 1 :=
        (p.toOuterMeasure_apply_eq_one_iff Set.univ).2
          (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  · exact p.toOuterMeasure.mono hEF

private theorem shiftedWide_one_sub_two_pmfOuterMass_le_compl_union
    {Omega : Type*} (p : PMF Omega) (E F : Set Omega) :
    1 - (p.toOuterMeasure E).toReal -
        (p.toOuterMeasure F).toReal ≤
      (p.toOuterMeasure ((E ∪ F)ᶜ)).toReal := by
  have huniv : p.toOuterMeasure Set.univ = 1 :=
    (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hfinite (A : Set Omega) : p.toOuterMeasure A ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      p.toOuterMeasure A ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ A)
      _ = 1 := huniv
  have hunion := MeasureTheory.measure_union_le
    (μ := p.toOuterMeasure) E F
  have hunionReal :
      (p.toOuterMeasure (E ∪ F)).toReal ≤
        (p.toOuterMeasure E).toReal +
          (p.toOuterMeasure F).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfinite E, hfinite F⟩) hunion
    simpa [ENNReal.toReal_add, hfinite] using h
  have hcar : p.toOuterMeasure.IsCaratheodory (E ∪ F) := by
    change @MeasurableSet Omega p.toOuterMeasure.caratheodory (E ∪ F)
    rw [PMF.toOuterMeasure_caratheodory]
    trivial
  have hsplitENN :
      p.toOuterMeasure Set.univ =
        p.toOuterMeasure (Set.univ ∩ (E ∪ F)) +
          p.toOuterMeasure (Set.univ \ (E ∪ F)) :=
    hcar Set.univ
  have hsplit :
      1 = (p.toOuterMeasure (E ∪ F)).toReal +
        (p.toOuterMeasure ((E ∪ F)ᶜ)).toReal := by
    have h := congrArg ENNReal.toReal hsplitENN
    simpa [huniv, ENNReal.toReal_add, hfinite, Set.diff_eq] using h
  linarith

private theorem shiftedWideLowerAbsTailMass_le
    {b : ℕ} (hb : 200 ≤ b) :
    ((Tao.geom2PNatListPMF
        (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
      {full |
        ndGeom2ShiftedWideSymmetricMargin b <
          |Tao.taoGeom2CenteredListWeight
            (full.take (ndGeom2ShiftedWideSymmetricLower b))|}).toReal ≤
      2 * Real.exp
        (-min
          (ndGeom2ShiftedWideSymmetricMargin b ^ 2 /
            (32 * (ndGeom2ShiftedWideSymmetricLower b : ℝ)))
          (ndGeom2ShiftedWideSymmetricMargin b / 8)) := by
  have hlPos : 0 < ndGeom2ShiftedWideSymmetricLower b := by
    unfold ndGeom2ShiftedWideSymmetricLower
      ndGeom2ShiftedWideSymmetricWidth
    omega
  change
    ((Tao.geom2PNatListPMF
        (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
      ((fun full => full.take (ndGeom2ShiftedWideSymmetricLower b)) ⁻¹'
        {as |
          ndGeom2ShiftedWideSymmetricMargin b <
            |Tao.taoGeom2CenteredListWeight as|})).toReal ≤ _
  rw [geom2PNatListPMF_take_event_outerMeasure_toReal
    (ndGeom2ShiftedWideSymmetricLower_le_horizon b)
    {as |
      ndGeom2ShiftedWideSymmetricMargin b <
        |Tao.taoGeom2CenteredListWeight as|}]
  exact Tao.geom2PNatListPMF_centeredWeight_absTail_le_min
    hlPos (ndGeom2ShiftedWideSymmetricMargin_pos hb)

private theorem shiftedWideHorizonAbsTailMass_le
    {b : ℕ} (hb : 200 ≤ b) :
    ((Tao.geom2PNatListPMF
        (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
      {full |
        ndGeom2ShiftedWideSymmetricMargin b <
          |Tao.taoGeom2CenteredListWeight
            (full.take (ndGeom2ShiftedWideSymmetricHorizon b))|}).toReal ≤
      2 * Real.exp
        (-min
          (ndGeom2ShiftedWideSymmetricMargin b ^ 2 /
            (32 * (ndGeom2ShiftedWideSymmetricHorizon b : ℝ)))
          (ndGeom2ShiftedWideSymmetricMargin b / 8)) := by
  have huPos : 0 < ndGeom2ShiftedWideSymmetricHorizon b := by
    unfold ndGeom2ShiftedWideSymmetricHorizon
      ndGeom2ShiftedWideSymmetricWidth
    omega
  change
    ((Tao.geom2PNatListPMF
        (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
      ((fun full => full.take (ndGeom2ShiftedWideSymmetricHorizon b)) ⁻¹'
        {as |
          ndGeom2ShiftedWideSymmetricMargin b <
            |Tao.taoGeom2CenteredListWeight as|})).toReal ≤ _
  rw [geom2PNatListPMF_take_event_outerMeasure_toReal
    (le_refl (ndGeom2ShiftedWideSymmetricHorizon b))
    {as |
      ndGeom2ShiftedWideSymmetricMargin b <
        |Tao.taoGeom2CenteredListWeight as|}]
  exact Tao.geom2PNatListPMF_centeredWeight_absTail_le_min
    huPos (ndGeom2ShiftedWideSymmetricMargin_pos hb)

theorem one_sub_shiftedWideSymmetricCrossingError_le_probability
    {b a : ℕ} (hb : 200 ≤ b)
    (ha : a ∈ ndGeom2ShiftedWideSymmetricShiftIndices b) :
    1 - ndGeom2ShiftedWideSymmetricCrossingError b ≤
      ndGeom2ShiftedWideSymmetricCrossingProbability b a := by
  let p := Tao.geom2PNatListPMF
    (ndGeom2ShiftedWideSymmetricHorizon b)
  let lowerBad : Set (List ℕ+) :=
    {full |
      ndGeom2ShiftedWideSymmetricMargin b <
        |Tao.taoGeom2CenteredListWeight
          (full.take (ndGeom2ShiftedWideSymmetricLower b))|}
  let upperBad : Set (List ℕ+) :=
    {full |
      ndGeom2ShiftedWideSymmetricMargin b <
        |Tao.taoGeom2CenteredListWeight
          (full.take (ndGeom2ShiftedWideSymmetricHorizon b))|}
  let good : Set (List ℕ+) := (lowerBad ∪ upperBad)ᶜ
  let crossing : Set (List ℕ+) :=
    {full | ndGeom2ShiftedWideSymmetricCrossing b a full}
  have haBound :
      a ≤ 2 * ndGeom2ShiftedWideSymmetricShiftRadius b :=
    (Finset.mem_Icc.mp ha).2
  have hlower := shiftedWideLowerAbsTailMass_le hb
  have hupper := shiftedWideHorizonAbsTailMass_le hb
  have hgoodBase := shiftedWide_one_sub_two_pmfOuterMass_le_compl_union
    p lowerBad upperBad
  have hgoodCross :
      (p.toOuterMeasure good).toReal ≤
        (p.toOuterMeasure crossing).toReal := by
    have hsupport : good ∩ p.support ⊆ crossing := by
      intro full hfull
      have hlen :
          full.length = ndGeom2ShiftedWideSymmetricHorizon b :=
        Tao.geom2PNatListPMF_support_length_eq hfull.2
      have hnot : full ∉ lowerBad ∪ upperBad := by
        simpa only [good, Set.mem_compl_iff] using hfull.1
      have hnotLower : full ∉ lowerBad := fun h => hnot (Or.inl h)
      have hnotUpper : full ∉ upperBad := fun h => hnot (Or.inr h)
      apply centered_endpoint_bounds_imply_shiftedWide_crossing
        hb haBound hlen
      · exact le_of_not_gt hnotLower
      · exact le_of_not_gt hnotUpper
    have hgoodEq : p.toOuterMeasure good =
        p.toOuterMeasure (good ∩ p.support) := by
      apply p.toOuterMeasure_apply_eq_of_inter_support_eq
      simp only [Set.inter_assoc, Set.inter_self]
    rw [hgoodEq]
    exact shiftedWide_pmfOuterMass_toReal_mono p hsupport
  have hgoodLower :
      1 - ndGeom2ShiftedWideSymmetricCrossingError b ≤
        (p.toOuterMeasure good).toReal := by
    unfold ndGeom2ShiftedWideSymmetricCrossingError
    simp only [p, lowerBad, upperBad, good] at hgoodBase ⊢
    linarith
  exact hgoodLower.trans (by
    simpa [p, crossing,
      ndGeom2ShiftedWideSymmetricCrossingProbability] using hgoodCross)

private theorem shiftedWide_commonExponent_le
    {b N : ℕ} (hb : 200 ≤ b) (hN : 0 < N)
    (hNle : N ≤ ndGeom2ShiftedWideSymmetricHorizon b) :
    (b : ℝ) / 2560000 ≤
      min
        (ndGeom2ShiftedWideSymmetricMargin b ^ 2 / (32 * (N : ℝ)))
        (ndGeom2ShiftedWideSymmetricMargin b / 8) := by
  let u := ndGeom2ShiftedWideSymmetricHorizon b
  let m := ndGeom2ShiftedWideSymmetricMarginNat b
  let lambda := ndGeom2ShiftedWideSymmetricMargin b
  have hbPos : (0 : ℝ) < b := by positivity
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmNat : b ≤ 200 * m := by
    dsimp only [m]
    unfold ndGeom2ShiftedWideSymmetricMarginNat
    omega
  have hmReal : (b : ℝ) / 200 ≤ lambda := by
    have hmCast : (b : ℝ) ≤ 200 * (m : ℝ) := by exact_mod_cast hmNat
    dsimp only [lambda]
    unfold ndGeom2ShiftedWideSymmetricMargin
    dsimp only [m] at hmCast ⊢
    linarith
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold ndGeom2ShiftedWideSymmetricMargin
    positivity
  have huNat : u ≤ 2 * b := by
    dsimp only [u]
    unfold ndGeom2ShiftedWideSymmetricHorizon
      ndGeom2ShiftedWideSymmetricWidth
    omega
  have hNReal : (N : ℝ) ≤ 2 * (b : ℝ) := by
    exact_mod_cast hNle.trans huNat
  have hquad :
      (b : ℝ) / 2560000 ≤ lambda ^ 2 / (32 * (N : ℝ)) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 32 * (N : ℝ))]
    have h32N : 32 * (N : ℝ) ≤ 64 * (b : ℝ) := by
      nlinarith
    calc
      (b : ℝ) / 2560000 * (32 * (N : ℝ)) ≤
          (b : ℝ) / 2560000 * (64 * (b : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h32N (by positivity)
      _ = ((b : ℝ) / 200) ^ 2 := by ring
      _ ≤ lambda ^ 2 := by
        nlinarith [sq_nonneg (lambda - (b : ℝ) / 200)]
  have hlinear : (b : ℝ) / 2560000 ≤ lambda / 8 := by
    calc
      (b : ℝ) / 2560000 ≤ (b : ℝ) / 1600 := by nlinarith
      _ ≤ lambda / 8 := by linarith
  exact le_min hquad hlinear

theorem shiftedWideSymmetricCrossingError_le_four_mul_exp
    {b : ℕ} (hb : 200 ≤ b) :
    ndGeom2ShiftedWideSymmetricCrossingError b ≤
      4 * Real.exp (-(b : ℝ) / 2560000) := by
  have hlPos : 0 < ndGeom2ShiftedWideSymmetricLower b := by
    unfold ndGeom2ShiftedWideSymmetricLower
      ndGeom2ShiftedWideSymmetricWidth
    omega
  have huPos : 0 < ndGeom2ShiftedWideSymmetricHorizon b := by
    unfold ndGeom2ShiftedWideSymmetricHorizon
      ndGeom2ShiftedWideSymmetricWidth
    omega
  have hlExp := shiftedWide_commonExponent_le hb hlPos
    (ndGeom2ShiftedWideSymmetricLower_le_horizon b)
  have huExp := shiftedWide_commonExponent_le hb huPos (le_refl _)
  have hlTail :
      Real.exp
          (-min
            (ndGeom2ShiftedWideSymmetricMargin b ^ 2 /
              (32 * (ndGeom2ShiftedWideSymmetricLower b : ℝ)))
            (ndGeom2ShiftedWideSymmetricMargin b / 8)) ≤
        Real.exp (-(b : ℝ) / 2560000) := by
    apply Real.exp_le_exp.mpr
    linarith
  have huTail :
      Real.exp
          (-min
            (ndGeom2ShiftedWideSymmetricMargin b ^ 2 /
              (32 * (ndGeom2ShiftedWideSymmetricHorizon b : ℝ)))
            (ndGeom2ShiftedWideSymmetricMargin b / 8)) ≤
        Real.exp (-(b : ℝ) / 2560000) := by
    apply Real.exp_le_exp.mpr
    linarith
  unfold ndGeom2ShiftedWideSymmetricCrossingError
  nlinarith

theorem one_sub_four_mul_exp_le_shiftedWideSymmetricCrossingProbability
    {b a : ℕ} (hb : 200 ≤ b)
    (ha : a ∈ ndGeom2ShiftedWideSymmetricShiftIndices b) :
    1 - 4 * Real.exp (-(b : ℝ) / 2560000) ≤
      ndGeom2ShiftedWideSymmetricCrossingProbability b a := by
  have hrate :=
    one_sub_shiftedWideSymmetricCrossingError_le_probability hb ha
  have herr := shiftedWideSymmetricCrossingError_le_four_mul_exp hb
  linarith

end

end PositiveDensity

end ND

end Erdos1135Predecessor
