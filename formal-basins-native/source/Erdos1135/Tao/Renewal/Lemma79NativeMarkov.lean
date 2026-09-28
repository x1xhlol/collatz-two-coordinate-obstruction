import Erdos1135.Tao.Renewal.Lemma79AllRBound

/-!
# Lemma 7.9 Countable Native Markov Bound

This proof leaf turns the native `ENNReal` expectation bound into an event
bound under `PMF.toOuterMeasure`.  It stays countable and does not pass through
the finite-`Fintype` real expectation packet used by older Case 3 scaffolding.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Division-free Markov inequality for a native nonnegative PMF payload on
an arbitrary sample type. -/
theorem lemma79_pmfToOuterMeasure_gt_mul_le_expectation
    {Omega : Type*} (mu : PMF Omega)
    (F : Omega -> ENNReal) (cutoff : ENNReal) :
    mu.toOuterMeasure {omega | cutoff < F omega} * cutoff ≤
      lemma79PMFENNExpectation mu F := by
  let Event : Set Omega := {omega | cutoff < F omega}
  rw [← lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure]
  rw [← lemma79PMFENNExpectation_mul_const]
  unfold lemma79PMFENNExpectation
  apply ENNReal.tsum_le_tsum
  intro omega
  by_cases hEvent : omega ∈ Event
  · have hcutoff : cutoff ≤ F omega := le_of_lt hEvent
    have hmem : cutoff < F omega := by simpa [Event] using hEvent
    simp only [Set.indicator, Set.mem_setOf_eq, hmem, if_true, one_mul]
    change mu omega * cutoff ≤ mu omega * F omega
    exact mul_le_mul_left' hcutoff _
  · have hnot : ¬ cutoff < F omega := by simpa [Event] using hEvent
    simp [Set.indicator, hnot]

/-- Inclusive division-free Markov inequality.  This sibling is required for
source events whose threshold equality belongs to the bad event. -/
theorem lemma79_pmfToOuterMeasure_le_mul_le_expectation
    {Omega : Type*} (mu : PMF Omega)
    (F : Omega -> ENNReal) (cutoff : ENNReal) :
    mu.toOuterMeasure {omega | cutoff ≤ F omega} * cutoff ≤
      lemma79PMFENNExpectation mu F := by
  let Event : Set Omega := {omega | cutoff ≤ F omega}
  rw [← lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure]
  rw [← lemma79PMFENNExpectation_mul_const]
  unfold lemma79PMFENNExpectation
  apply ENNReal.tsum_le_tsum
  intro omega
  by_cases hEvent : omega ∈ Event
  · have hcutoff : cutoff ≤ F omega := by simpa [Event] using hEvent
    simp only [Set.indicator, Set.mem_setOf_eq, hcutoff, if_true, one_mul]
    exact mul_le_mul_left' hcutoff _
  · have hnot : ¬ cutoff ≤ F omega := by simpa [Event] using hEvent
    simp [Set.indicator, hnot]

/-- Scaled native Markov inequality.  Only the common expectation base is
cancelled; the scale may be any extended nonnegative real. -/
theorem lemma79_pmfToOuterMeasure_base_mul_scale_gt_le_inv
    {Omega : Type*} (mu : PMF Omega)
    (F : Omega -> ENNReal) (base scale : ENNReal)
    (hbase0 : base ≠ 0) (hbaseTop : base ≠ ⊤)
    (hmean : lemma79PMFENNExpectation mu F ≤ base) :
    mu.toOuterMeasure {omega | base * scale < F omega} ≤ scale⁻¹ := by
  have hmarkov :=
    lemma79_pmfToOuterMeasure_gt_mul_le_expectation
      mu F (base * scale)
  have hbaseMul :
      base *
          (mu.toOuterMeasure {omega | base * scale < F omega} * scale) ≤
        base := by
    calc
      _ = mu.toOuterMeasure {omega | base * scale < F omega} *
            (base * scale) := by ac_rfl
      _ ≤ lemma79PMFENNExpectation mu F := hmarkov
      _ ≤ base := hmean
  have hmassScale :
      mu.toOuterMeasure {omega | base * scale < F omega} * scale ≤ 1 := by
    apply (ENNReal.mul_le_mul_iff_right hbase0 hbaseTop).mp
    simpa using hbaseMul
  have hdiv :
      mu.toOuterMeasure {omega | base * scale < F omega} ≤ 1 / scale :=
    (ENNReal.le_div_iff_mul_le
      (a := mu.toOuterMeasure {omega | base * scale < F omega})
      (b := scale) (c := (1 : ENNReal))
      (Or.inr one_ne_zero)
      (Or.inr (by simp : (1 : ENNReal) ≠ ⊤))).2
      hmassScale
  simpa [one_div] using hdiv

/-- For every fixed repaired index, the canonical shifted tail event has
native mass at most the reciprocal of its power-of-ten scale. -/
theorem lemma79_canonical_tailEvent_outerMeasure_le_inv_pow
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (R k : ℕ) (origin : TaoSection7RenewalPoint) :
    let J := n / 2
    let family := taoSection7CanonicalTriangleFamily hxi hscalar
    let moment := lemma79HoldPathCutoffTailMomentENN origin family
      n xi epsilon J R
    let base := ENNReal.ofReal (Real.exp epsilon)
    let scale := (10 : ENNReal) ^ k
    (taoSection7HoldListPMF J).toOuterMeasure
        {full | scale * base < moment full} ≤
      scale⁻¹ := by
  dsimp only
  let family := taoSection7CanonicalTriangleFamily hxi hscalar
  let moment := lemma79HoldPathCutoffTailMomentENN origin family
    n xi epsilon (n / 2) R
  let base := ENNReal.ofReal (Real.exp epsilon)
  let scale := (10 : ENNReal) ^ k
  have hbase0 : base ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos epsilon)).ne'
  have hbaseTop : base ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmean :
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF (n / 2)) moment ≤ base := by
    simpa [moment, base, family] using
      (lemma79_canonical_all_R
        L hlocalizedMass hxi hscalar hcollar R origin)
  simpa [moment, base, scale, family, mul_comm] using
    (lemma79_pmfToOuterMeasure_base_mul_scale_gt_le_inv
      (taoSection7HoldListPMF (n / 2)) moment base scale
      hbase0 hbaseTop hmean)

/-- Shifted Case 3 `FSlack` exponent form of the canonical native Markov
bound. -/
theorem lemma79_canonical_shiftedFSlack_outerMeasure_le
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (R Amarkov Aweight : ℕ)
    (hAmarkov : Amarkov = Aweight + 1)
    (origin : TaoSection7RenewalPoint) :
    let J := n / 2
    let family := taoSection7CanonicalTriangleFamily hxi hscalar
    let moment := lemma79HoldPathCutoffTailMomentENN origin family
      n xi epsilon J R
    (taoSection7HoldListPMF J).toOuterMeasure
        {full |
          (10 : ENNReal) ^ (Amarkov + 2) *
              ENNReal.ofReal (Real.exp epsilon) <
            moment full} ≤
      ((10 : ENNReal) ^ (Aweight + 3))⁻¹ := by
  subst Amarkov
  simpa [Nat.add_assoc] using
    (lemma79_canonical_tailEvent_outerMeasure_le_inv_pow
      L hlocalizedMass hxi hscalar hcollar R (Aweight + 1 + 2) origin)

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
