/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79Case3EventAdapter
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshDomain

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

noncomputable def lemma79CanonicalEndpointFreshFSlackEvent
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (R Amarkov : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  {atom |
    atom.2 ∈ lemma79CanonicalFSlackEvent
      (lemma79EndpointFreshOrigin entry atom)
      family n xi epsilon (n / 2) R Amarkov}

theorem lemma79CanonicalEndpointFreshFSlackEvent_eq_native
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (R Amarkov : ℕ) :
    lemma79CanonicalEndpointFreshFSlackEvent
        entry family n xi epsilon R Amarkov =
      {atom |
        (10 : ENNReal) ^ (Amarkov + 2) *
              ENNReal.ofReal (Real.exp epsilon) <
          lemma79HoldPathCutoffTailMomentENN
            (lemma79EndpointFreshOrigin entry atom)
            family n xi epsilon (n / 2) R atom.2} := by
  ext atom
  change
    atom.2 ∈ lemma79CanonicalFSlackEvent
        (lemma79EndpointFreshOrigin entry atom)
        family n xi epsilon (n / 2) R Amarkov ↔ _
  rw [lemma79CanonicalFSlackEvent_eq_native]
  rfl

theorem lemma79CanonicalEndpointFreshPMF_fSlackEvent_outerMeasure_le
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
    (entry : TaoSection7RenewalPoint) (gap R Amarkov Aweight : ℕ)
    (hAmarkov : Amarkov = Aweight + 1) :
    (lemma79CanonicalEndpointFreshPMF (n / 2) entry gap).toOuterMeasure
        (lemma79CanonicalEndpointFreshFSlackEvent entry
          (taoSection7CanonicalTriangleFamily hxi hscalar)
          n xi epsilon R Amarkov) ≤
      ENNReal.ofReal (1 / ((10 : ℝ) ^ (Aweight + 3))) := by
  subst Amarkov
  let μ := lemma79CanonicalEndpointFreshPMF (n / 2) entry gap
  let family := taoSection7CanonicalTriangleFamily hxi hscalar
  let moment :
      ((ℕ × ℤ) × List TaoSection7RenewalPoint) → ENNReal :=
    fun atom =>
      lemma79HoldPathCutoffTailMomentENN
        (lemma79EndpointFreshOrigin entry atom)
        family n xi epsilon (n / 2) R atom.2
  let base := ENNReal.ofReal (Real.exp epsilon)
  let scale := (10 : ENNReal) ^ (Aweight + 1 + 2)
  have hbase0 : base ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos epsilon)).ne'
  have hbaseTop : base ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmean : lemma79PMFENNExpectation μ moment ≤ base := by
    simpa [μ, moment, base, family, lemma79EndpointFreshOrigin] using
      (lemma79CanonicalEndpointFreshPMF_all_R
        L hlocalizedMass hxi hscalar hcollar entry gap R)
  rw [lemma79CanonicalEndpointFreshFSlackEvent_eq_native]
  calc
    μ.toOuterMeasure {atom | scale * base < moment atom} ≤ scale⁻¹ := by
      simpa [mul_comm] using
        (lemma79_pmfToOuterMeasure_base_mul_scale_gt_le_inv
          μ moment base scale hbase0 hbaseTop hmean)
    _ = ENNReal.ofReal (1 / ((10 : ℝ) ^ (Aweight + 3))) := by
      dsimp [scale]
      rw [show Aweight + 1 + 2 = Aweight + 3 by omega]
      rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
