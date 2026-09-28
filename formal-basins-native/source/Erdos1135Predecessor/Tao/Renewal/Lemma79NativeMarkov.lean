/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79AllRBound

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

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

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
