/- This local copy changes proof tactics only to satisfy the pinned toolchain linters.
   The theorem statements are unchanged; see provenance/native-linter-patches.json. -/

import Erdos1135.Tao.Renewal.HoldListHorizontalMoment
import Erdos1135.Tao.Renewal.Lemma79NativeMarkov
import Erdos1135.Tao.Renewal.Prop78Case2MomentScalar

/-!
# Inclusive Horizontal Tail of an IID Hold List

This leaf applies the exact horizontal MGF at rate `1/16` to the inclusive
suffix event in Tao's outer `(7.54)` split.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

namespace TaoSection7Lemma77

/-- A length-`P` iid Hold block has the inclusive horizontal tail needed by
the suffix half of the outer large-horizontal event. -/
theorem taoSection7HoldListPMF_horizontalTail_outerMeasure_le
    (P m : ℕ) :
    (taoSection7HoldListPMF P).toOuterMeasure
        {fresh | m ≤ 10 * lemma77HoldPrefixHorizontalDelta P fresh} ≤
      ENNReal.ofReal
        (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) := by
  let t : ℝ := 1 / 16
  let F : List TaoSection7RenewalPoint → ENNReal := fun fresh =>
    ENNReal.ofReal
      (Real.exp (t * (lemma77HoldPrefixHorizontalDelta P fresh : ℝ)))
  let cutoff : ENNReal := ENNReal.ofReal (Real.exp ((m : ℝ) / 160))
  let Event : Set (List TaoSection7RenewalPoint) :=
    {fresh | m ≤ 10 * lemma77HoldPrefixHorizontalDelta P fresh}
  have hscalar := taoSection7Geom4ExpMoment_le_exp_eight_mul
    (t := t) (by norm_num [t]) (by norm_num [t])
  have hmgf := taoSection7HoldListPMF_horizontalExpMoment_ennreal
    P hscalar.1
  have hmean :
      lemma79PMFENNExpectation (taoSection7HoldListPMF P) F ≤
        ENNReal.ofReal (Real.exp ((P : ℝ) / 2)) := by
    unfold lemma79PMFENNExpectation
    change (∑' fresh, taoSection7HoldListPMF P fresh * F fresh) ≤ _
    rw [show (∑' fresh, taoSection7HoldListPMF P fresh * F fresh) =
        ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ P by
      simpa [F, t] using hmgf]
    calc
      ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ P ≤
          ENNReal.ofReal (Real.exp (8 * t)) ^ P :=
        pow_le_pow_left' (ENNReal.ofReal_le_ofReal hscalar.2) P
      _ = ENNReal.ofReal ((Real.exp (8 * t)) ^ P) := by
        rw [ENNReal.ofReal_pow (Real.exp_nonneg _)]
      _ = ENNReal.ofReal (Real.exp ((P : ℝ) / 2)) := by
        congr 1
        rw [← Real.exp_nat_mul]
        dsimp [t]
        ring_nf
  have hsubset :
      Event ⊆ {fresh | cutoff ≤ F fresh} := by
    intro fresh hfresh
    have hcast :
        (m : ℝ) ≤
          10 * (lemma77HoldPrefixHorizontalDelta P fresh : ℝ) := by
      exact_mod_cast hfresh
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    dsimp [cutoff, F, t]
    nlinarith
  have hmarkov := lemma79_pmfToOuterMeasure_le_mul_le_expectation
    (taoSection7HoldListPMF P) F cutoff
  have hmul :
      (taoSection7HoldListPMF P).toOuterMeasure Event * cutoff ≤
        ENNReal.ofReal (Real.exp ((P : ℝ) / 2)) := by
    calc
      (taoSection7HoldListPMF P).toOuterMeasure Event * cutoff ≤
          (taoSection7HoldListPMF P).toOuterMeasure
              {fresh | cutoff ≤ F fresh} * cutoff :=
        mul_le_mul_left ((taoSection7HoldListPMF P).toOuterMeasure.mono hsubset) _
      _ ≤ lemma79PMFENNExpectation (taoSection7HoldListPMF P) F := hmarkov
      _ ≤ ENNReal.ofReal (Real.exp ((P : ℝ) / 2)) := hmean
  have hcutoff0 : cutoff ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hcutoffTop : cutoff ≠ ⊤ := ENNReal.ofReal_ne_top
  have htargetMul :
      ENNReal.ofReal
          (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) * cutoff =
        ENNReal.ofReal (Real.exp ((P : ℝ) / 2)) := by
    dsimp [cutoff]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  apply (ENNReal.mul_le_mul_iff_right hcutoff0 hcutoffTop).mp
  change cutoff *
      (taoSection7HoldListPMF P).toOuterMeasure Event ≤
    cutoff * ENNReal.ofReal
      (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)))
  calc
    cutoff * (taoSection7HoldListPMF P).toOuterMeasure Event =
        (taoSection7HoldListPMF P).toOuterMeasure Event * cutoff := by
      ac_rfl
    _ ≤
        ENNReal.ofReal (Real.exp ((P : ℝ) / 2)) := hmul
    _ = ENNReal.ofReal
          (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) * cutoff :=
      htargetMul.symm
    _ = cutoff * ENNReal.ofReal
          (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) := by
      ac_rfl

/-- Real-mass projection of the inclusive iid Hold-list horizontal tail. -/
theorem taoSection7HoldListPMF_horizontalTail_toReal_le
    (P m : ℕ) :
    ((taoSection7HoldListPMF P).toOuterMeasure
        {fresh | m ≤ 10 * lemma77HoldPrefixHorizontalDelta P fresh}).toReal ≤
      Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) := by
  calc
    ((taoSection7HoldListPMF P).toOuterMeasure
        {fresh | m ≤ 10 * lemma77HoldPrefixHorizontalDelta P fresh}).toReal ≤
      (ENNReal.ofReal
        (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (taoSection7HoldListPMF_horizontalTail_outerMeasure_le P m)
    _ = Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) :=
      ENNReal.toReal_ofReal (Real.exp_nonneg _)

end TaoSection7Lemma77

end

end Tao
end Erdos1135
