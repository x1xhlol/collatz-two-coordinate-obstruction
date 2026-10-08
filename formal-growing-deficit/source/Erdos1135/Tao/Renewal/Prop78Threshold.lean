import Erdos1135.Tao.Renewal.QmStatement

/-!
# Section 7 Proposition 7.8 Threshold Surface

This module records the real source threshold parameter `C_{A,epsilon}` for
Proposition 7.8 separately from the local lower-bound helper used by the
checked source-`Q_m` monotonicity consumer.  It does not prove the existence or
size of `C_{A,epsilon}`, the boundary estimate `(7.41)`, Proposition 7.8, or
any case estimate.
-/

namespace Erdos1135
namespace Tao

/--
Threshold surface for the future sufficiently large constant `C_{A,epsilon}`.
For now it only stores the minimal fact needed to feed the deterministic
monotonicity consumer; later case estimates can strengthen or refine this
surface without changing the source `Q_m` API.
-/
structure TaoSection7Prop78Threshold
    (A : ℕ) (epsilon : ℝ) (C : ℕ) : Prop where
  lowerThreshold_le : taoSection7Prop78LowerThreshold ≤ C

/-- Alias carrying the source-checker name for the `C_{A,epsilon}` threshold gate. -/
def prop78_threshold_CAepsilon
    (A : ℕ) (epsilon : ℝ) (C : ℕ) : Prop :=
  TaoSection7Prop78Threshold A epsilon C

theorem taoSection7Prop78LowerThreshold_le_of_threshold
    {A C : ℕ} {epsilon : ℝ}
    (hC : TaoSection7Prop78Threshold A epsilon C) :
    taoSection7Prop78LowerThreshold ≤ C :=
  hC.lowerThreshold_le

theorem taoSection7Prop78Threshold_to_lowerThreshold
    {A C m : ℕ} {epsilon : ℝ}
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hm_low : C ≤ m) :
    taoSection7Prop78LowerThreshold ≤ m :=
  le_trans (taoSection7Prop78LowerThreshold_le_of_threshold hC) hm_low

/--
Thresholded boundary-estimate statement surface for `(7.41)`.  This theorem
only repackages a supplied boundary estimate under the real `C_{A,epsilon}`
range hypotheses; it does not prove the estimate.
-/
theorem taoSection7Prop78_boundary741
    {n A C m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hm_low : C ≤ m)
    (hm_hi : m ≤ n / 2)
    (hboundary741 : ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) :
    ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  have _hm_local : taoSection7Prop78LowerThreshold ≤ m :=
    taoSection7Prop78Threshold_to_lowerThreshold hC hm_low
  have _hm_hi : m ≤ n / 2 := hm_hi
  intro p hp
  exact hboundary741 p hp

/--
Source-range monotonicity `(7.40)` as a deterministic consumer of a future
thresholded boundary estimate `(7.41)`.
-/
theorem taoSection7_prop78_monotonicity_740
    {n A C m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hm_low : C ≤ m)
    (hm_hi : m ≤ n / 2)
    (hboundary741 : ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) :
    taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
      taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  exact taoSection7SourceProp78Monotonicity
    (n := n) (A := A) (m := m) (xi := xi) (epsilon := epsilon)
    hepsilon
    (taoSection7Prop78Threshold_to_lowerThreshold hC hm_low)
    hm_hi
    (taoSection7Prop78_boundary741
      (n := n) (A := A) (C := C) (m := m)
      (xi := xi) (epsilon := epsilon)
      hC hm_low hm_hi hboundary741)

end Tao
end Erdos1135
