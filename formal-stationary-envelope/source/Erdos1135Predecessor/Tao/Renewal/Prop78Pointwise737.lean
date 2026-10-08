/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageLocalizedMass
import Erdos1135Predecessor.Tao.Renewal.Prop78ActiveCover
import Erdos1135Predecessor.Tao.Renewal.Prop78Case1White
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2Expectation
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2Geometry
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3EventualScale
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3PriorityScalar
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshCloseout
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarUniform
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshMiddleMass
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOuterBadJ
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeBoundary
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshPriorityPartition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoSection7SourceQm_le_max_pow_of_bounded01
    {J A m : ℕ} {Q : TaoSection7Q}
    (hQ : TaoSection7QBounded01 Q) :
    taoSection7SourceQm J A Q m ≤
      ((max m 1 : ℕ) : ℝ) ^ A := by
  unfold taoSection7SourceQm
  exact csSup_le
    (taoSection7QmValueSet_nonempty J A Q m)
    (by
      intro x hx
      rcases hx with ⟨p, hp, rfl⟩
      exact taoSection7QmWeightedValue_le_max_pow_of_bounded01
        (J := J) (A := A) (m := m) (Q := Q) hQ hp)

theorem taoSection7SourceActualQmAtCutoff_le_max_pow
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
      ((max m 1 : ℕ) : ℝ) ^ A := by
  unfold taoSection7SourceActualQmAtCutoff taoSection7SourceActualQm
  exact taoSection7SourceQm_le_max_pow_of_bounded01
    (J := n / 2) (A := A) (m := m)
    (Q := taoSection7SourceActualQ n xi epsilon)
    (taoSection7SourceActualQ_bounded01
      (n := n) (xi := xi) hepsilon)

theorem taoSection7SourceActualQ_weighted_le_QmAtCutoff
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmTail (n / 2) m p) :
    (taoSection7QDistanceToCutoff (n / 2) p : ℝ) ^ A *
        taoSection7SourceActualQ n xi epsilon p ≤
      taoSection7SourceActualQmAtCutoff n A m xi epsilon := by
  have hbdd := taoSection7QmValueSet_bddAbove_of_bounded01
    (J := n / 2) (A := A) (m := m)
    (Q := taoSection7SourceActualQ n xi epsilon)
    (taoSection7SourceActualQ_bounded01
      (n := n) (xi := xi) hepsilon)
  have hweighted := taoSection7QmWeightedValue_le_sourceQm
    (J := n / 2) (A := A) (k := m)
    (Q := taoSection7SourceActualQ n xi epsilon) hbdd hp
  simpa [taoSection7QmWeightedValue,
    taoSection7SourceActualQmAtCutoff,
    taoSection7SourceActualQm] using hweighted

theorem
    taoSection7SourceActualQmAtCutoff_le_threshold_pow_of_monotonicity
    {n A C : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hmono : ∀ m : ℕ, C ≤ m → m ≤ n / 2 →
      taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) :
    ∀ m : ℕ, m ≤ n / 2 →
      taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
        (C : ℝ) ^ A := by
  have honeC : 1 ≤ C := by
    simpa [taoSection7Prop78LowerThreshold] using hC.lowerThreshold_le
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm_hi
      by_cases hmC : m ≤ C
      · have hmaxC : max m 1 ≤ C := max_le hmC honeC
        calc
          taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
              ((max m 1 : ℕ) : ℝ) ^ A :=
            taoSection7SourceActualQmAtCutoff_le_max_pow hepsilon
          _ ≤ (C : ℝ) ^ A :=
            pow_le_pow_left₀ (Nat.cast_nonneg _)
              (Nat.cast_le.mpr hmaxC) A
      · have hCm : C ≤ m := by omega
        exact
          (hmono m hCm hm_hi).trans
            (ih (m - 1) (by omega) (by omega))

end

end Tao

end Erdos1135Predecessor
