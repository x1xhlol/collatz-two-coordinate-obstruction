/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.PMFExpectationThreeRegion
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshCloseout

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

def lemma79CanonicalEndpointFreshOuterBadJEvent
    (P m : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  taoSection7Case3Outer754LargeHorizontalEvent
    (lemma79EndpointFreshHorizontalAdvance P) m

def lemma79CanonicalEndpointFreshCutoffW
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (entry : TaoSection7RenewalPoint)
    (atom : (ℕ × ℤ) × List TaoSection7RenewalPoint)
    (q : ℕ) : Prop :=
  taoSection7Case3SourceCutoffPointW
    (lemma79EndpointFreshPointAt entry atom)
    n xi epsilon (n / 2) q

noncomputable def lemma79CanonicalEndpointFreshLowWhiteEvent
    (n P T : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (entry : TaoSection7RenewalPoint) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  taoSection7Case3LowWhiteEvent
    (lemma79CanonicalEndpointFreshCutoffW n xi epsilon entry) P T

theorem
    lemma79CanonicalEndpointFreshPMF_outer754Weight_summable_and_le_priorityPartition
    {n A m P T : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m)
    (hthreshold :
      (10 : ℝ) * (A : ℝ) ≤ epsilon ^ 3 * ((T + 1 : ℕ) : ℝ))
    (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    let μ := lemma79CanonicalEndpointFreshPMF (n / 2) entry gap
    let Bad := lemma79CanonicalEndpointFreshOuterBadJEvent P m
    let Low :=
      lemma79CanonicalEndpointFreshLowWhiteEvent
        n P T xi epsilon entry
    let weight :=
      lemma79EndpointFreshOuter754Weight
        n A m P xi epsilon entry
    Summable (fun atom => (μ atom).toReal * weight atom) ∧
      taoSection7PMFExpectation μ weight ≤
        (m : ℝ) ^ A * (μ.toOuterMeasure Bad).toReal +
          (10 : ℝ) ^ A * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
            ((10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ)))) *
              (μ.toOuterMeasure ((Bad ∪ Low)ᶜ)).toReal := by
  classical
  dsimp only
  let μ := lemma79CanonicalEndpointFreshPMF (n / 2) entry gap
  let Jtot := lemma79EndpointFreshHorizontalAdvance P
  let W := lemma79CanonicalEndpointFreshCutoffW n xi epsilon entry
  let Bad := lemma79CanonicalEndpointFreshOuterBadJEvent P m
  let Low :=
    lemma79CanonicalEndpointFreshLowWhiteEvent n P T xi epsilon entry
  let H := taoSection7Case3Outer754HorizontalFactor A m Jtot
  let E := taoSection7Case3Outer754SourceExponentialFactor P epsilon W
  let weight :=
    lemma79EndpointFreshOuter754Weight n A m P xi epsilon entry
  have hweight : ∀ atom, weight atom = E atom * H atom := by
    intro atom
    rfl
  have hE0 : ∀ atom, 0 ≤ E atom := by
    intro atom
    dsimp [E, taoSection7Case3Outer754SourceExponentialFactor,
      taoSection7Case3Outer754ExponentialFactor]
    positivity
  have hE1 : ∀ atom, E atom ≤ 1 := by
    intro atom
    dsimp [E, taoSection7Case3Outer754SourceExponentialFactor,
      taoSection7Case3Outer754ExponentialFactor]
    rw [Real.exp_le_one_iff]
    have hepsilon3 : 0 ≤ epsilon ^ 3 := pow_nonneg hepsilon 3
    have hcount :
        0 ≤ (taoSection7Case3WindowWhiteCount (W atom) P : ℝ) := by
      positivity
    nlinarith [mul_nonneg hepsilon3 hcount]
  have hH0 : ∀ atom, 0 ≤ H atom := by
    intro atom
    exact taoSection7Case3Outer754HorizontalFactor_nonneg atom
  have hHm : ∀ atom, H atom ≤ (m : ℝ) ^ A := by
    simpa [H, Jtot] using
      (taoSection7Case3Outer754HorizontalFactor_le_m_pow
        (A := A) (m := m) (Jtot := Jtot) hm)
  have hHmid : ∀ atom, atom ∉ Bad → H atom ≤ (10 : ℝ) ^ A := by
    simpa [H, Bad, Jtot, lemma79CanonicalEndpointFreshOuterBadJEvent] using
      (taoSection7Case3Outer754HorizontalFactor_le_ten_pow_of_not_largeHorizontal
        (A := A) (m := m) (Jtot := Jtot) hm)
  have hEtail :
      ∀ atom, atom ∉ Low →
        E atom ≤ Real.exp (-((10 : ℝ) * (A : ℝ))) := by
    intro atom hnotLow
    dsimp [E, taoSection7Case3Outer754SourceExponentialFactor,
      taoSection7Case3Outer754ExponentialFactor]
    rw [Real.exp_le_exp]
    have hcountNat :
        T + 1 ≤ taoSection7Case3WindowWhiteCount (W atom) P := by
      exact taoSection7Case3WindowWhiteCount_succ_le_of_not_lowWhiteEvent
        (by simpa [Low, lemma79CanonicalEndpointFreshLowWhiteEvent] using
          hnotLow)
    have hcount :
        ((T + 1 : ℕ) : ℝ) ≤
          (taoSection7Case3WindowWhiteCount (W atom) P : ℝ) := by
      exact_mod_cast hcountNat
    have hepsilon3 : 0 ≤ epsilon ^ 3 := pow_nonneg hepsilon 3
    have hmul :=
      mul_le_mul_of_nonneg_left hcount hepsilon3
    nlinarith [hthreshold, hmul]
  have hpartition :=
    taoSection7PMFExpectation_summable_and_le_threeRegion
      μ Bad Low weight
      (badCap := (m : ℝ) ^ A)
      (lowCap := (10 : ℝ) ^ A)
      (goodCap :=
        (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))))
      (by positivity) (by positivity) (by positivity)
      (fun atom _ => by
        rw [hweight]
        exact mul_nonneg (hE0 atom) (hH0 atom))
      (fun atom _ _ => by
        rw [hweight]
        calc
          E atom * H atom ≤ 1 * (m : ℝ) ^ A :=
            mul_le_mul (hE1 atom) (hHm atom) (hH0 atom) (by norm_num)
          _ = (m : ℝ) ^ A := one_mul _)
      (fun atom _ hnotBad _ => by
        rw [hweight]
        calc
          E atom * H atom ≤ 1 * (10 : ℝ) ^ A :=
            mul_le_mul (hE1 atom) (hHmid atom hnotBad)
              (hH0 atom) (by norm_num)
          _ = (10 : ℝ) ^ A := one_mul _)
      (fun atom _ hnotBad hnotLow => by
        rw [hweight]
        calc
          E atom * H atom ≤
              Real.exp (-((10 : ℝ) * (A : ℝ))) * (10 : ℝ) ^ A :=
            mul_le_mul (hEtail atom hnotLow) (hHmid atom hnotBad)
              (hH0 atom) (Real.exp_nonneg _)
          _ = (10 : ℝ) ^ A *
              Real.exp (-((10 : ℝ) * (A : ℝ))) := by ring)
  simpa [μ, Bad, Low, weight] using hpartition

theorem
    lemma79CanonicalEndpointFreshPMF_outer754Weight_summable_and_le_priorityPartition_one
    {n A m P T : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m)
    (hthreshold :
      (10 : ℝ) * (A : ℝ) ≤ epsilon ^ 3 * ((T + 1 : ℕ) : ℝ))
    (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    let μ := lemma79CanonicalEndpointFreshPMF (n / 2) entry gap
    let Bad := lemma79CanonicalEndpointFreshOuterBadJEvent P m
    let Low :=
      lemma79CanonicalEndpointFreshLowWhiteEvent
        n P T xi epsilon entry
    let weight :=
      lemma79EndpointFreshOuter754Weight
        n A m P xi epsilon entry
    Summable (fun atom => (μ atom).toReal * weight atom) ∧
      taoSection7PMFExpectation μ weight ≤
        (m : ℝ) ^ A * (μ.toOuterMeasure Bad).toReal +
          (10 : ℝ) ^ A * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
            (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) := by
  dsimp only
  let μ := lemma79CanonicalEndpointFreshPMF (n / 2) entry gap
  let Bad := lemma79CanonicalEndpointFreshOuterBadJEvent P m
  let Low :=
    lemma79CanonicalEndpointFreshLowWhiteEvent n P T xi epsilon entry
  let weight :=
    lemma79EndpointFreshOuter754Weight n A m P xi epsilon entry
  have hexact :=
    lemma79CanonicalEndpointFreshPMF_outer754Weight_summable_and_le_priorityPartition
      (n := n) (A := A) (m := m) (P := P) (T := T)
      (xi := xi) (epsilon := epsilon)
      hepsilon hm hthreshold entry gap
  have hmass :
      (μ.toOuterMeasure ((Bad ∪ Low)ᶜ)).toReal ≤ 1 :=
    taoSection7PMFEventMass_le_one μ _
  have hcoefficient :
      0 ≤ (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) := by
    positivity
  refine ⟨by simpa [μ, weight] using hexact.1, ?_⟩
  calc
    taoSection7PMFExpectation μ weight ≤
        (m : ℝ) ^ A * (μ.toOuterMeasure Bad).toReal +
          (10 : ℝ) ^ A * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
            ((10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ)))) *
              (μ.toOuterMeasure ((Bad ∪ Low)ᶜ)).toReal := by
      simpa [μ, Bad, Low, weight] using hexact.2
    _ ≤ (m : ℝ) ^ A * (μ.toOuterMeasure Bad).toReal +
          (10 : ℝ) ^ A * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
            (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) := by
      calc
        (m : ℝ) ^ A * (μ.toOuterMeasure Bad).toReal +
              (10 : ℝ) ^ A * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
                ((10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ)))) *
                  (μ.toOuterMeasure ((Bad ∪ Low)ᶜ)).toReal ≤
            (m : ℝ) ^ A * (μ.toOuterMeasure Bad).toReal +
              (10 : ℝ) ^ A * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
                ((10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ)))) * 1 :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hmass hcoefficient)
        _ = (m : ℝ) ^ A * (μ.toOuterMeasure Bad).toReal +
              (10 : ℝ) ^ A * (μ.toOuterMeasure (Badᶜ ∩ Low)).toReal +
                (10 : ℝ) ^ A * Real.exp (-((10 : ℝ) * (A : ℝ))) := by
          ring

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
