/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.EndpointFiberEnvelope
import Erdos1135SecondScale.Tao.Section5.Geom2HighWeightScalar

/-!
# Section 5 Endpoint Coefficient Bound

This leaf aggregates the native fixed-fiber envelope over the deduplicated
endpoint valuation carrier.  It enlarges base terms to the exact-length list
subtype and high terms to the ambient PMF event, proving the branch-free
coefficient bound `0 ≤ c ≤ 5`.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

private theorem geom2PNatListNativeBase_nonneg (bs : List ℕ+) :
    0 ≤ geom2PNatListNativeBase bs := by
  unfold geom2PNatListNativeBase
  positivity

/-- Direct duplicate-free enlargement of the endpoint valuation carrier to
all exact-length valuation lists. -/
theorem sum_endpointValuationCarrier_nativeBase_le_two
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B) :
    (∑ bs ∈ taoSection5EndpointValuationCarrier B E,
      geom2PNatListNativeBase bs) ≤ 2 := by
  classical
  let C : Finset (List ℕ+) := taoSection5EndpointValuationCarrier B E
  let ExactM := {bs : List ℕ+ // bs.length = taoSection5M0 B}
  let e : {bs : List ℕ+ // bs ∈ C} ↪ ExactM :=
    { toFun := fun bs =>
        ⟨bs.1, length_eq_m0_of_mem_taoSection5EndpointValuationCarrier bs.2⟩
      inj' := by
        intro bs cs h
        apply Subtype.ext
        exact congrArg (fun x : ExactM => x.1) h }
  let T : Finset ExactM := C.attach.map e
  have hsum :
      (∑ bs ∈ C, geom2PNatListNativeBase bs) =
        ∑ bs ∈ T, geom2PNatListNativeBase bs.1 := by
    calc
      (∑ bs ∈ C, geom2PNatListNativeBase bs) =
          ∑ bs ∈ C.attach, geom2PNatListNativeBase bs.1 :=
        (Finset.sum_attach C geom2PNatListNativeBase).symm
      _ = ∑ bs ∈ T, geom2PNatListNativeBase bs.1 := by
        simpa [T, e] using
          (Finset.sum_map C.attach e
            (fun bs : ExactM => geom2PNatListNativeBase bs.1)).symm
  change (∑ bs ∈ C, geom2PNatListNativeBase bs) ≤ 2
  rw [hsum]
  calc
    (∑ bs ∈ T, geom2PNatListNativeBase bs.1) ≤
        ∑' bs : ExactM, geom2PNatListNativeBase bs.1 :=
      (summable_geom2PNatListNativeBase_exactLength
        (taoSection5M0 B)).sum_le_tsum T
          (fun bs _hbs => geom2PNatListNativeBase_nonneg bs.1)
    _ = 2 := by
      rw [tsum_geom2PNatListNativeBase_exactLength,
        if_neg (Nat.ne_of_gt facts.one_le_m0)]

/-- Finite endpoint-carrier atoms in the strict high event are bounded by the
ambient exact-length PMF event mass. -/
theorem sum_endpointValuationCarrier_highAtom_le_eventMass
    (B : ℕ) (E : Set ℕ) :
    (∑ bs ∈ taoSection5EndpointValuationCarrier B E,
      (taoGeom2HighWeightEvent B).indicator
        (fun bs => (geom2PNatListPMF (taoSection5M0 B) bs).toReal) bs) ≤
      ((geom2PNatListPMF (taoSection5M0 B)).toOuterMeasure
        (taoGeom2HighWeightEvent B)).toReal := by
  classical
  let f : List ℕ+ → ℝ := fun bs =>
    (taoGeom2HighWeightEvent B).indicator
      (fun cs => (geom2PNatListPMF (taoSection5M0 B) cs).toReal) bs
  have hf : Summable f :=
    (taoPMF_summable_toReal
      (geom2PNatListPMF (taoSection5M0 B))).indicator
        (taoGeom2HighWeightEvent B)
  change (∑ bs ∈ taoSection5EndpointValuationCarrier B E, f bs) ≤ _
  calc
    (∑ bs ∈ taoSection5EndpointValuationCarrier B E, f bs) ≤
        ∑' bs : List ℕ+, f bs :=
      hf.sum_le_tsum (taoSection5EndpointValuationCarrier B E)
        (fun bs _hbs => by
          unfold f
          by_cases hhigh : bs ∈ taoGeom2HighWeightEvent B
          · simp only [Set.indicator_of_mem hhigh]
            exact ENNReal.toReal_nonneg
          · simp only [Set.indicator_of_notMem hhigh]
            exact le_rfl)
    _ = ((geom2PNatListPMF (taoSection5M0 B)).toOuterMeasure
          (taoGeom2HighWeightEvent B)).toReal := by
      rw [pmfOuterMass_toReal_eq_tsum_indicator]

/-- Lost-window facts and the `m0+q` index guard give the high-event scalar
without a source branch or passage time. -/
theorem taoSection5_three_pow_m0_add_q_mul_geom2HighWeight_le_one
    {B q : ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    (3 : ℝ) ^ (taoSection5M0 B + q) *
        ((geom2PNatListPMF (taoSection5M0 B)).toOuterMeasure
          (taoGeom2HighWeightEvent B)).toReal ≤ 1 := by
  have hpreterminal : 2 * 3 ^ (taoSection5M0 B - 1) ≤ B := by
    exact_mod_cast facts.preterminal_offset_room
  have hpowPos : 0 < 3 ^ (taoSection5M0 B - 1) := by positivity
  have hB : 1 < B := by omega
  have hscalar := taoSection5_three_pow_mul_geom2HighWeight_le_rpow
    hB hindex
  exact hscalar.1.trans hscalar.2

/-- The finite high-envelope carrier sum is at most three. -/
theorem sum_endpointValuationCarrier_highEnvelope_le_three
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    (∑ bs ∈ taoSection5EndpointValuationCarrier B E,
      taoSection5EndpointFiberHighEnvelope B q bs) ≤ 3 := by
  classical
  let C : Finset (List ℕ+) := taoSection5EndpointValuationCarrier B E
  let p : List ℕ+ → ℝ := fun bs =>
    (taoGeom2HighWeightEvent B).indicator
      (fun cs => (geom2PNatListPMF (taoSection5M0 B) cs).toReal) bs
  let K : ℝ := 3 * (3 : ℝ) ^ (taoSection5M0 B + q)
  have hpoint : ∀ bs ∈ C,
      taoSection5EndpointFiberHighEnvelope B q bs = K * p bs := by
    intro bs hbs
    have hlength :=
      length_eq_m0_of_mem_taoSection5EndpointValuationCarrier hbs
    have hmass := geom2PNatListPMF_apply_length_toReal bs
    rw [hlength] at hmass
    unfold taoSection5EndpointFiberHighEnvelope p K
    by_cases hhigh : bs ∈ taoGeom2HighWeightEvent B
    · rw [if_pos hhigh, Set.indicator_of_mem hhigh, hmass,
        geom2PNatListMass_eq_inv_pow]
      ring
    · rw [if_neg hhigh, Set.indicator_of_notMem hhigh, mul_zero]
  have hatom := sum_endpointValuationCarrier_highAtom_le_eventMass B E
  have hscalar :=
    taoSection5_three_pow_m0_add_q_mul_geom2HighWeight_le_one facts hindex
  calc
    (∑ bs ∈ taoSection5EndpointValuationCarrier B E,
        taoSection5EndpointFiberHighEnvelope B q bs) =
        ∑ bs ∈ C, K * p bs := by
      apply Finset.sum_congr rfl
      exact hpoint
    _ = K * ∑ bs ∈ C, p bs := by rw [Finset.mul_sum]
    _ ≤ K *
        ((geom2PNatListPMF (taoSection5M0 B)).toOuterMeasure
          (taoGeom2HighWeightEvent B)).toReal := by
      exact mul_le_mul_of_nonneg_left hatom (by positivity)
    _ = 3 *
        ((3 : ℝ) ^ (taoSection5M0 B + q) *
          ((geom2PNatListPMF (taoSection5M0 B)).toOuterMeasure
            (taoGeom2HighWeightEvent B)).toReal) := by
      dsimp [K]
      ring
    _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left hscalar (by norm_num)
    _ = 3 := by norm_num

/-- Pointwise fixed-fiber aggregation before the two carrier enlargements. -/
theorem taoSection5PayloadFreeCoefficient_le_sum_nativeEnvelope
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)}
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X ≤
      ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
        (geom2PNatListNativeBase bs +
          taoSection5EndpointFiberHighEnvelope B q bs) := by
  classical
  calc
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X =
        ((3 ^ q : ℕ) : ℝ) *
          ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
            ∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
              1 / (M.1 : ℝ) :=
      taoSection5PayloadFreeCoefficient_eq_sum_endpointValuationFiber B E q X
    _ = (3 : ℝ) ^ q *
          ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
            ∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
              1 / (M.1 : ℝ) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    _ = ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
          (3 : ℝ) ^ q *
            (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
              1 / (M.1 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
          (geom2PNatListNativeBase bs +
            taoSection5EndpointFiberHighEnvelope B q bs) := by
      apply Finset.sum_le_sum
      intro bs _hbs
      exact taoSection5_endpointFiber_scaled_reciprocal_le_nativeEnvelope
        (E := E) (q := q) (X := X) (bs := bs) facts hindex

theorem taoSection5PayloadFreeCoefficient_nonneg
    (q : ℕ) (S : Finset ℕ) (X : ZMod (3 ^ q)) :
    0 ≤ taoSection5PayloadFreeCoefficient q S X := by
  unfold taoSection5PayloadFreeCoefficient
  positivity

/-- Branch-free endpoint coefficient bound with the native constant five. -/
theorem taoSection5PayloadFreeCoefficient_ePrime_mem_Icc_five
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)}
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X ∈
      Set.Icc (0 : ℝ) 5 := by
  constructor
  · exact taoSection5PayloadFreeCoefficient_nonneg q _ X
  · have hpoint := taoSection5PayloadFreeCoefficient_le_sum_nativeEnvelope
      facts (E := E) (q := q) (X := X) hindex
    have hbase := sum_endpointValuationCarrier_nativeBase_le_two
      (E := E) facts
    have hhigh := sum_endpointValuationCarrier_highEnvelope_le_three
      (E := E) facts hindex
    calc
      taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X ≤
          ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
            (geom2PNatListNativeBase bs +
              taoSection5EndpointFiberHighEnvelope B q bs) := hpoint
      _ = (∑ bs ∈ taoSection5EndpointValuationCarrier B E,
            geom2PNatListNativeBase bs) +
          ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
            taoSection5EndpointFiberHighEnvelope B q bs := by
        rw [Finset.sum_add_distrib]
      _ ≤ 2 + 3 := add_le_add hbase hhigh
      _ = 5 := by norm_num

end

end Tao
end Erdos1135SecondScale
