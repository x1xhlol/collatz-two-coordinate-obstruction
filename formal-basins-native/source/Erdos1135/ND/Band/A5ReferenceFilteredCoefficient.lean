import Erdos1135.ND.Band.A5ReferencePhysicalSplit
import Erdos1135.Tao.Section5.EndpointCoefficientBound

/-!
# A5 predicate-filtered endpoint coefficients

This leaf retains a predicate on the original natural endpoint while the
payload-free coefficient is partitioned by valuation tuple.  Each retained
subfiber is enlarged only to its checked full same-tuple Tao fiber; the outer
carrier still records an actual predicate witness.  This is the finite
algebraic socket needed before the exterior centered-tail argument.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- A Tao endpoint valuation/residue fiber restricted by a predicate on the
original natural endpoint. -/
def ndA5EndpointValuationFiberFilter
    (B : ℕ) (E : Set ℕ) (q : ℕ) (X : ZMod (3 ^ q))
    (P : ℕ → Prop) [DecidablePred P] (bs : List ℕ+) :
    Finset (Tao.TaoSection5Endpoint B E) :=
  (Tao.taoSection5EndpointValuationFiber B E q X bs).filter
    (fun M => P M.1)

/-- Valuation tuples whose fixed residue fiber contains a retained original
endpoint. -/
def ndA5EndpointValuationFilterCarrier
    (B : ℕ) (E : Set ℕ) (q : ℕ) (X : ZMod (3 ^ q))
    (P : ℕ → Prop) [DecidablePred P] : Finset (List ℕ+) :=
  (Tao.taoSection5EndpointValuationCarrier B E).filter
    (fun bs =>
      (ndA5EndpointValuationFiberFilter B E q X P bs).Nonempty)

@[simp] theorem mem_ndA5EndpointValuationFiberFilter_iff
    {B q : ℕ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {P : ℕ → Prop} [DecidablePred P] {bs : List ℕ+}
    {M : Tao.TaoSection5Endpoint B E} :
    M ∈ ndA5EndpointValuationFiberFilter B E q X P bs ↔
      M ∈ Tao.taoSection5EndpointValuationFiber B E q X bs ∧ P M.1 := by
  simp [ndA5EndpointValuationFiberFilter]

@[simp] theorem mem_ndA5EndpointValuationFilterCarrier_iff
    {B q : ℕ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {P : ℕ → Prop} [DecidablePred P] {bs : List ℕ+} :
    bs ∈ ndA5EndpointValuationFilterCarrier B E q X P ↔
      bs ∈ Tao.taoSection5EndpointValuationCarrier B E ∧
        (ndA5EndpointValuationFiberFilter B E q X P bs).Nonempty := by
  simp [ndA5EndpointValuationFilterCarrier]

theorem ndA5EndpointValuationFilterCarrier_subset
    {B q : ℕ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {P : ℕ → Prop} [DecidablePred P] :
    ndA5EndpointValuationFilterCarrier B E q X P ⊆
      Tao.taoSection5EndpointValuationCarrier B E :=
  Finset.filter_subset _ _

theorem ndA5EndpointValuationFilterCarrier_length
    {B q : ℕ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {P : ℕ → Prop} [DecidablePred P] {bs : List ℕ+}
    (hbs : bs ∈ ndA5EndpointValuationFilterCarrier B E q X P) :
    bs.length = Tao.taoSection5M0 B := by
  exact Tao.length_eq_m0_of_mem_taoSection5EndpointValuationCarrier
    (ndA5EndpointValuationFilterCarrier_subset hbs)

/-- Every retained tuple carries an actual original-endpoint witness. -/
theorem exists_endpoint_of_mem_ndA5EndpointValuationFilterCarrier
    {B q : ℕ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {P : ℕ → Prop} [DecidablePred P] {bs : List ℕ+}
    (hbs : bs ∈ ndA5EndpointValuationFilterCarrier B E q X P) :
    ∃ M : Tao.TaoSection5Endpoint B E,
      M ∈ Tao.taoSection5EndpointValuationFiber B E q X bs ∧ P M.1 := by
  rcases (mem_ndA5EndpointValuationFilterCarrier_iff.mp hbs).2 with
    ⟨M, hM⟩
  exact ⟨M, mem_ndA5EndpointValuationFiberFilter_iff.mp hM⟩

/-- Exact predicate-aware partition of residue-restricted attached endpoints.
The nonempty filtered carrier removes only zero inner sums. -/
theorem sum_ndA5EndpointValuationFiberFilter
    {R : Type*} [AddCommMonoid R]
    {B : ℕ} {E : Set ℕ} (q : ℕ) (X : ZMod (3 ^ q))
    (P : ℕ → Prop) [DecidablePred P]
    (f : Tao.TaoSection5Endpoint B E → R) :
    (∑ M : Tao.TaoSection5Endpoint B E
        with (M.1 : ZMod (3 ^ q)) = X ∧ P M.1, f M) =
      ∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
        ∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs, f M := by
  classical
  let S : Finset (Tao.TaoSection5Endpoint B E) :=
    Finset.univ.filter fun M =>
      (M.1 : ZMod (3 ^ q)) = X ∧ P M.1
  let T : Finset (List ℕ+) :=
    ndA5EndpointValuationFilterCarrier B E q X P
  let g : Tao.TaoSection5Endpoint B E → List ℕ+ :=
    Tao.taoSection5EndpointValuation
  have hmaps : ∀ M ∈ S, g M ∈ T := by
    intro M hM
    have hpred := (Finset.mem_filter.mp hM).2
    rw [show T = ndA5EndpointValuationFilterCarrier B E q X P by rfl,
      mem_ndA5EndpointValuationFilterCarrier_iff]
    constructor
    · exact Finset.mem_image.mpr ⟨M, by simp, rfl⟩
    · refine ⟨M, mem_ndA5EndpointValuationFiberFilter_iff.mpr ⟨?_, hpred.2⟩⟩
      rw [Tao.mem_taoSection5EndpointValuationFiber_iff]
      exact ⟨rfl, hpred.1⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps f
  symm
  calc
    (∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
        ∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs, f M) =
        ∑ bs ∈ T, ∑ M ∈ S with g M = bs, f M := by
      apply Finset.sum_congr rfl
      intro bs _hbs
      apply Finset.sum_congr
      · ext M
        simp [S, g, ndA5EndpointValuationFiberFilter,
          Tao.taoSection5EndpointValuationFiber, and_comm, and_assoc]
      · intro M _hM
        rfl
    _ = ∑ M ∈ S, f M := hfiber
    _ = ∑ M : Tao.TaoSection5Endpoint B E
        with (M.1 : ZMod (3 ^ q)) = X ∧ P M.1, f M := by
      rfl

/-- The coefficient of a predicate-filtered endpoint set is exactly the sum
over its nonempty filtered valuation fibers. -/
theorem ndA5PayloadFreeCoefficient_filter_eq_sum_endpointValuationFiberFilter
    (B : ℕ) (E : Set ℕ) (q : ℕ) (X : ZMod (3 ^ q))
    (P : ℕ → Prop) [DecidablePred P] :
    Tao.taoSection5PayloadFreeCoefficient q
        ((Tao.taoSection5EPrime B E).filter P) X =
      ((3 ^ q : ℕ) : ℝ) *
        ∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
          ∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs,
            1 / (M.1 : ℝ) := by
  classical
  unfold Tao.taoSection5PayloadFreeCoefficient
  calc
    ((3 ^ q : ℕ) : ℝ) *
        ((((Tao.taoSection5EPrime B E).filter P).filter
          (fun M : ℕ => (M : ZMod (3 ^ q)) = X)).sum
            (fun M => 1 / (M : ℝ))) =
      ((3 ^ q : ℕ) : ℝ) *
        ∑ M : Tao.TaoSection5Endpoint B E
          with (M.1 : ZMod (3 ^ q)) = X ∧ P M.1,
            1 / (M.1 : ℝ) := by
      congr 1
      apply Finset.sum_bij
        (fun M hM =>
          (⟨M,
            (Finset.mem_filter.mp
              (Finset.mem_filter.mp hM).1).1⟩ :
            Tao.TaoSection5Endpoint B E))
      · intro M hM
        rcases Finset.mem_filter.mp hM with ⟨hMP, hresidue⟩
        rcases Finset.mem_filter.mp hMP with ⟨_hME, hP⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨hresidue, hP⟩⟩
      · intro M₁ _hM₁ M₂ _hM₂ hEq
        exact congrArg Subtype.val hEq
      · intro M hM
        rcases (Finset.mem_filter.mp hM).2 with ⟨hresidue, hP⟩
        refine ⟨M.1, ?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨M.2, hP⟩, hresidue⟩
        · apply Subtype.ext
          rfl
      · intro M _hM
        rfl
    _ = ((3 ^ q : ℕ) : ℝ) *
        ∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
          ∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs,
            1 / (M.1 : ℝ) := by
      rw [sum_ndA5EndpointValuationFiberFilter]

/-- A filtered same-tuple reciprocal sum is bounded by the inherited full
fiber native envelope. -/
theorem ndA5_endpointFiberFilter_scaled_reciprocal_le_nativeEnvelope
    {B : ℕ} {E : Set ℕ} (facts : Tao.TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {P : ℕ → Prop} [DecidablePred P]
    {bs : List ℕ+}
    (hindex : Tao.taoSection5M0 B + q ≤ Tao.taoSection5N0 B) :
    (3 : ℝ) ^ q *
        (∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs,
          1 / (M.1 : ℝ)) ≤
      Tao.geom2PNatListNativeBase bs +
        Tao.taoSection5EndpointFiberHighEnvelope B q bs := by
  have hsubset :
      ndA5EndpointValuationFiberFilter B E q X P bs ⊆
        Tao.taoSection5EndpointValuationFiber B E q X bs :=
    Finset.filter_subset _ _
  have hsum :
      (∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs,
          1 / (M.1 : ℝ)) ≤
        ∑ M ∈ Tao.taoSection5EndpointValuationFiber B E q X bs,
          1 / (M.1 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro M _hM _hnot
      positivity)
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
    (Tao.taoSection5_endpointFiber_scaled_reciprocal_le_nativeEnvelope
      facts hindex)

/-- Predicate-filtered coefficient aggregation before the native-base and
high-envelope carrier sums are treated separately. -/
theorem ndA5PayloadFreeCoefficient_filter_le_sum_nativeEnvelope
    {B : ℕ} {E : Set ℕ} (facts : Tao.TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} (P : ℕ → Prop) [DecidablePred P]
    (hindex : Tao.taoSection5M0 B + q ≤ Tao.taoSection5N0 B) :
    Tao.taoSection5PayloadFreeCoefficient q
        ((Tao.taoSection5EPrime B E).filter P) X ≤
      ∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
        (Tao.geom2PNatListNativeBase bs +
          Tao.taoSection5EndpointFiberHighEnvelope B q bs) := by
  classical
  calc
    Tao.taoSection5PayloadFreeCoefficient q
        ((Tao.taoSection5EPrime B E).filter P) X =
      ((3 ^ q : ℕ) : ℝ) *
        ∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
          ∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs,
            1 / (M.1 : ℝ) :=
      ndA5PayloadFreeCoefficient_filter_eq_sum_endpointValuationFiberFilter
        B E q X P
    _ = (3 : ℝ) ^ q *
        ∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
          ∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs,
            1 / (M.1 : ℝ) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    _ = ∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
        (3 : ℝ) ^ q *
          (∑ M ∈ ndA5EndpointValuationFiberFilter B E q X P bs,
            1 / (M.1 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
        (Tao.geom2PNatListNativeBase bs +
          Tao.taoSection5EndpointFiberHighEnvelope B q bs) := by
      apply Finset.sum_le_sum
      intro bs _hbs
      exact ndA5_endpointFiberFilter_scaled_reciprocal_le_nativeEnvelope
        facts hindex

theorem ndA5EndpointFiberHighEnvelope_nonneg
    (B q : ℕ) (bs : List ℕ+) :
    0 ≤ Tao.taoSection5EndpointFiberHighEnvelope B q bs := by
  unfold Tao.taoSection5EndpointFiberHighEnvelope
  by_cases hhigh : bs ∈ Tao.taoGeom2HighWeightEvent B
  · simp only [if_pos hhigh]
    positivity
  · simp only [if_neg hhigh]
    exact le_rfl

/-- The high-envelope contribution keeps its scheduled negative power of
`B`; unlike the inherited coarse `≤ 3` endpoint, this is usable in exterior H. -/
theorem sum_ndA5EndpointValuationFilterCarrier_highEnvelope_le_three_mul_rpow
    {B : ℕ} {E : Set ℕ} (facts : Tao.TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {P : ℕ → Prop} [DecidablePred P]
    (hindex : Tao.taoSection5M0 B + q ≤ Tao.taoSection5N0 B) :
    (∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
      Tao.taoSection5EndpointFiberHighEnvelope B q bs) ≤
      3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) := by
  classical
  let C : Finset (List ℕ+) :=
    ndA5EndpointValuationFilterCarrier B E q X P
  let p : List ℕ+ → ℝ := fun bs =>
    (Tao.taoGeom2HighWeightEvent B).indicator
      (fun cs =>
        (Tao.geom2PNatListPMF (Tao.taoSection5M0 B) cs).toReal) bs
  let K : ℝ := 3 * (3 : ℝ) ^ (Tao.taoSection5M0 B + q)
  have hpoint : ∀ bs ∈ C,
      Tao.taoSection5EndpointFiberHighEnvelope B q bs = K * p bs := by
    intro bs hbs
    have hlength := ndA5EndpointValuationFilterCarrier_length
      (by simpa only [C] using hbs)
    have hmass := Tao.geom2PNatListPMF_apply_length_toReal bs
    rw [hlength] at hmass
    unfold Tao.taoSection5EndpointFiberHighEnvelope p K
    by_cases hhigh : bs ∈ Tao.taoGeom2HighWeightEvent B
    · rw [if_pos hhigh, Set.indicator_of_mem hhigh, hmass,
        Tao.geom2PNatListMass_eq_inv_pow]
      ring
    · rw [if_neg hhigh, Set.indicator_of_notMem hhigh, mul_zero]
  have hsubset : C ⊆ Tao.taoSection5EndpointValuationCarrier B E := by
    intro bs hbs
    exact ndA5EndpointValuationFilterCarrier_subset
      (by simpa only [C] using hbs)
  have hcarrier :
      (∑ bs ∈ C, p bs) ≤
        ∑ bs ∈ Tao.taoSection5EndpointValuationCarrier B E, p bs :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro bs _hbs _hnot
      dsimp only [p]
      by_cases hhigh : bs ∈ Tao.taoGeom2HighWeightEvent B
      · simp only [Set.indicator_of_mem hhigh]
        exact ENNReal.toReal_nonneg
      · simp only [Set.indicator_of_notMem hhigh]
        exact le_rfl)
  have hatom := Tao.sum_endpointValuationCarrier_highAtom_le_eventMass B E
  have hevent :
      (∑ bs ∈ C, p bs) ≤
        ((Tao.geom2PNatListPMF (Tao.taoSection5M0 B)).toOuterMeasure
          (Tao.taoGeom2HighWeightEvent B)).toReal :=
    hcarrier.trans (by simpa only [p] using hatom)
  have hpreterminal :
      2 * 3 ^ (Tao.taoSection5M0 B - 1) ≤ B := by
    exact_mod_cast facts.preterminal_offset_room
  have hpowPos : 0 < 3 ^ (Tao.taoSection5M0 B - 1) := by positivity
  have hB : 1 < B := by omega
  have hscalar :=
    (Tao.taoSection5_three_pow_mul_geom2HighWeight_le_rpow hB hindex).1
  calc
    (∑ bs ∈ ndA5EndpointValuationFilterCarrier B E q X P,
        Tao.taoSection5EndpointFiberHighEnvelope B q bs) =
        ∑ bs ∈ C, K * p bs := by
      apply Finset.sum_congr rfl
      exact hpoint
    _ = K * ∑ bs ∈ C, p bs := by rw [Finset.mul_sum]
    _ ≤ K *
        ((Tao.geom2PNatListPMF (Tao.taoSection5M0 B)).toOuterMeasure
          (Tao.taoGeom2HighWeightEvent B)).toReal := by
      exact mul_le_mul_of_nonneg_left hevent (by positivity)
    _ = 3 * ((3 : ℝ) ^ (Tao.taoSection5M0 B + q) *
        ((Tao.geom2PNatListPMF (Tao.taoSection5M0 B)).toOuterMeasure
          (Tao.taoGeom2HighWeightEvent B)).toReal) := by
      dsimp only [K]
      ring
    _ ≤ 3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar (by norm_num)

/-- Exterior specialization of the filtered valuation carrier. -/
def ndA5ReferenceExteriorEndpointValuationCarrier
    (B : ℕ) (C : ℝ) (E : Set ℕ) (q : ℕ) (X : ZMod (3 ^ q)) :
    Finset (List ℕ+) := by
  classical
  exact ndA5EndpointValuationFilterCarrier B E q X
    (ndA5ReferenceEndpointExteriorAt B C)

/-- An exterior carrier tuple retains a strict original-endpoint witness in
its full Tao valuation/residue fiber. -/
theorem exists_exterior_endpoint_of_mem_referenceExteriorCarrier
    {B q : ℕ} {C : ℝ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+}
    (hbs : bs ∈
      ndA5ReferenceExteriorEndpointValuationCarrier B C E q X) :
    ∃ M : Tao.TaoSection5Endpoint B E,
      M ∈ Tao.taoSection5EndpointValuationFiber B E q X bs ∧
        ndA5ReferenceEndpointExteriorAt B C M.1 := by
  classical
  exact exists_endpoint_of_mem_ndA5EndpointValuationFilterCarrier
    (by simpa only [ndA5ReferenceExteriorEndpointValuationCarrier] using hbs)

set_option maxHeartbeats 400000 in
/-- Route-facing exterior coefficient bound.  The native-base sum is still
over tuples carrying an actual strict exterior endpoint, and the high
remainder retains its scheduled decay. -/
theorem ndA5ReferenceExteriorCoefficient_le_nativeBase_add_three_mul_rpow
    {B : ℕ} {C : ℝ} {E : Set ℕ}
    (facts : Tao.TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)}
    (hindex : Tao.taoSection5M0 B + q ≤ Tao.taoSection5N0 B) :
    Tao.taoSection5PayloadFreeCoefficient q
        (ndA5ReferenceExteriorEndpoints B C E) X ≤
      (∑ bs ∈ ndA5ReferenceExteriorEndpointValuationCarrier B C E q X,
        Tao.geom2PNatListNativeBase bs) +
        3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) := by
  classical
  have hnative :
      Tao.taoSection5PayloadFreeCoefficient q
          (ndA5ReferenceExteriorEndpoints B C E) X ≤
        ∑ bs ∈
            ndA5ReferenceExteriorEndpointValuationCarrier B C E q X,
          (Tao.geom2PNatListNativeBase bs +
            Tao.taoSection5EndpointFiberHighEnvelope B q bs) := by
    simpa only [ndA5ReferenceExteriorEndpoints,
      ndA5ReferenceExteriorEndpointValuationCarrier] using
      (ndA5PayloadFreeCoefficient_filter_le_sum_nativeEnvelope
        facts (ndA5ReferenceEndpointExteriorAt B C) hindex
          (X := X) (E := E))
  have hhigh :
      (∑ bs ∈ ndA5ReferenceExteriorEndpointValuationCarrier B C E q X,
        Tao.taoSection5EndpointFiberHighEnvelope B q bs) ≤
          3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) := by
    simpa only [ndA5ReferenceExteriorEndpointValuationCarrier] using
      (sum_ndA5EndpointValuationFilterCarrier_highEnvelope_le_three_mul_rpow
        facts (E := E) (P := ndA5ReferenceEndpointExteriorAt B C)
          (X := X) hindex)
  calc
    Tao.taoSection5PayloadFreeCoefficient q
        (ndA5ReferenceExteriorEndpoints B C E) X ≤
      ∑ bs ∈ ndA5ReferenceExteriorEndpointValuationCarrier B C E q X,
        (Tao.geom2PNatListNativeBase bs +
          Tao.taoSection5EndpointFiberHighEnvelope B q bs) := hnative
    _ = (∑ bs ∈ ndA5ReferenceExteriorEndpointValuationCarrier B C E q X,
          Tao.geom2PNatListNativeBase bs) +
        ∑ bs ∈ ndA5ReferenceExteriorEndpointValuationCarrier B C E q X,
          Tao.taoSection5EndpointFiberHighEnvelope B q bs := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ bs ∈ ndA5ReferenceExteriorEndpointValuationCarrier B C E q X,
          Tao.geom2PNatListNativeBase bs) +
        3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) :=
      add_le_add le_rfl hhigh

end
end ND
end Erdos1135
