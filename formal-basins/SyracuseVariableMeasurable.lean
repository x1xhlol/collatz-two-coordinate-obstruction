import PadicSyracuseVariable
import GeometricSequenceLaw
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace CollatzCylinderPacking.Arithmetic

instance geometricWordCountable (k : ℕ) : Countable (GeometricWord k) := by
  induction k with
  | zero => change Countable Unit; infer_instance
  | succ k ih =>
    letI := ih
    change Countable (ℕ × GeometricWord k)
    infer_instance

instance geometricWordMeasurableSpace (k : ℕ) : MeasurableSpace (GeometricWord k) := ⊤

instance geometricWordMeasurableSingleton (k : ℕ) : MeasurableSingletonClass (GeometricWord k) := by
  constructor
  intro _
  trivial

theorem sequenceWord_event_measurable (k : ℕ) (w : GeometricWord k) :
    MeasurableSet {f : ℕ → ℕ | sequenceWord k f = w} := by
  rw [sequenceWord_event]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => measurableSet_singleton _)

theorem sequenceWord_measurable (k : ℕ) : Measurable (sequenceWord k) := by
  intro s _
  rw [← Set.biUnion_preimage_singleton]
  exact MeasurableSet.biUnion (Set.to_countable s) (fun w _ => sequenceWord_event_measurable k w)

theorem integerResidue_measurable (k : ℕ) : Measurable (integerResidue k) :=
  (measurable_of_countable (fun w : GeometricWord k => ((wordResidue k w).val : ℤ))).comp
    (sequenceWord_measurable k)

instance padicThreeMeasurableSpace : MeasurableSpace ℤ_[3] := borel ℤ_[3]
instance padicThreeBorelSpace : BorelSpace ℤ_[3] := ⟨rfl⟩

theorem kernel_three (k : ℕ) :
    RingHom.ker (PadicInt.toZModPow k : ℤ_[3] →+* ZMod (3 ^ k)) =
      Ideal.span {(3 : ℤ_[3]) ^ k} := by
  simpa only [Nat.cast_ofNat] using (PadicInt.ker_toZModPow (p := 3) k)

theorem norm_span_three (x : ℤ_[3]) (k : ℕ) :
    ‖x‖ ≤ (3 : ℝ) ^ (-k : ℤ) ↔ x ∈ (Ideal.span {(3 : ℤ_[3]) ^ k} : Ideal ℤ_[3]) := by
  simpa only [Nat.cast_ofNat] using (PadicInt.norm_le_pow_iff_mem_span_pow (p := 3) x k)

theorem canonical_approximation_bound (k : ℕ) (f : ℕ → ℕ) :
    dist (integerResidue k f : ℤ_[3]) (canonicalSyracuseVariable f) ≤ (1 / 3 : ℝ) ^ k := by
  have hi : canonicalSyracuseVariable f - (integerResidue k f : ℤ_[3]) ∈
      (Ideal.span {(3 : ℤ_[3]) ^ k} : Ideal ℤ_[3]) := by
    rw [← kernel_three k, RingHom.mem_ker, map_sub,
      canonical_variable_projection, map_intCast]
    simp [integerResidue]
  have hn := (norm_span_three _ k).mpr hi
  rw [dist_eq_norm, norm_sub_rev]
  convert hn using 1
  simp [zpow_neg, zpow_natCast, one_div, inv_pow]

theorem canonical_approximation_tendsto (f : ℕ → ℕ) :
    Tendsto (fun k => (integerResidue k f : ℤ_[3])) atTop (𝓝 (canonicalSyracuseVariable f)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => canonical_approximation_bound k f)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem canonical_variable_measurable : Measurable canonicalSyracuseVariable := by
  apply measurable_of_tendsto_metrizable
    (fun k => (measurable_of_countable (fun z : ℤ => (z : ℤ_[3]))).comp
      (integerResidue_measurable k))
  exact tendsto_pi_nhds.mpr canonical_approximation_tendsto

theorem padic_cylinder_measurable (k : ℕ) (v : ZMod (3 ^ k)) :
    MeasurableSet {x : ℤ_[3] | PadicInt.toZModPow k x = v} := by
  have hs : MeasurableSet {x : ℤ_[3] | ‖x - (v.val : ℤ_[3])‖ ≤ (3 : ℝ) ^ (-k : ℤ)} :=
    (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).measurableSet
  convert hs using 1
  ext x
  simp only [Set.mem_setOf_eq]
  rw [norm_span_three, ← kernel_three k,
    RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]

#print axioms canonical_approximation_bound
#print axioms canonical_variable_measurable
#print axioms padic_cylinder_measurable

end CollatzCylinderPacking.Arithmetic
