import PadicHaarLift
import CanonicalIntegerEnvelope
import CanonicalSyracuseUnique
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

noncomputable def padicOddLiftENN (f : ℤ_[3] → ℝ≥0∞) : ℤ_[3] → ℝ≥0∞ :=
  Function.extend (padicAffineBranch 1) f (fun _ => 0)

theorem padicOddLiftENN_apply_branch (f : ℤ_[3] → ℝ≥0∞) (x : ℤ_[3]) :
    padicOddLiftENN f (padicAffineBranch 1 x) = f x :=
  (padicAffineBranch_injective 1).extend_apply f (fun _ => 0) x

theorem padicOddLiftENN_eq_zero (f : ℤ_[3] → ℝ≥0∞) {x : ℤ_[3]}
    (hx : x ∉ Set.range (padicAffineBranch 1)) : padicOddLiftENN f x = 0 :=
  Function.extend_apply' f (fun _ => 0) x hx

theorem padicOddLiftENN_measurable {f : ℤ_[3] → ℝ≥0∞} (hf : Measurable f) :
    Measurable (padicOddLiftENN f) :=
  (padicAffineBranch_measurableEmbedding 1).measurable_extend hf measurable_const

theorem padicOddLiftENN_indicator (f : ℤ_[3] → ℝ≥0∞) :
    (Set.range (padicAffineBranch 1)).indicator (padicOddLiftENN f) =
      padicOddLiftENN f := by
  funext x
  by_cases hx : x ∈ Set.range (padicAffineBranch 1)
  · exact Set.indicator_of_mem hx _
  · rw [Set.indicator_of_notMem hx, padicOddLiftENN_eq_zero f hx]

theorem padicAffineBranch_isOpenMap (a : ℕ+) : IsOpenMap (padicAffineBranch a) := by
  apply ((padicAffineBranch_continuous a).isClosedEmbedding
    (padicAffineBranch_injective a)).isEmbedding.isInducing.isOpenMap
  rw [padicAffineBranch_range]
  exact padic_cylinder_isOpen 1 _

theorem padicOddLiftENN_lowerSemicontinuous {f : ℤ_[3] → ℝ≥0∞}
    (hf : LowerSemicontinuous f) : LowerSemicontinuous (padicOddLiftENN f) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro t
  have he : {x | t < padicOddLiftENN f x} =
      padicAffineBranch 1 '' {x | t < f x} := by
    ext x
    by_cases hx : x ∈ Set.range (padicAffineBranch 1)
    · obtain ⟨y, rfl⟩ := hx
      simp only [Set.mem_setOf_eq, padicOddLiftENN_apply_branch]
      change y ∈ {x | t < f x} ↔ padicAffineBranch 1 y ∈ _
      exact (Function.Injective.mem_set_image (padicAffineBranch_injective 1)).symm
    · rw [Set.mem_setOf_eq, padicOddLiftENN_eq_zero f hx]
      exact iff_of_false (not_lt_of_ge (zero_le t))
        (fun ⟨y, _, hy⟩ => hx ⟨y, hy⟩)
  change IsOpen {x | t < padicOddLiftENN f x}
  rw [he]
  exact padicAffineBranch_isOpenMap 1 _ (hf.isOpen_preimage t)

theorem padicOddLiftENN_lintegral (f : ℤ_[3] → ℝ≥0∞) :
    (∫⁻ x : ℤ_[3], padicOddLiftENN f x ∂padicThreeHaar) =
      (1 / 3 : ℝ≥0∞) * ∫⁻ x : ℤ_[3], f x ∂padicThreeHaar := by
  have h := (padicAffineBranch_measurableEmbedding 1).lintegral_map
    (μ := padicThreeHaar) (padicOddLiftENN f)
  simp only [padicOddLiftENN_apply_branch] at h
  rw [padicAffineBranch_map_haar, lintegral_smul_measure,
    ← lintegral_indicator (padicAffineBranch_range_measurable 1),
    padicOddLiftENN_indicator] at h
  change (3 : ℝ≥0∞) * (∫⁻ x, padicOddLiftENN f x ∂padicThreeHaar) = _ at h
  calc
    _ = (1 / 3 : ℝ≥0∞) * (3 * ∫⁻ x, padicOddLiftENN f x ∂padicThreeHaar) := by
      rw [← mul_assoc]
      rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by finiteness), one_mul]
    _ = _ := by rw [h]

noncomputable def padicBinaryTransfer (f : ℤ_[3] → ℝ≥0∞) (x : ℤ_[3]) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * f (2 * x) + (3 / 2 : ℝ≥0∞) * padicOddLiftENN f x

theorem padicBinaryTransfer_measurable {f : ℤ_[3] → ℝ≥0∞} (hf : Measurable f) :
    Measurable (padicBinaryTransfer f) := by
  unfold padicBinaryTransfer
  exact (measurable_const.mul (hf.comp (by fun_prop))).add
    (measurable_const.mul (padicOddLiftENN_measurable hf))

theorem padicBinaryTransfer_lowerSemicontinuous {f : ℤ_[3] → ℝ≥0∞}
    (hf : LowerSemicontinuous f) : LowerSemicontinuous (padicBinaryTransfer f) := by
  have hmul (c : ℝ≥0∞) (hc : c ≠ ∞) {g : ℤ_[3] → ℝ≥0∞}
      (hg : LowerSemicontinuous g) : LowerSemicontinuous (fun x => c * g x) :=
    (ENNReal.continuous_const_mul hc).comp_lowerSemicontinuous hg
      (fun _ _ h => mul_le_mul_right h c)
  exact (hmul _ (by finiteness) (hf.comp (by fun_prop))).add
    (hmul _ (by finiteness) (padicOddLiftENN_lowerSemicontinuous hf))

theorem padicBinaryTransfer_lintegral {f : ℤ_[3] → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, padicBinaryTransfer f x ∂padicThreeHaar) =
      ∫⁻ x, f x ∂padicThreeHaar := by
  have hd : Measurable (fun x : ℤ_[3] => f (2 * x)) := hf.comp (by fun_prop)
  have he : Measurable (fun x : ℤ_[3] => (1 / 2 : ℝ≥0∞) * f (2 * x)) :=
    measurable_const.mul hd
  unfold padicBinaryTransfer
  rw [lintegral_add_left he, lintegral_const_mul _ hd,
    lintegral_const_mul _ (padicOddLiftENN_measurable hf),
    padicThreeHaar_doubling_preserving.lintegral_comp hf, padicOddLiftENN_lintegral,
    ← mul_assoc, ← add_mul]
  have hc : (1 / 2 : ℝ≥0∞) + 3 / 2 * (1 / 3) = 1 := by
    norm_num [div_eq_mul_inv, mul_comm (3 : ℝ≥0∞), mul_assoc,
      ← mul_assoc (2 : ℝ≥0∞)⁻¹, ENNReal.inv_mul_cancel]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
  rw [hc, one_mul]

theorem padicBinaryTransfer_ae_eq_of_le {f : ℤ_[3] → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ x, f x ∂padicThreeHaar) ≠ ∞)
    (hle : ∀ x, padicBinaryTransfer f x ≤ f x) :
    padicBinaryTransfer f =ᵐ[padicThreeHaar] f := by
  apply ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hle)
  · rwa [padicBinaryTransfer_lintegral hf]
  · exact hf.aemeasurable
  · exact (padicBinaryTransfer_lintegral hf).ge

theorem map_withDensity_comp_padic (μ : Measure ℤ_[3]) (T : ℤ_[3] → ℤ_[3])
    (hT : Measurable T) (g : ℤ_[3] → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (g ∘ T)).map T = (μ.map T).withDensity g := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs),
    withDensity_apply _ hs, setLIntegral_map hs hg hT]
  rfl

theorem padicThreeHaar_syracuseH_preserving :
    MeasurePreserving syracuseH padicThreeHaar padicThreeHaar := by
  let T : ℤ_[3] →+ ℤ_[3] :=
    { toFun := syracuseH
      map_zero' := by simp [syracuseH]
      map_add' := fun x y => by simp [syracuseH, mul_add] }
  apply AddMonoidHom.measurePreserving (f := T)
    (by change Continuous syracuseH; unfold syracuseH; fun_prop) ?_ rfl
  intro y
  refine ⟨2 * y, ?_⟩
  change (↑(padicTwoUnit⁻¹) : ℤ_[3]) * (2 * y) = y
  rw [← padicTwoUnit_coe, ← mul_assoc, Units.inv_mul, one_mul]

theorem padicWithDensity_map_syracuseH {f : ℤ_[3] → ℝ≥0∞} (hf : Measurable f) :
    (padicThreeHaar.withDensity f).map syracuseH =
      padicThreeHaar.withDensity (fun x => f (2 * x)) := by
  have he : (fun x : ℤ_[3] => f (2 * x)) ∘ syracuseH = f := by
    funext x
    simp only [Function.comp_def, syracuseH, ← mul_assoc, ← padicTwoUnit_coe,
      Units.mul_inv, one_mul]
  calc
    _ = (padicThreeHaar.withDensity ((fun x : ℤ_[3] => f (2 * x)) ∘ syracuseH)).map
        syracuseH := by rw [he]
    _ = _ := by
      rw [map_withDensity_comp_padic _ _ syracuseH_measurable
        (fun x : ℤ_[3] => f (2 * x)) (hf.comp (by fun_prop)),
        padicThreeHaar_syracuseH_preserving.map_eq]

theorem padicWithDensity_map_syracuseJ {f : ℤ_[3] → ℝ≥0∞} (hf : Measurable f) :
    (padicThreeHaar.withDensity f).map syracuseJ =
      (3 : ℝ≥0∞) • padicThreeHaar.withDensity (padicOddLiftENN f) := by
  have hj : syracuseJ = padicAffineBranch 1 := by
    funext x
    simp [syracuseJ, padicAffineBranch]
  rw [hj]
  have he : padicOddLiftENN f ∘ padicAffineBranch 1 = f := by
    funext x
    exact padicOddLiftENN_apply_branch f x
  calc
    _ = (padicThreeHaar.withDensity (padicOddLiftENN f ∘ padicAffineBranch 1)).map
        (padicAffineBranch 1) := by rw [he]
    _ = _ := by
      rw [map_withDensity_comp_padic _ _ (padicAffineBranch_measurable 1)
        (padicOddLiftENN f) (padicOddLiftENN_measurable hf), padicAffineBranch_map_haar,
        withDensity_smul_measure]
      congr 1
      rw [← withDensity_indicator (padicAffineBranch_range_measurable 1),
        padicOddLiftENN_indicator]

theorem padicBinaryTransfer_withDensity {f : ℤ_[3] → ℝ≥0∞} (hf : Measurable f) :
    padicThreeHaar.withDensity (padicBinaryTransfer f) =
      (1 / 2 : ℝ≥0∞) • (padicThreeHaar.withDensity f).map syracuseH +
      (1 / 2 : ℝ≥0∞) • (padicThreeHaar.withDensity f).map syracuseJ := by
  rw [padicWithDensity_map_syracuseH hf, padicWithDensity_map_syracuseJ hf]
  have he : padicBinaryTransfer f =
      (1 / 2 : ℝ≥0∞) • (fun x : ℤ_[3] => f (2 * x)) +
      (3 / 2 : ℝ≥0∞) • padicOddLiftENN f := rfl
  have hd : Measurable (fun x : ℤ_[3] => f (2 * x)) := hf.comp (by fun_prop)
  have hm : Measurable ((1 / 2 : ℝ≥0∞) • (fun x : ℤ_[3] => f (2 * x))) :=
    measurable_const.mul (hf.comp (by fun_prop))
  rw [he, withDensity_add_left hm,
    withDensity_smul _ hd,
    withDensity_smul _ (padicOddLiftENN_measurable hf), smul_smul]
  congr 2
  simp [div_eq_mul_inv, mul_comm]

theorem padicWithDensity_stationary_of_transfer_le {f : ℤ_[3] → ℝ≥0∞}
    (hf : Measurable f) (hfin : (∫⁻ x, f x ∂padicThreeHaar) ≠ ∞)
    (hle : ∀ x, padicBinaryTransfer f x ≤ f x) :
    IsSyracuseStationary (padicThreeHaar.withDensity f) := by
  have he := withDensity_congr_ae (padicBinaryTransfer_ae_eq_of_le hf hfin hle)
  exact he.symm.trans (padicBinaryTransfer_withDensity hf)

theorem padicBinaryTransfer_normalized_eq_canonical {f : ℤ_[3] → ℝ≥0∞}
    (hf : Measurable f) (hfin : (∫⁻ x, f x ∂padicThreeHaar) ≠ ∞)
    (hpos : (∫⁻ x, f x ∂padicThreeHaar) ≠ 0)
    (hle : ∀ x, padicBinaryTransfer f x ≤ f x) :
    padicThreeHaar.withDensity (fun x => (∫⁻ y, f y ∂padicThreeHaar)⁻¹ * f x) =
      canonicalSyracuseMeasure := by
  let m := ∫⁻ y, f y ∂padicThreeHaar
  let μ := padicThreeHaar.withDensity f
  have hm : μ Set.univ = m := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hp : IsProbabilityMeasure (m⁻¹ • μ) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul, hm]
    exact ENNReal.inv_mul_cancel hpos hfin
  have hs := padicWithDensity_stationary_of_transfer_le hf hfin hle
  have ht : IsSyracuseStationary (m⁻¹ • μ) := by
    change m⁻¹ • μ = _
    rw [Measure.map_smul, Measure.map_smul, smul_comm (1 / 2 : ℝ≥0∞) m⁻¹,
      smul_comm (1 / 2 : ℝ≥0∞) m⁻¹, ← smul_add]
    exact congrArg (fun ν : Measure ℤ_[3] => m⁻¹ • ν) hs
  change padicThreeHaar.withDensity (m⁻¹ • f) = _
  rw [withDensity_smul _ hf]
  exact eq_canonical_of_syracuse_stationary (m⁻¹ • μ) ht

theorem padicAffineBranch_one_eq_syracuseJ : padicAffineBranch 1 = syracuseJ := by
  funext x
  simp [syracuseJ, padicAffineBranch]

theorem padicAffineBranch_oddPredecessor {n : ℕ} (hn : n % 3 = 2) :
    padicAffineBranch 1 (oddPredecessor n : ℤ_[3]) = (n : ℤ_[3]) := by
  have hs := oddPredecessor_spec hn
  have ho := CollatzCylinderPacking.step_odd hs.2.1
  rw [hs.2.2] at ho
  have he : 1 + 3 * (oddPredecessor n : ℤ_[3]) = 2 * (n : ℤ_[3]) := by
    have he' : 1 + 3 * oddPredecessor n = 2 * n := by omega
    exact_mod_cast he'
  rw [padicAffineBranch_one_eq_syracuseJ, syracuseJ, he, ← mul_assoc,
    ← padicTwoUnit_coe, Units.inv_mul, one_mul]

theorem padicAffineBranch_natCast_not_mem_range {n : ℕ} (hn : n % 3 ≠ 2) :
    (n : ℤ_[3]) ∉ Set.range (padicAffineBranch 1) := by
  rintro ⟨y, hy⟩
  rw [padicAffineBranch_one_eq_syracuseJ] at hy
  have he := syracuseJ_mod_three y
  rw [hy, map_natCast] at he
  have hv := congrArg (fun x : ZMod (3 ^ 1) => x.val) he
  norm_num [ZMod.val_natCast] at hv
  exact hn hv

#print axioms padicOddLiftENN_lowerSemicontinuous
#print axioms padicBinaryTransfer_lintegral
#print axioms padicBinaryTransfer_ae_eq_of_le
#print axioms padicBinaryTransfer_withDensity
#print axioms padicBinaryTransfer_normalized_eq_canonical

end Erdos1135.Tao

namespace CollatzCanonical.IntegerStationaryEnvelope
open Erdos1135.Tao

theorem actualIntegerTrace_harmonic {n : ℕ} (hn : 0 < n) :
    actualIntegerTrace n = (1 / 2 : ℝ≥0∞) * actualIntegerTrace (2 * n) +
      (3 / 2 : ℝ≥0∞) * (if n % 3 = 2 then actualIntegerTrace (oddPredecessor n) else 0) := by
  have hnonneg (m : ℕ) (hm : 0 < m) : 0 ≤ actualDensityValue actualFirstHitDensity m := by
    by_cases hu : m % 3 = 0
    · rw [actual_trace_zero_of_multiple_three hu]
    · exact ((actual_trace_positive_iff_unit hm).mpr hu).le
  unfold actualIntegerTrace
  rw [actual_unconditional_density_harmonic hn]
  have ho : 0 ≤ (if n % 3 = 2 then
      actualDensityValue actualFirstHitDensity (oddPredecessor n) else 0) := by
    split_ifs with h
    · exact hnonneg _ (oddPredecessor_spec h).1
    · exact le_rfl
  rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (hnonneg _ (by omega)))
    (mul_nonneg (by norm_num) ho), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num)]
  simp only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  split_ifs <;> simp only [ENNReal.ofReal_zero]

theorem canonicalIntegerEnvelope_transfer_le :
    ∀ x, padicBinaryTransfer canonicalIntegerEnvelope x ≤ canonicalIntegerEnvelope x := by
  apply padicIntegerEnvelope_maximal actualIntegerTrace
    (padicBinaryTransfer canonicalIntegerEnvelope)
    (padicBinaryTransfer_lowerSemicontinuous canonicalIntegerEnvelope_lowerSemicontinuous)
  intro n hn
  rw [actualIntegerTrace_harmonic hn]
  unfold padicBinaryTransfer
  apply add_le_add
  · apply mul_le_mul_right
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      canonicalIntegerEnvelope_natCast_le (2 * n) (by omega)
  · apply mul_le_mul_right
    by_cases hu : n % 3 = 2
    · rw [if_pos hu, ← padicAffineBranch_oddPredecessor hu, padicOddLiftENN_apply_branch]
      exact canonicalIntegerEnvelope_natCast_le _ (oddPredecessor_spec hu).1
    · rw [if_neg hu, padicOddLiftENN_eq_zero _ (padicAffineBranch_natCast_not_mem_range hu)]

#print axioms canonicalIntegerEnvelope_transfer_le

end CollatzCanonical.IntegerStationaryEnvelope
