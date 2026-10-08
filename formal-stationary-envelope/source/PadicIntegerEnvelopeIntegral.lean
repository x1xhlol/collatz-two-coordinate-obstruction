import CanonicalIntegerEnvelope
import PeriodicTraceTestIntegralBoundFromLayers
import CanonicalTracePolynomialFloor
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
open CollatzCylinderPacking.Arithmetic Erdos1135.Tao

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem sum_range_zmod {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ n ∈ Finset.range q, f (n : ZMod q)) = ∑ z : ZMod q, f z := by
  classical
  apply Finset.sum_bij (fun (n : ℕ) (_ : n ∈ Finset.range q) => (n : ZMod q))
  · intro n hn
    exact Finset.mem_univ _
  · intro n hn m hm he
    have h := congrArg ZMod.val he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hn),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hm)] using h
  · intro z _
    exact ⟨z.val, Finset.mem_range.mpr z.val_lt, ZMod.natCast_zmod_val z⟩
  · intro n _
    rfl

theorem odd_mask_cylinder_sum (k : ℕ) (f : ZMod (3 ^ k) → ℝ) :
    (∑ n ∈ Finset.range (2 * 3 ^ k), if n % 2 = 1 then f (n : ZMod (3 ^ k)) else 0) =
      ∑ z : ZMod (3 ^ k), f z := by
  classical
  have hodd : 3 ^ k % 2 = 1 := by simp [Nat.pow_mod]
  rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  have hpair (n : ℕ) :
      (if n % 2 = 1 then f (n : ZMod (3 ^ k)) else 0) +
      (if (3 ^ k + n) % 2 = 1 then f ((3 ^ k + n : ℕ) : ZMod (3 ^ k)) else 0) =
      f (n : ZMod (3 ^ k)) := by
    have he : ((3 ^ k + n : ℕ) : ZMod (3 ^ k)) = (n : ZMod (3 ^ k)) := by
      rw [Nat.cast_add, ZMod.natCast_self, zero_add]
    rw [he]
    have hm : n % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases hn : n % 2 = 1
    · have hs : (3 ^ k + n) % 2 ≠ 1 := by rw [Nat.add_mod, hodd, hn]; decide
      simp only [if_pos hn, if_neg hs, add_zero]
    · have hn0 : n % 2 = 0 := by omega
      have hs : (3 ^ k + n) % 2 = 1 := by rw [Nat.add_mod, hodd, hn0]
      simp only [if_neg hn, if_pos hs, zero_add]
  simp_rw [hpair]
  exact sum_range_zmod f

theorem dominated_cylinder_integral_le_one (k : ℕ) (f : ZMod (3 ^ k) → ℝ)
    (hf0 : ∀ z, 0 ≤ f z)
    (hfunit : ∀ n : ℕ, n % 3 = 0 → f (n : ZMod (3 ^ k)) = 0)
    (hfdom : ∀ n : ℕ, 0 < n → n % 3 ≠ 0 →
      f (n : ZMod (3 ^ k)) ≤ actualDensityValue actualFirstHitDensity n) :
    (∫ x, f (PadicInt.toZModPow k x) ∂padicThreeHaar) ≤ 1 := by
  classical
  let a : ℕ → ℝ := fun n => if n % 2 = 1 then f (n : ZMod (3 ^ k)) else 0
  let L : ℝ := ∑ z : ZMod (3 ^ k), f z
  have hL : 0 ≤ L := Finset.sum_nonneg (fun z _ => hf0 z)
  have hfL (z : ZMod (3 ^ k)) : f z ≤ L :=
    Finset.single_le_sum (fun z _ => hf0 z) (Finset.mem_univ z)
  have ha : Function.Periodic a (2 * 3 ^ k) := by
    intro n
    have hm : (n + 2 * 3 ^ k) % 2 = n % 2 := by omega
    have he : ((n + 2 * 3 ^ k : ℕ) : ZMod (3 ^ k)) = (n : ZMod (3 ^ k)) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
    simp only [a, hm, he]
  have hbound := periodic_actual_density_value_mean_le_half_from_layers
    (by positivity : 0 < 2 * 3 ^ k) a ha hL
    (fun n => by dsimp [a]; split_ifs; exact hf0 _; exact le_rfl)
    (fun n => by dsimp [a]; split_ifs; exact hfL _; exact hL)
    (fun n hn => by
      dsimp [a]
      split_ifs with ho
      · exact hfunit n (by tauto)
      · rfl)
    (fun n hn hu => by
      dsimp [a]
      split_ifs
      · exact hfdom n hn hu
      · exact ((actual_trace_positive_iff_unit hn).mpr hu).le)
  change (∑ n ∈ Finset.range (2 * 3 ^ k),
    if n % 2 = 1 then f (n : ZMod (3 ^ k)) else 0) / (2 * 3 ^ k : ℕ) ≤ 1 / 2 at hbound
  rw [odd_mask_cylinder_sum] at hbound
  rw [integral_padicThreeHaar_cylinder]
  have hq : (0 : ℝ) < 3 ^ k := by positivity
  have hb := (div_le_iff₀ (show (0 : ℝ) < (2 * 3 ^ k : ℕ) by positivity)).mp hbound
  rw [div_le_iff₀ hq]
  push_cast at hb
  nlinarith only [hb]

theorem canonicalIntegerStep_residue (k : ℕ) (x : ℤ_[3]) :
    canonicalIntegerStep k (((PadicInt.toZModPow k x).val : ℕ) : ℤ_[3]) =
      canonicalIntegerStep k x := by
  apply padicIntegerStep_eq_of_projection_eq
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem canonicalIntegerStep_integral_le_one (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, (canonicalIntegerStep k x).toReal ∂padicThreeHaar) ≤ 1 := by
  let f : ZMod (3 ^ k) → ℝ := fun z => (canonicalIntegerStep k (z.val : ℤ_[3])).toReal
  have he (n : ℕ) : f (n : ZMod (3 ^ k)) = (canonicalIntegerStep k (n : ℤ_[3])).toReal := by
    have h := canonicalIntegerStep_residue k (n : ℤ_[3])
    rw [map_natCast] at h
    exact congrArg ENNReal.toReal h
  have hbound := dominated_cylinder_integral_le_one k f
    (fun _ => ENNReal.toReal_nonneg)
    (fun n hn => by
      rw [he, canonicalIntegerStep_zero_of_not_isUnit k hk _
        (by rw [padic_natCast_isUnit_iff]; exact not_not.mpr hn), ENNReal.toReal_zero])
    (fun n hn hu => by
      rw [he]
      have ht := ENNReal.toReal_mono (ne_of_lt (actualIntegerTrace_lt_top n))
        (padicIntegerStep_natCast_le actualIntegerTrace k n hn)
      exact ht.trans_eq (ENNReal.toReal_ofReal ((actual_trace_positive_iff_unit hn).mpr hu).le))
  have heq : (fun x => f (PadicInt.toZModPow k x)) =
      (fun x => (canonicalIntegerStep k x).toReal) := by
    funext x
    exact congrArg ENNReal.toReal (canonicalIntegerStep_residue k x)
  rwa [heq] at hbound

theorem canonicalIntegerStep_toReal_integrable (k : ℕ) :
    Integrable (fun x => (canonicalIntegerStep k x).toReal) padicThreeHaar := by
  have h := (canonicalIntegerStep_toReal_continuous k).continuousOn.integrableOn_compact
    (μ := padicThreeHaar) isCompact_univ
  simpa only [integrableOn_univ] using h

theorem canonicalIntegerStep_lintegral_le_one (k : ℕ) :
    (∫⁻ x, canonicalIntegerStep k x ∂padicThreeHaar) ≤ 1 := by
  have hbase (j : ℕ) (hj : 1 ≤ j) : (∫⁻ x, canonicalIntegerStep j x ∂padicThreeHaar) ≤ 1 := by
    have he := ofReal_integral_eq_lintegral_ofReal (canonicalIntegerStep_toReal_integrable j)
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    simp only [ENNReal.ofReal_toReal (ne_of_lt (canonicalIntegerStep_lt_top j _))] at he
    rw [← he]
    exact_mod_cast ENNReal.ofReal_le_ofReal (canonicalIntegerStep_integral_le_one j hj)
  exact (lintegral_mono (fun x => padicIntegerStep_monotone actualIntegerTrace x
    (Nat.le_succ k))).trans (hbase (k + 1) (by omega))

theorem canonicalIntegerEnvelope_lintegral_le_one :
    (∫⁻ x, canonicalIntegerEnvelope x ∂padicThreeHaar) ≤ 1 := by
  rw [canonicalIntegerEnvelope, padicIntegerEnvelope_lintegral]
  exact iSup_le canonicalIntegerStep_lintegral_le_one

theorem canonicalIntegerEnvelope_uniform_unit_floor :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ ∀ x : ℤ_[3], IsUnit x → c ≤ canonicalIntegerEnvelope x := by
  obtain ⟨c, hc, hfloor⟩ := PeriodicCensusFloor.exists_uniform_unit_canonical_trace_floor
  refine ⟨ENNReal.ofReal c, ENNReal.ofReal_pos.mpr hc, ENNReal.ofReal_lt_top, ?_⟩
  intro x hx
  apply le_trans (b := canonicalIntegerStep 1 x)
  · refine le_iInf fun n => le_iInf fun hn => le_iInf fun he => ?_
    have hu : n % 3 ≠ 0 := by
      apply (padic_natCast_isUnit_iff n).mp
      rw [padicThree_isUnit_iff_projection_ne_zero, he]
      exact (padicThree_isUnit_iff_projection_ne_zero x).mp hx
    exact ENNReal.ofReal_le_ofReal (hfloor n hn hu)
  · exact padicIntegerStep_le_envelope actualIntegerTrace 1 x

theorem canonicalIntegerEnvelope_lintegral_pos :
    0 < ∫⁻ x, canonicalIntegerEnvelope x ∂padicThreeHaar := by
  obtain ⟨c, hc, _hcfin, hfloor⟩ := canonicalIntegerEnvelope_uniform_unit_floor
  have hmono : (∫⁻ x, {x : ℤ_[3] | IsUnit x}.indicator (fun _ => c) x ∂padicThreeHaar) ≤
      ∫⁻ x, canonicalIntegerEnvelope x ∂padicThreeHaar := by
    apply lintegral_mono
    intro x
    by_cases hx : IsUnit x
    · simpa only [Set.indicator_of_mem (show x ∈ {x : ℤ_[3] | IsUnit x} from hx)]
        using hfloor x hx
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℤ_[3] | IsUnit x} from hx)]
      exact zero_le _
  rw [lintegral_indicator_const padicThree_units_measurable, padicThreeHaar_units] at hmono
  exact (ENNReal.mul_pos_iff.mpr ⟨hc, by norm_num⟩).trans_le hmono

#print axioms dominated_cylinder_integral_le_one
#print axioms canonicalIntegerEnvelope_lintegral_le_one
#print axioms canonicalIntegerEnvelope_lintegral_pos
#print axioms canonicalIntegerEnvelope_uniform_unit_floor

end CollatzCanonical.IntegerStationaryEnvelope
