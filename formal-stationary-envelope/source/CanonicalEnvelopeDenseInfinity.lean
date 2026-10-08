import CanonicalEnvelopeInfiniteOrbit
import PowerTwoModuloThree
import Mathlib.Topology.GDelta.Basic

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology
open Erdos1135.Tao CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem syracuseH_iterate_eq (a : ℕ) (x : ℤ_[3]) :
    (syracuseH^[a]) x = (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ a * x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', syracuseH, ih, pow_succ]
    ring

theorem two_pow_mul_syracuseH_iterate (a : ℕ) (x : ℤ_[3]) :
    (2 : ℤ_[3]) ^ a * (syracuseH^[a]) x = x := by
  rw [syracuseH_iterate_eq, ← mul_assoc, ← mul_pow,
    ← padicTwoUnit_coe, Units.mul_inv, one_pow, one_mul]

theorem halving_neg_one_cylinder_dense (j : ℕ) (x : ℤ_[3]) (hx : IsUnit x) :
    ∃ a : ℕ, PadicInt.toZModPow (j + 1) ((syracuseH^[a]) (-1)) =
      PadicInt.toZModPow (j + 1) x := by
  let y : ℤ_[3] := -(↑(hx.unit⁻¹) : ℤ_[3])
  have hy : IsUnit y := (hx.unit⁻¹).isUnit.neg
  have hyx : y * x = -1 := by
    dsimp only [y]
    rw [neg_mul]
    exact congrArg Neg.neg (by simpa only [hx.unit_spec] using Units.inv_mul hx.unit)
  obtain ⟨a, ha⟩ := CollatzPowerTwo.exists_two_power_mod (j + 1)
    (PadicInt.toZModPow (j + 1) y).val
    ((padicThree_isUnit_iff_projection_val_mod_three j y).mp hy)
  have hp : (2 : ZMod (3 ^ (j + 1))) ^ a = PadicInt.toZModPow (j + 1) y := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ha
    simpa only [Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_zmod_val] using h
  have hpu : IsUnit ((2 : ZMod (3 ^ (j + 1))) ^ a) := by
    rw [hp]
    exact hy.map (PadicInt.toZModPow (j + 1))
  refine ⟨a, hpu.mul_left_cancel ?_⟩
  have hleft := congrArg (PadicInt.toZModPow (j + 1))
    (two_pow_mul_syracuseH_iterate a (-1))
  have hright := congrArg (PadicInt.toZModPow (j + 1)) hyx
  simp only [map_mul, map_pow, map_ofNat, map_neg, map_one] at hleft hright
  rw [hleft, hp]
  exact hright.symm

theorem canonicalIntegerEnvelope_infinite_in_unit_cylinder (j : ℕ)
    (x : ℤ_[3]) (hx : IsUnit x) :
    ∃ y : ℤ_[3], PadicInt.toZModPow (j + 1) y = PadicInt.toZModPow (j + 1) x ∧
      canonicalIntegerEnvelope y = ⊤ := by
  obtain ⟨a, ha⟩ := halving_neg_one_cylinder_dense j x hx
  exact ⟨_, ha, canonicalIntegerEnvelope_halving_neg_one_eq_top a⟩

theorem canonicalIntegerEnvelope_infinity_closure :
    closure {x : ℤ_[3] | canonicalIntegerEnvelope x = ⊤} = {x | IsUnit x} := by
  apply Set.Subset.antisymm
  · have hclosed : IsClosed {x : ℤ_[3] | IsUnit x} := by
      have he : {x : ℤ_[3] | IsUnit x} =
          {x | PadicInt.toZModPow 1 x = 0}ᶜ := by
        ext x
        exact padicThree_isUnit_iff_projection_ne_zero x
      rw [he]
      exact (padic_cylinder_isOpen 1 0).isClosed_compl
    apply closure_minimal _ hclosed
    intro x hx
    by_contra hnu
    have hzero := canonicalIntegerEnvelope_zero_of_not_isUnit x hnu
    exact ENNReal.zero_ne_top (hzero.symm.trans hx)
  · intro x hx
    apply mem_closure_iff_nhds.mpr
    intro s hs
    obtain ⟨k, hk⟩ := padic_cylinder_subset_nhds hs
    obtain ⟨y, hy, hinf⟩ := canonicalIntegerEnvelope_infinite_in_unit_cylinder k x hx
    exact ⟨y, hk (padic_projection_refines (Nat.le_succ k) hy), hinf⟩

theorem canonicalIntegerEnvelope_infinity_isGDelta :
    IsGδ {x : ℤ_[3] | canonicalIntegerEnvelope x = ⊤} := by
  have he : {x : ℤ_[3] | canonicalIntegerEnvelope x = ⊤} =
      ⋂ m : ℕ, {x | (m : ℝ≥0∞) < canonicalIntegerEnvelope x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hx m
      rw [hx]
      exact ENNReal.natCast_lt_top m
    · intro hx
      apply top_unique
      rw [← ENNReal.iSup_natCast]
      exact iSup_le fun m => (hx m).le
  rw [he]
  exact IsGδ.iInter_of_isOpen fun m =>
    canonicalIntegerEnvelope_lowerSemicontinuous.isOpen_preimage (m : ℝ≥0∞)

theorem canonicalIntegerEnvelope_infinity_haar_null :
    padicThreeHaar {x | canonicalIntegerEnvelope x = ⊤} = 0 := by
  have ha := ae_lt_top canonicalIntegerEnvelope_lowerSemicontinuous.measurable
    (show (∫⁻ x, canonicalIntegerEnvelope x ∂padicThreeHaar) ≠ ⊤ by
      rw [canonicalIntegerEnvelope_lintegral_eq_one]
      exact ENNReal.one_ne_top)
  have hn : ∀ᵐ x ∂padicThreeHaar, canonicalIntegerEnvelope x ≠ ⊤ := by
    filter_upwards [ha] with x hx using ne_of_lt hx
  simpa only [not_not] using ae_iff.mp hn

theorem padic_cylinder_has_positive_odd_integer (k : ℕ) (x : ℤ_[3]) :
    ∃ n : ℕ, 0 < n ∧ n % 2 = 1 ∧
      PadicInt.toZModPow k (n : ℤ_[3]) = PadicInt.toZModPow k x := by
  let b := (PadicInt.toZModPow k x).val
  let n := if b % 2 = 1 then b + 2 * 3 ^ k else b + 3 ^ k
  have hpow : 3 ^ k % 2 = 1 := by simp [Nat.pow_mod]
  have hb : b % 2 < 2 := Nat.mod_lt _ (by decide)
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp only [n]
    split_ifs <;> positivity
  · dsimp only [n]
    split_ifs with h
    · simp [Nat.add_mod, h]
    · have hz : b % 2 = 0 := by omega
      simp [Nat.add_mod, hz, hpow]
  · rw [map_natCast]
    dsimp only [n, b]
    split_ifs <;> simp

theorem actual_trace_unbounded_in_unit_cylinder (j : ℕ)
    (x : ℤ_[3]) (hx : IsUnit x) (M : ℝ) :
    ∃ n : ℕ, 0 < n ∧ n % 2 = 1 ∧
      PadicInt.toZModPow (j + 1) (n : ℤ_[3]) = PadicInt.toZModPow (j + 1) x ∧
      M < actualDensityValue actualFirstHitDensity n := by
  obtain ⟨y, hy, hinf⟩ := canonicalIntegerEnvelope_infinite_in_unit_cylinder j x hx
  have hhigh : ENNReal.ofReal M < canonicalIntegerEnvelope y := by
    rw [hinf]
    exact ENNReal.ofReal_lt_top
  obtain ⟨k, hk⟩ := padic_cylinder_subset_nhds
    (canonicalIntegerEnvelope_lowerSemicontinuous y (ENNReal.ofReal M) hhigh)
  obtain ⟨n, hn, hodd, hproj⟩ :=
    padic_cylinder_has_positive_odd_integer (max k (j + 1)) y
  refine ⟨n, hn, hodd, (padic_projection_refines (le_max_right k (j + 1)) hproj).trans hy, ?_⟩
  have hbound := hk (padic_projection_refines (le_max_left k (j + 1)) hproj)
  change ENNReal.ofReal M < canonicalIntegerEnvelope (n : ℤ_[3]) at hbound
  rw [canonicalIntegerEnvelope_natCast_eq hn, actualIntegerTrace] at hbound
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hbound).1

theorem canonicalIntegerEnvelope_not_continuousAt_of_unit_finite
    (x : ℤ_[3]) (hx : IsUnit x) (hfin : canonicalIntegerEnvelope x ≠ ⊤) :
    ¬ ContinuousAt canonicalIntegerEnvelope x := by
  intro hc
  obtain ⟨b, hb, _hbtop⟩ := exists_between (lt_top_iff_ne_top.mpr hfin)
  have hnear : {y | canonicalIntegerEnvelope y < b} ∈ 𝓝 x :=
    hc.eventually (gt_mem_nhds hb)
  have hxcl : x ∈ closure {y : ℤ_[3] | canonicalIntegerEnvelope y = ⊤} := by
    rwa [canonicalIntegerEnvelope_infinity_closure]
  obtain ⟨y, hy, hytop⟩ := (mem_closure_iff_nhds.mp hxcl) _ hnear
  change canonicalIntegerEnvelope y < b at hy
  rw [hytop] at hy
  exact not_lt_of_ge le_top hy

theorem canonicalIntegerEnvelope_not_continuousAt_positive_unit
    (n : ℕ) (hn : 0 < n) (hu : n % 3 ≠ 0) :
    ¬ ContinuousAt canonicalIntegerEnvelope (n : ℤ_[3]) := by
  apply canonicalIntegerEnvelope_not_continuousAt_of_unit_finite _
    ((padic_natCast_isUnit_iff n).mpr hu)
  rw [canonicalIntegerEnvelope_natCast_eq hn]
  exact ne_of_lt (actualIntegerTrace_lt_top n)

#print axioms canonicalIntegerEnvelope_infinity_closure
#print axioms canonicalIntegerEnvelope_infinity_isGDelta
#print axioms canonicalIntegerEnvelope_infinity_haar_null
#print axioms actual_trace_unbounded_in_unit_cylinder
#print axioms canonicalIntegerEnvelope_not_continuousAt_positive_unit

end CollatzCanonical.IntegerStationaryEnvelope
