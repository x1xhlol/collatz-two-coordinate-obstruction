import PadicCylinderDetermining
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal

namespace CollatzCylinderPacking.Arithmetic

theorem padic_cylinder_isOpen (k : ℕ) (v : ZMod (3 ^ k)) :
    IsOpen {x : ℤ_[3] | PadicInt.toZModPow k x = v} := by
  have he : {x : ℤ_[3] | PadicInt.toZModPow k x = v} =
      Metric.closedBall (v.val : ℤ_[3]) ((3 : ℝ) ^ (-k : ℤ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm]
    rw [norm_span_three, ← kernel_three k, RingHom.mem_ker, map_sub,
      map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]
  rw [he]
  exact IsUltrametricDist.isOpen_closedBall _ (ne_of_gt (zpow_pos (by norm_num) _))

theorem padic_projection_dist_le (k : ℕ) {x y : ℤ_[3]}
    (he : PadicInt.toZModPow k x = PadicInt.toZModPow k y) :
    dist x y ≤ (1 / 3 : ℝ) ^ k := by
  have hi : x - y ∈ (Ideal.span {(3 : ℤ_[3]) ^ k} : Ideal ℤ_[3]) := by
    rw [← kernel_three k, RingHom.mem_ker, map_sub, he, sub_self]
  have hn := (norm_span_three _ k).mpr hi
  rw [dist_eq_norm]
  convert hn using 1
  simp [zpow_neg, zpow_natCast, one_div, inv_pow]

theorem padic_cylinder_subset_nhds {x : ℤ_[3]} {s : Set ℤ_[3]}
    (hs : s ∈ 𝓝 x) :
    ∃ k : ℕ, {y | PadicInt.toZModPow k y = PadicInt.toZModPow k x} ⊆ s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have ht : Tendsto (fun k : ℕ => (1 / 3 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨k, fun y hy => hball ?_⟩
  exact lt_of_le_of_lt (padic_projection_dist_le k hy) hk

noncomputable def padicIntegerStep (g : ℕ → ℝ≥0∞) (k : ℕ) (x : ℤ_[3]) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (_ : 0 < n)
    (_ : PadicInt.toZModPow k (n : ℤ_[3]) = PadicInt.toZModPow k x), g n

noncomputable def padicIntegerEnvelope (g : ℕ → ℝ≥0∞) (x : ℤ_[3]) : ℝ≥0∞ :=
  ⨆ k : ℕ, padicIntegerStep g k x

theorem padicIntegerStep_eq_of_projection_eq (g : ℕ → ℝ≥0∞) (k : ℕ)
    {x y : ℤ_[3]} (he : PadicInt.toZModPow k x = PadicInt.toZModPow k y) :
    padicIntegerStep g k x = padicIntegerStep g k y := by
  simp only [padicIntegerStep, he]

theorem padicIntegerStep_continuous (g : ℕ → ℝ≥0∞) (k : ℕ) :
    Continuous (padicIntegerStep g k) := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | PadicInt.toZModPow k y = PadicInt.toZModPow k x},
    padic_cylinder_isOpen k _, rfl, ?_⟩
  intro y hy
  exact padicIntegerStep_eq_of_projection_eq g k hy

theorem padicIntegerStep_natCast_le (g : ℕ → ℝ≥0∞) (k n : ℕ) (hn : 0 < n) :
    padicIntegerStep g k (n : ℤ_[3]) ≤ g n := by
  exact iInf_le_of_le n (iInf_le_of_le hn (iInf_le_of_le rfl le_rfl))

theorem padicIntegerStep_monotone (g : ℕ → ℝ≥0∞) (x : ℤ_[3]) :
    Monotone (fun k => padicIntegerStep g k x) := by
  intro k m hkm
  refine le_iInf fun n => le_iInf fun hn => le_iInf fun he => ?_
  exact iInf_le_of_le n (iInf_le_of_le hn
    (iInf_le_of_le (padic_projection_refines hkm he) le_rfl))

theorem padicIntegerEnvelope_lowerSemicontinuous (g : ℕ → ℝ≥0∞) :
    LowerSemicontinuous (padicIntegerEnvelope g) :=
  lowerSemicontinuous_iSup fun k => (padicIntegerStep_continuous g k).lowerSemicontinuous

theorem padicIntegerEnvelope_natCast_le (g : ℕ → ℝ≥0∞) (n : ℕ) (hn : 0 < n) :
    padicIntegerEnvelope g (n : ℤ_[3]) ≤ g n :=
  iSup_le fun k => padicIntegerStep_natCast_le g k n hn

theorem padicIntegerEnvelope_maximal (g : ℕ → ℝ≥0∞) (f : ℤ_[3] → ℝ≥0∞)
    (hf : LowerSemicontinuous f) (hb : ∀ n : ℕ, 0 < n → f (n : ℤ_[3]) ≤ g n) :
    f ≤ padicIntegerEnvelope g := by
  intro x
  apply le_of_forall_lt_imp_le_of_dense
  intro a ha
  obtain ⟨k, hk⟩ := padic_cylinder_subset_nhds (hf x a ha)
  apply le_trans (b := padicIntegerStep g k x)
  · refine le_iInf fun n => le_iInf fun hn => le_iInf fun he => ?_
    exact (le_of_lt (hk he)).trans (hb n hn)
  · exact le_iSup (fun j => padicIntegerStep g j x) k

theorem padicIntegerStep_lt_top (g : ℕ → ℝ≥0∞)
    (hg : ∀ n : ℕ, 0 < n → g n < ⊤) (k : ℕ) (x : ℤ_[3]) :
    padicIntegerStep g k x < ⊤ := by
  let n := (PadicInt.toZModPow k x).val + 3 ^ k
  have hn : 0 < n := by dsimp [n]; positivity
  have he : PadicInt.toZModPow k (n : ℤ_[3]) = PadicInt.toZModPow k x := by
    rw [map_natCast]
    simp only [n, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
  exact lt_of_le_of_lt
    (iInf_le_of_le n (iInf_le_of_le hn (iInf_le_of_le he le_rfl))) (hg n hn)

theorem padicIntegerStep_toReal_continuous (g : ℕ → ℝ≥0∞)
    (hg : ∀ n : ℕ, 0 < n → g n < ⊤) (k : ℕ) :
    Continuous (fun x => (padicIntegerStep g k x).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (ENNReal.continuousAt_toReal (ne_of_lt (padicIntegerStep_lt_top g hg k x))).comp
    (padicIntegerStep_continuous g k).continuousAt

theorem padicIntegerStep_le_envelope (g : ℕ → ℝ≥0∞) (k : ℕ) (x : ℤ_[3]) :
    padicIntegerStep g k x ≤ padicIntegerEnvelope g x :=
  le_iSup (fun j => padicIntegerStep g j x) k

theorem padicIntegerEnvelope_lintegral (g : ℕ → ℝ≥0∞) (μ : Measure ℤ_[3]) :
    (∫⁻ x, padicIntegerEnvelope g x ∂μ) = ⨆ k, ∫⁻ x, padicIntegerStep g k x ∂μ := by
  apply lintegral_iSup (fun k => (padicIntegerStep_continuous g k).measurable)
  intro k m hkm x
  exact padicIntegerStep_monotone g x hkm

#print axioms padicIntegerEnvelope_maximal
#print axioms padicIntegerEnvelope_lintegral

end CollatzCylinderPacking.Arithmetic
