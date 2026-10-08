import PeriodicSourceMean
import WeightedKernelLimit
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

noncomputable section

def logarithmicSourceMean (w : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ q ∈ Finset.range X, w (q + 1) / (q + 1 : ℝ)) / Real.log X

theorem sourceMean_shift_of_bounded (w : ℕ → ℝ) {C L : ℝ}
    (hw : ∀ q, |w q| ≤ C) (hmean : Tendsto (sourceMean w) atTop (𝓝 L)) :
    Tendsto (sourceMean (fun q => w (q + 1))) atTop (𝓝 L) := by
  have hz : Tendsto (fun X : ℕ => (w X - w 0) / (X : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (2 * C))
    filter_upwards [] with X
    have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hX]
    apply div_le_div_of_nonneg_right _ hX
    exact (abs_sub _ _).trans (by linarith [hw X, hw 0])
  have h := hmean.add hz
  simp only [add_zero] at h
  convert h using 1
  funext X
  have hs := sourceMean_shift_sub w X
  linarith

def harmonicCesaroNumerator (X n : ℕ) : ℝ :=
  if n < X then 1 / (n + 2 : ℝ) else if n = X then 1 else 0

theorem harmonicCesaroNumerator_nonneg (X n : ℕ) :
    0 ≤ harmonicCesaroNumerator X n := by
  unfold harmonicCesaroNumerator
  split_ifs <;> positivity

theorem harmonicCesaroNumerator_support (X n : ℕ) (hn : n ∉ Finset.range (X + 1)) :
    harmonicCesaroNumerator X n = 0 := by
  have hn' : X < n := by simpa using hn
  simp [harmonicCesaroNumerator, show ¬ n < X by omega, show n ≠ X by omega]

theorem harmonicCesaroNumerator_sum (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), harmonicCesaroNumerator X n) = harmonic (X + 1) := by
  rw [Finset.sum_range_succ]
  have hsum : (∑ n ∈ Finset.range X, harmonicCesaroNumerator X n) =
      ∑ n ∈ Finset.range X, 1 / (n + 2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [harmonicCesaroNumerator, Finset.mem_range.mp hn]
  rw [hsum]
  clear hsum
  simp only [harmonicCesaroNumerator, lt_self_iff_false, ↓reduceIte]
  induction X with
  | zero => norm_num [harmonic]
  | succ X ih =>
    rw [Finset.sum_range_succ, harmonic_succ]
    push_cast
    rw [← ih]
    ring

theorem harmonic_succ_pos (X : ℕ) : (0 : ℝ) < harmonic (X + 1) := by
  have hnonneg : (0 : ℚ) ≤ harmonic X := by
    unfold harmonic
    positivity
  rw [harmonic_succ]
  push_cast
  have : (0 : ℝ) ≤ (harmonic X : ℝ) := by exact_mod_cast hnonneg
  positivity

theorem harmonic_atTop : Tendsto (fun X : ℕ => (harmonic X : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun X => log_add_one_le_harmonic X)
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

theorem harmonicCesaro_abel_identity (w : ℕ → ℝ) (X : ℕ) :
    (∑ q ∈ Finset.range (X + 1), w (q + 1) / (q + 1 : ℝ)) =
      ∑ n ∈ Finset.range (X + 1), harmonicCesaroNumerator X n *
        sourceMean (fun q => w (q + 1)) (n + 1) := by
  have hrewrite (Y : ℕ) :
      (∑ n ∈ Finset.range (Y + 1), harmonicCesaroNumerator Y n *
        sourceMean (fun q => w (q + 1)) (n + 1)) =
      (∑ n ∈ Finset.range Y, sourceMean (fun q => w (q + 1)) (n + 1) /
        (n + 2 : ℝ)) + sourceMean (fun q => w (q + 1)) (Y + 1) := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      simp [harmonicCesaroNumerator, Finset.mem_range.mp hn, div_eq_mul_inv, mul_comm]
    · simp [harmonicCesaroNumerator]
  rw [hrewrite]
  induction X with
  | zero => simp [sourceMean]
  | succ X ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [sourceMean, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    have h1 : (X : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (X : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem harmonic_weighted_sourceMean (w : ℕ → ℝ) {C L : ℝ}
    (hw : ∀ q, |w q| ≤ C) (hmean : Tendsto (sourceMean w) atTop (𝓝 L)) :
    Tendsto (fun X : ℕ =>
      (∑ q ∈ Finset.range X, w (q + 1) / (q + 1 : ℝ)) / (harmonic X : ℝ))
      atTop (𝓝 L) := by
  let K : ℕ → ℕ → ℝ := fun X n => harmonicCesaroNumerator X n / harmonic (X + 1)
  have hK0 (X n : ℕ) : 0 ≤ K X n :=
    div_nonneg (harmonicCesaroNumerator_nonneg X n) (harmonic_succ_pos X).le
  have hs (X : ℕ) : Summable (K X) := by
    apply summable_of_ne_finset_zero (s := Finset.range (X + 1))
    intro n hn
    simp only [K, harmonicCesaroNumerator_support X n hn, zero_div]
  have hm (X : ℕ) : ∑' n, K X n = 1 := by
    rw [tsum_eq_sum (s := Finset.range (X + 1)) (fun n hn => by
      simp only [K, harmonicCesaroNumerator_support X n hn, zero_div])]
    simp only [K, ← Finset.sum_div, harmonicCesaroNumerator_sum,
      div_self (harmonic_succ_pos X).ne']
  have hp (n : ℕ) : Tendsto (fun X => K X n) atTop (𝓝 0) := by
    have h : Tendsto (fun X : ℕ => (1 / (n + 2 : ℝ)) / harmonic (X + 1))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop
          (harmonic_atTop.comp (tendsto_add_atTop_nat 1))
    apply h.congr'
    filter_upwards [eventually_gt_atTop n] with X hX
    simp only [K, harmonicCesaroNumerator, hX, ↓reduceIte]
  have hu := (sourceMean_shift_of_bounded w hw hmean).comp (tendsto_add_atTop_nat 1)
  have h := CollatzCanonical.WeightedKernel.normalized_kernel_tendsto K hK0 hs hm hp hu
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert h using 1
  funext X
  rw [tsum_eq_sum (s := Finset.range (X + 1)) (fun n hn => by
    simp only [K, harmonicCesaroNumerator_support X n hn, zero_div, zero_mul])]
  rw [harmonicCesaro_abel_identity]
  simp only [K, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Function.comp_apply]
  ring

theorem harmonic_div_log_tendsto_one :
    Tendsto (fun X : ℕ => (harmonic X : ℝ) / Real.log X) atTop (𝓝 1) := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun X : ℕ => 1 + 1 / Real.log X) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hlog :
      Tendsto (fun X : ℕ => (1 : ℝ) / Real.log X) atTop (𝓝 0))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hlogpos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
    apply (le_div_iff₀ hlogpos).mpr
    simpa only [one_mul] using
      (Real.log_le_log (by positivity : (0 : ℝ) < X)
        (by exact_mod_cast Nat.le_succ X)).trans (log_add_one_le_harmonic X)
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hlogpos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
    have h := div_le_div_of_nonneg_right (harmonic_le_one_add_log X) hlogpos.le
    simpa only [add_div, div_self hlogpos.ne', add_comm] using h

theorem logarithmicSourceMean_of_sourceMean (w : ℕ → ℝ) {C L : ℝ}
    (hw : ∀ q, |w q| ≤ C) (hmean : Tendsto (sourceMean w) atTop (𝓝 L)) :
    Tendsto (logarithmicSourceMean w) atTop (𝓝 L) := by
  have h := (harmonic_weighted_sourceMean w hw hmean).mul harmonic_div_log_tendsto_one
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hpos : (0 : ℝ) < harmonic X := by
    obtain ⟨Y, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : X ≠ 0)
    exact harmonic_succ_pos Y
  dsimp only [logarithmicSourceMean]
  field_simp

#print axioms logarithmicSourceMean_of_sourceMean

end
end CollatzCanonical.PeriodicCensusFloor
