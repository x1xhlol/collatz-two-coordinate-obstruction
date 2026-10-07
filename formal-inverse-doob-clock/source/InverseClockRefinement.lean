import InverseClockGeometry
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Filter.Finite

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace CollatzCylinderPacking.Arithmetic.InverseDoob.ClockGeometry

theorem tendsto_of_finite_interlacing
    {E : Type*} [TopologicalSpace E] {f : ℕ → E} {v : E} {L : ℕ}
    (hL : 0 < L)
    (h : ∀ r : Fin L, Tendsto (fun j : ℕ => f (L * j + r)) atTop (𝓝 v)) :
    Tendsto f atTop (𝓝 v) := by
  apply tendsto_def.mpr
  intro s hs
  have hall : ∀ᶠ j : ℕ in atTop, ∀ r : Fin L, f (L * j + r) ∈ s :=
    Filter.eventually_all.mpr (fun r => (h r).eventually hs)
  have hdiv : Tendsto (fun j : ℕ => j / L) atTop atTop := by
    rw [Tendsto, Filter.map_div_atTop_eq_nat L hL]
  filter_upwards [hdiv.eventually hall] with j hj
  simpa only [Nat.div_add_mod] using hj ⟨j % L, Nat.mod_lt j hL⟩

noncomputable def refiningRatio (alpha : ℝ) (r : ℕ) : ℝ :=
  alpha ^ (((r + 1 : ℕ) : ℝ)⁻¹)

theorem refiningRatio_one_lt {alpha : ℝ} (ha : 1 < alpha) (r : ℕ) :
    1 < refiningRatio alpha r := by
  apply Real.one_lt_rpow ha
  positivity

theorem refiningRatio_pow {alpha : ℝ} (ha : 0 ≤ alpha) (r : ℕ) :
    refiningRatio alpha r ^ (r + 1) = alpha := by
  exact Real.rpow_inv_natCast_pow ha (by omega)

theorem refiningRatio_tendsto_one {alpha : ℝ} (ha : 0 < alpha) :
    Tendsto (refiningRatio alpha) atTop (𝓝 1) := by
  have hnat : Tendsto (fun r : ℕ => ((r + 1 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) tendsto_natCast_atTop_atTop
    exact_mod_cast Nat.le_succ r
  have hinv := tendsto_inv_atTop_zero.comp hnat
  simpa only [refiningRatio, Real.rpow_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => alpha) atTop (𝓝 alpha)).rpow hinv
      (Or.inl ha.ne')

theorem interlaced_exp_power {alpha : ℝ} (ha : 0 ≤ alpha)
    (b : ℝ) (r l j : ℕ) :
    (Real.exp (b * refiningRatio alpha r ^ l)) ^ (alpha ^ j) =
      Real.exp (b * refiningRatio alpha r ^ ((r + 1) * j + l)) := by
  rw [← Real.exp_mul, pow_add, pow_mul, refiningRatio_pow ha]
  congr 1
  ring

theorem refined_clock_limit_of_reference_limits
    {alpha b q : ℝ} {F : ℝ → ℝ} (ha : 0 ≤ alpha) (r : ℕ)
    (h : ∀ l : Fin (r + 1),
      Tendsto (fun j : ℕ =>
        F ((Real.exp (b * refiningRatio alpha r ^ (l : ℕ))) ^ (alpha ^ j)) /
          Real.log ((Real.exp (b * refiningRatio alpha r ^ (l : ℕ))) ^ (alpha ^ j)))
        atTop (𝓝 q)) :
    Tendsto (fun j : ℕ => F (Real.exp (b * refiningRatio alpha r ^ j)) /
      (b * refiningRatio alpha r ^ j)) atTop (𝓝 q) := by
  apply tendsto_of_finite_interlacing (L := r + 1) (by omega)
  intro l
  simpa only [interlaced_exp_power ha, Real.log_exp] using h l

theorem ae_refined_clock_limits
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {alpha b q : ℝ} {F : Ω → ℝ → ℝ} (ha : 1 < alpha) (hb : 0 < b)
    (href : ∀ M : ℝ, 1 < M → ∀ᵐ ω ∂μ,
      Tendsto (fun j : ℕ => F ω (M ^ (alpha ^ j)) /
        Real.log (M ^ (alpha ^ j))) atTop (𝓝 q)) :
    ∀ᵐ ω ∂μ, ∀ r : ℕ,
      Tendsto (fun j : ℕ => F ω (Real.exp (b * refiningRatio alpha r ^ j)) /
        (b * refiningRatio alpha r ^ j)) atTop (𝓝 q) := by
  have hall : ∀ᵐ ω ∂μ, ∀ r : ℕ, ∀ l : Fin (r + 1),
      Tendsto (fun j : ℕ =>
        F ω ((Real.exp (b * refiningRatio alpha r ^ (l : ℕ))) ^ (alpha ^ j)) /
          Real.log ((Real.exp (b * refiningRatio alpha r ^ (l : ℕ))) ^ (alpha ^ j)))
        atTop (𝓝 q) := by
    rw [ae_all_iff]
    intro r
    rw [ae_all_iff]
    intro l
    apply href
    apply Real.one_lt_exp_iff.mpr
    exact mul_pos hb (pow_pos (zero_lt_one.trans (refiningRatio_one_lt ha r)) _)
  filter_upwards [hall] with ω hω
  intro r
  exact refined_clock_limit_of_reference_limits (zero_le_one.trans ha.le) r (hω r)

theorem ae_height_clock_of_reference_limits
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {alpha b q g : ℝ} {Y : Ω → ℕ → ℕ} {C : Ω → ℝ → ℕ}
    (ha : 1 < alpha) (hb : 0 < b) (hq : 0 < q) (hg : 0 ≤ g)
    (href : ∀ M : ℝ, 1 < M → ∀ᵐ ω ∂μ,
      Tendsto (fun j : ℕ => (C ω (M ^ (alpha ^ j)) : ℝ) /
        Real.log (M ^ (alpha ^ j))) atTop (𝓝 q))
    (hcut : ∀ᵐ ω ∂μ, ∀ r j : ℕ,
      (Y ω (C ω (Real.exp (b * refiningRatio alpha r ^ j))) : ℝ) ≤
        Real.exp (b * refiningRatio alpha r ^ j))
    (hafter : ∀ᵐ ω ∂μ, ∀ r j k : ℕ,
      C ω (Real.exp (b * refiningRatio alpha r ^ j)) < k →
        Real.exp (b * refiningRatio alpha r ^ j) < (Y ω k : ℝ))
    (hback : ∀ᵐ ω ∂μ, ∀ k t : ℕ, k ≤ t →
      Real.log ((Y ω k : ℝ) + 1) ≤ Real.log ((Y ω t : ℝ) + 1) +
        g * ((t - k : ℕ) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => Real.log (Y ω k : ℝ) / (k : ℝ))
      atTop (𝓝 (1 / q)) := by
  have hclocks := ae_refined_clock_limits (F := fun ω R => (C ω R : ℝ)) ha hb href
  filter_upwards [hclocks, hcut, hafter, hback] with ω hω hc haf hba
  exact height_clock_of_refining_last_clock_grids
    (Y := Y ω)
    (sigma := fun r j => C ω (Real.exp (b * refiningRatio alpha r ^ j)))
    (base := fun _ => b) hq hg (refiningRatio_one_lt ha) (fun _ => hb)
    (refiningRatio_tendsto_one (zero_lt_one.trans ha)) hω hc haf hba

#print axioms tendsto_of_finite_interlacing
#print axioms refiningRatio_one_lt
#print axioms refiningRatio_pow
#print axioms refiningRatio_tendsto_one
#print axioms interlaced_exp_power
#print axioms refined_clock_limit_of_reference_limits
#print axioms ae_refined_clock_limits
#print axioms ae_height_clock_of_reference_limits

end CollatzCylinderPacking.Arithmetic.InverseDoob.ClockGeometry
