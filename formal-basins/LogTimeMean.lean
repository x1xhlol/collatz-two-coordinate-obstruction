import TwoScaleAveraging
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

open Filter Set
open scoped Topology

namespace CollatzCanonical.TwoScale

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def logarithmicMean (A : ℝ → V) (u : ℝ) : V :=
  Real.exp (-u) • A (Real.exp u)

noncomputable def windowMean (A : ℝ → V) (a t : ℝ) : V :=
  ((a - 1) * t)⁻¹ • (A (a * t) - A t)

/-- Linear growth of a primitive bounds its mean in logarithmic time. -/
theorem logarithmicMean_bound (A : ℝ → V) (U L C : ℝ)
    (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hgrowth : ∀ t, Real.exp U ≤ t → ‖A t‖ ≤ L * t + C) :
    ∀ u, U ≤ u → ‖logarithmicMean A u‖ ≤ L + C := by
  intro u hu
  have harg : Real.exp U ≤ Real.exp u := Real.exp_le_exp.mpr hu
  have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hprod : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  calc
    ‖logarithmicMean A u‖ = Real.exp (-u) * ‖A (Real.exp u)‖ := by
      simp only [logarithmicMean, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-u) * (L * Real.exp u + C) :=
      mul_le_mul_of_nonneg_left (hgrowth _ harg) (Real.exp_pos _).le
    _ = L + Real.exp (-u) * C := by
      calc
        _ = L * (Real.exp (-u) * Real.exp u) + Real.exp (-u) * C := by ring
        _ = _ := by rw [hprod, mul_one]
    _ ≤ L + C := by nlinarith

/-- A bounded additive error in the primitive becomes a vanishing error in its logarithmic modulus. -/
theorem logarithmicMean_modulus_of_le (A : ℝ → V) (U L C : ℝ)
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hgrowth : ∀ t, Real.exp U ≤ t → ‖A t‖ ≤ L * t + C)
    (hincr : ∀ t z, Real.exp U ≤ t → 0 ≤ z → ‖A (t + z) - A t‖ ≤ L * z + C) :
    ∀ u v, U ≤ u → u ≤ v →
      ‖logarithmicMean A v - logarithmicMean A u‖ ≤
        (2 * L + C) * (v - u) + C * Real.exp (-u) := by
  intro u v hu huv
  let r := Real.exp (u - v)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr huv)
  have hrlin : 1 - r ≤ v - u := by
    have := Real.add_one_le_exp (u - v)
    dsimp [r]
    linarith
  have heuv : Real.exp (-v) * Real.exp u = r := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hev : Real.exp (-v) * Real.exp v = 1 := by rw [← Real.exp_add]; simp
  have hevu : r * Real.exp (-u) = Real.exp (-v) := by
    dsimp [r]
    rw [← Real.exp_add]
    congr 1
    ring
  have hemon : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (neg_le_neg huv)
  have hinc := hincr (Real.exp u) (Real.exp v - Real.exp u)
    (Real.exp_le_exp.mpr hu) (sub_nonneg.mpr (Real.exp_le_exp.mpr huv))
  rw [add_sub_cancel] at hinc
  have hB := logarithmicMean_bound A U L C hU hC hgrowth u hu
  have he : logarithmicMean A v - logarithmicMean A u =
      Real.exp (-v) • (A (Real.exp v) - A (Real.exp u)) +
        (r - 1) • logarithmicMean A u := by
    dsimp [logarithmicMean]
    rw [smul_smul, sub_mul, hevu, one_mul]
    module
  have habs : |r - 1| = 1 - r := abs_of_nonpos (sub_nonpos.mpr hr1) |>.trans (by ring)
  calc
    ‖logarithmicMean A v - logarithmicMean A u‖ ≤
        ‖Real.exp (-v) • (A (Real.exp v) - A (Real.exp u))‖ +
          ‖(r - 1) • logarithmicMean A u‖ := by rw [he]; exact norm_add_le _ _
    _ = Real.exp (-v) * ‖A (Real.exp v) - A (Real.exp u)‖ +
        (1 - r) * ‖logarithmicMean A u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), habs]
    _ ≤ Real.exp (-v) * (L * (Real.exp v - Real.exp u) + C) +
        (1 - r) * (L + C) := add_le_add
      (mul_le_mul_of_nonneg_left hinc (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hr1))
    _ = (2 * L + C) * (1 - r) + C * Real.exp (-v) := by
      nlinarith [hev, heuv]
    _ ≤ (2 * L + C) * (v - u) + C * Real.exp (-u) := add_le_add
      (mul_le_mul_of_nonneg_left hrlin (by positivity))
      (mul_le_mul_of_nonneg_left hemon hC)

/-- Symmetric form of the logarithmic modulus. -/
theorem logarithmicMean_modulus (A : ℝ → V) (U L C : ℝ)
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hgrowth : ∀ t, Real.exp U ≤ t → ‖A t‖ ≤ L * t + C)
    (hincr : ∀ t z, Real.exp U ≤ t → 0 ≤ z → ‖A (t + z) - A t‖ ≤ L * z + C) :
    ∀ u v, U ≤ u → U ≤ v →
      ‖logarithmicMean A u - logarithmicMean A v‖ ≤
        (2 * L + C) * |u - v| + C * Real.exp (-min u v) := by
  intro u v hu hv
  rcases le_total u v with huv | hvu
  · have hb := logarithmicMean_modulus_of_le A U L C hU hL hC hgrowth hincr u v hu huv
    rw [norm_sub_rev, min_eq_left huv, abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using hb
  · have hb := logarithmicMean_modulus_of_le A U L C hU hL hC hgrowth hincr v u hv hvu
    simpa only [min_eq_right hvu, abs_of_nonneg (sub_nonneg.mpr hvu)] using hb

/-- The first moving-window average satisfies the exact stable translation relation. -/
theorem logarithmicMean_stable_link (A : ℝ → V) (a : ℝ) (ha : 1 < a) (u : ℝ) :
    logarithmicMean A (u + Real.log a) =
      a⁻¹ • logarithmicMean A u + (1 - a⁻¹) • windowMean A a (Real.exp u) := by
  have ha0 : 0 < a := by linarith
  have ha1 : a - 1 ≠ 0 := by linarith
  have he : Real.exp (u + Real.log a) = a * Real.exp u := by
    rw [Real.exp_add, Real.exp_log ha0, mul_comm]
  have he' : Real.exp (-(u + Real.log a)) = (a * Real.exp u)⁻¹ := by
    rw [Real.exp_neg, he]
  dsimp [logarithmicMean, windowMean]
  rw [he, he', Real.exp_neg]
  match_scalars
  all_goals field_simp [ha0.ne', ha1, (Real.exp_pos u).ne']
  all_goals ring

/-- The second moving-window discrepancy is exactly the logarithmic second-scale residual. -/
theorem logarithmicMean_second_residual (A : ℝ → V) (b : ℝ) (hb : 1 < b) (u : ℝ) :
    b • logarithmicMean A (u + 2 * Real.log b) -
      (b + 1) • logarithmicMean A (u + Real.log b) + logarithmicMean A u =
      (b - 1) • (windowMean A b (b * Real.exp u) - windowMean A b (Real.exp u)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  have he1 : Real.exp (u + Real.log b) = b * Real.exp u := by
    rw [Real.exp_add, Real.exp_log hb0, mul_comm]
  have he2 : Real.exp (u + 2 * Real.log b) = b * (b * Real.exp u) := by
    have harg : u + 2 * Real.log b = (u + Real.log b) + Real.log b := by ring
    rw [harg, Real.exp_add, Real.exp_log hb0, he1]
    ring
  dsimp [logarithmicMean, windowMean]
  rw [Real.exp_neg, Real.exp_neg, Real.exp_neg, he1, he2]
  match_scalars
  all_goals field_simp [hb0.ne', hb1, (Real.exp_pos u).ne']
  all_goals ring

/-- A moving-window power saving becomes exponential decay in logarithmic time. -/
theorem logarithmicMean_first_residual (A : ℝ → V) (a U C c : ℝ) (ha : 1 < a)
    (hfirst : ∀ t, Real.exp U ≤ t →
      ‖windowMean A a (a * t) - windowMean A a t‖ ≤ C * t ^ (-c)) :
    ∀ u, U ≤ u →
      ‖windowMean A a (Real.exp (u + Real.log a)) - windowMean A a (Real.exp u)‖ ≤
        C * Real.exp (-c * u) := by
  intro u hu
  have ha0 : 0 < a := by linarith
  have hb := hfirst (Real.exp u) (Real.exp_le_exp.mpr hu)
  rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp] at hb
  rw [Real.exp_add, Real.exp_log ha0, mul_comm (Real.exp u) a]
  simpa only [mul_comm u (-c)] using hb

/-- The exponential change of variables recovers the original normalized primitive. -/
theorem logarithmicMean_log (A : ℝ → V) (t : ℝ) (ht : 0 < t) :
    logarithmicMean A (Real.log t) = t⁻¹ • A t := by
  simp only [logarithmicMean, Real.exp_neg, Real.exp_log ht]

/-- Two moving-window scale estimates imply norm convergence, with every subcritical power rate.
The estimates for the two scales are independent, explicit hypotheses. -/
theorem two_scale_averaging [CompleteSpace V]
    (A : ℝ → V) (a b T L C C₁ c : ℝ)
    (ha : 1 < a) (hb : 1 < b) (hT : 0 < T)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hc : 0 < c)
    (hirr : Irrational (Real.log a / Real.log b))
    (hgrowth : ∀ t, T ≤ t → ‖A t‖ ≤ L * t + C)
    (hincr : ∀ t z, T ≤ t → 0 ≤ z → ‖A (t + z) - A t‖ ≤ L * z + C)
    (hfirst : ∀ t, T ≤ t →
      ‖windowMean A a (a * t) - windowMean A a t‖ ≤ C₁ * t ^ (-c))
    (hsecond : Tendsto
      (fun t => windowMean A b (b * t) - windowMean A b t) atTop (𝓝 0)) :
    ∃ p : V, Tendsto (fun t : ℝ => t⁻¹ • A t) atTop (𝓝 p) ∧
      ∀ η : ℝ, 0 < η → η < min c 1 →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t : ℝ in atTop,
          ‖t⁻¹ • A t - p‖ ≤ K * t ^ (-η) := by
  let U := max 0 (Real.log T)
  have hU : 0 ≤ U := le_max_left _ _
  have hTU : T ≤ Real.exp U := by
    rw [← Real.exp_log hT]
    exact Real.exp_le_exp.mpr (le_max_right _ _)
  have ha0 : 0 < a := by linarith
  have hd : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hd1 : a⁻¹ < 1 := (inv_lt_one₀ ha0).mpr ha
  have hlog : 0 < Real.log a := Real.log_pos ha
  have hgrowth' : ∀ t, Real.exp U ≤ t → ‖A t‖ ≤ L * t + C :=
    fun t ht => hgrowth t (hTU.trans ht)
  have hincr' : ∀ t z, Real.exp U ≤ t → 0 ≤ z → ‖A (t + z) - A t‖ ≤ L * z + C :=
    fun t z ht hz => hincr t z (hTU.trans ht) hz
  have hfirst' : ∀ t, Real.exp U ≤ t →
      ‖windowMean A a (a * t) - windowMean A a t‖ ≤ C₁ * t ^ (-c) :=
    fun t ht => hfirst t (hTU.trans ht)
  have hsecond' : Tendsto
      (fun u => b • logarithmicMean A (u + 2 * Real.log b) -
        (b + 1) • logarithmicMean A (u + Real.log b) + logarithmicMean A u)
      atTop (𝓝 0) := by
    have ht := (hsecond.comp Real.tendsto_exp_atTop).const_smul (b - 1)
    simp only [smul_zero] at ht
    apply ht.congr'
    exact Eventually.of_forall (fun u => (logarithmicMean_second_residual A b hb u).symm)
  obtain ⟨p, hp, hrate⟩ := exists_limit_of_eventual_two_scale_residuals
    (logarithmicMean A) (fun u => windowMean A a (Real.exp u))
    a⁻¹ (Real.log a) b (Real.log b) C₁ c (L + C) (2 * L + C) C U
    hd hd1 hlog hb hc hC₁ (by positivity) hC hirr
    (logarithmicMean_bound A U L C hU hC hgrowth')
    (logarithmicMean_modulus A U L C hU hL hC hgrowth' hincr')
    (fun u _ => logarithmicMean_stable_link A a ha u)
    (logarithmicMean_first_residual A a U C₁ c ha hfirst') hsecond'
  refine ⟨p, ?_, ?_⟩
  · apply (hp.comp Real.tendsto_log_atTop).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact logarithmicMean_log A t (by linarith)
  · intro η hη hηbound
    have hηc : η ≤ c := (hηbound.trans_le (min_le_left _ _)).le
    have hη1 : η < 1 := hηbound.trans_le (min_le_right _ _)
    have hdη : a⁻¹ < Real.exp (-η * Real.log a) := by
      have he : a⁻¹ = Real.exp (-Real.log a) := by rw [Real.exp_neg, Real.exp_log ha0]
      rw [he, Real.exp_lt_exp]
      nlinarith
    obtain ⟨K, hK, hKb⟩ := hrate η hη hηc hdη
    refine ⟨K, hK, ?_⟩
    have hKt := Real.tendsto_log_atTop.eventually hKb
    filter_upwards [hKt, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    have ht0 : 0 < t := by linarith
    rw [logarithmicMean_log A t ht0] at ht
    rw [Real.rpow_def_of_pos ht0]
    simpa only [mul_comm (Real.log t) (-η)] using ht

end CollatzCanonical.TwoScale
