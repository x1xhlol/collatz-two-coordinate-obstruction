import NaturalVectorTransport
import ClosedVectorWindowMean
import NaturalVectorMeans

open Filter
open scoped Topology BigOperators

namespace CollatzCanonical.LabelLaw
open Erdos1135 CollatzClockAudit CollatzCanonical.BanachWindow
open CollatzCanonical.NaturalPrefix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem natural_vector_mean_eq_native (F : ℕ → V) (y : ℝ)
    (hwindow : (ND.oddBlock y).Nonempty) :
    naturalOddVectorBlockMean F y =
      pmfMeanV (ND.uniformOddBlockPMF y hwindow) (fun q => F q.1) := by
  classical
  unfold naturalOddVectorBlockMean finiteVectorMean pmfMeanV finiteMeanV
  have hvalue (q : {n : ℕ // n ∈ ND.oddBlock y}) :
      ((ND.uniformOddBlockPMF y hwindow) q).toReal = ((ND.oddBlock y).card : ℝ)⁻¹ := by
    simp [ND.uniformOddBlockPMF, ND.uniformFinsetPMF, PMF.uniformOfFintype_apply,
      Fintype.card_coe]
  simp_rw [hvalue]
  rw [← Finset.smul_sum]
  congr 1
  exact (Finset.sum_coe_sort _ F).symm

theorem native_branch_log_vector_expectation (F : ℕ → V) {x : ℝ} (hx : 1 ≤ x)
    (hmass : 0 < Tao.logFinsetMass (ND.oddBlock (ND.transportSourceY x .alpha))) :
    pmfMeanV (ND.logOddBlockPMF (ND.transportSourceY x .alpha) hmass)
      (fun q => F q.1) = closedOddVectorExpectation F
        (Tao.taoAlpha * Real.log x) (Tao.taoAlpha * (Tao.taoAlpha * Real.log x)) := by
  exact (native_iterated_power_window_vector_expectation F
    (a := Tao.taoAlpha) (d := Tao.taoAlpha) hx Tao.taoAlpha_pos.le hmass).trans
      (by rw [mul_assoc])

theorem natural_vector_block_limit_of_comparison {F : ℕ → V} {p : V} {error : ℝ → ℝ}
    (hF : ∀ q, ‖F q‖ ≤ 1)
    (hmean : Tendsto (fun t => t⁻¹ • oddVectorCumulative F t) atTop (𝓝 p))
    (herror : Tendsto error atTop (𝓝 0))
    (hcompare : ∀ᶠ x : ℝ in atTop, ∀ _hx : 1 ≤ x,
      ∃ hwindow : (ND.oddBlock (ND.transportSourceY x .alpha)).Nonempty,
      ∃ hmass : 0 < Tao.logFinsetMass (ND.oddBlock (ND.transportSourceY x .alpha)),
      ‖pmfMeanV (ND.uniformOddBlockPMF (ND.transportSourceY x .alpha) hwindow)
          (fun q => F q.1) -
        pmfMeanV (ND.logOddBlockPMF (ND.transportSourceY x .alpha) hmass)
          (fun q => F q.1)‖ ≤ error x) :
    Tendsto (naturalOddVectorBlockMean F) atTop (𝓝 ((2:ℝ) • p)) := by
  have hclosed : Tendsto (fun x => closedOddVectorExpectation F
      (Tao.taoAlpha * Real.log x) (Tao.taoAlpha * (Tao.taoAlpha * Real.log x)))
      atTop (𝓝 ((2:ℝ) • p)) :=
    (closed_vector_window_mean_limit hF Tao.taoAlpha_one_lt hmean).comp
      (Real.tendsto_log_atTop.const_mul_atTop Tao.taoAlpha_pos)
  have hz : Tendsto (fun x => naturalOddVectorBlockMean F (ND.transportSourceY x .alpha) -
      closedOddVectorExpectation F (Tao.taoAlpha * Real.log x)
        (Tao.taoAlpha * (Tao.taoAlpha * Real.log x))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ herror
    filter_upwards [hcompare, eventually_ge_atTop (1:ℝ)] with x hcompare hx
    obtain ⟨hwindow, hmass, hbound⟩ := hcompare hx
    rw [natural_vector_mean_eq_native F _ hwindow,
      ← native_branch_log_vector_expectation F hx hmass]
    exact hbound
  have hsource : Tendsto (fun x => naturalOddVectorBlockMean F (ND.transportSourceY x .alpha))
      atTop (𝓝 ((2:ℝ) • p)) := by
    simpa only [sub_add_cancel, zero_add] using hz.add hclosed
  have hinverse : Tendsto (fun y : ℝ => y ^ (1 / Tao.taoAlpha)) atTop atTop :=
    tendsto_rpow_atTop (one_div_pos.mpr Tao.taoAlpha_pos)
  apply (hsource.comp hinverse).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
  dsimp only [Function.comp_def, ND.transportSourceY, ND.alpha]
  change naturalOddVectorBlockMean F ((y ^ (1 / Tao.taoAlpha)) ^ Tao.taoAlpha) =
    naturalOddVectorBlockMean F y
  rw [← Real.rpow_mul hy, one_div_mul_cancel Tao.taoAlpha_pos.ne', Real.rpow_one]

theorem actual_invariant_natural_vector_block_limit (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (hpass : EventuallyPassageInvariant F) (p : V)
    (hmean : Tendsto (fun t => t⁻¹ • oddVectorCumulative F t) atTop (𝓝 p)) :
    Tendsto (naturalOddVectorBlockMean F) atTop (𝓝 ((2:ℝ) • p)) := by
  obtain ⟨C, c, _, hc, hcompare⟩ := eventually_natural_vector_comparison F hF hpass
  apply natural_vector_block_limit_of_comparison hF hmean
    (natural_vector_comparison_error_tendsto_zero (C := C) hc)
  filter_upwards [hcompare] with x hx
  exact fun hx1 => hx hx1 .alpha

theorem actual_invariant_odd_and_natural_vector_mean [CompleteSpace V] (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (hpass : EventuallyPassageInvariant F) :
    ∃ p : V, Tendsto (fun t => t⁻¹ • oddVectorCumulative F t) atTop (𝓝 p) ∧
      Tendsto (naturalOddVectorBlockMean F) atTop (𝓝 ((2:ℝ) • p)) := by
  obtain ⟨p, hp⟩ := actual_invariant_odd_vector_mean_exists F hF hpass
  exact ⟨p, hp, actual_invariant_natural_vector_block_limit F hF hpass p hp⟩

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.natural_vector_mean_eq_native
#print axioms CollatzCanonical.LabelLaw.natural_vector_block_limit_of_comparison
#print axioms CollatzCanonical.LabelLaw.actual_invariant_natural_vector_block_limit
#print axioms CollatzCanonical.LabelLaw.actual_invariant_odd_and_natural_vector_mean
