import WeightedSourceLogMean
import ActualClockAdapter
import ClockExceptionalDensity
import NativeActualClockException

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.IntegerStationaryEnvelope

open CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.DirichletAbelian CollatzCanonical.GreenKernelScalars
open CollatzCanonical.ClockSqueeze CollatzCanonical.NativeTao

noncomputable section

theorem log_floor_exp_div_tendsto_one :
    Tendsto (fun t : ℝ => Real.log (⌊Real.exp t⌋₊ : ℝ) / t) atTop (𝓝 1) := by
  have hnat : Tendsto (fun t : ℝ => ⌊Real.exp t⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  have hratio : Tendsto (fun t : ℝ => (⌊Real.exp t⌋₊ : ℝ) / Real.exp t)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp Real.tendsto_exp_atTop
  have hlog : Tendsto (fun t : ℝ => Real.log ((⌊Real.exp t⌋₊ : ℝ) / Real.exp t))
      atTop (𝓝 0) := by
    simpa only [Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hsmall := hlog.mul (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hlim : Tendsto (fun t : ℝ => 1 +
      Real.log ((⌊Real.exp t⌋₊ : ℝ) / Real.exp t) / t) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero, div_eq_mul_inv] using tendsto_const_nhds.add hsmall
  apply hlim.congr'
  filter_upwards [hnat.eventually (eventually_ge_atTop 1), eventually_gt_atTop (0 : ℝ)] with t ht ht0
  have hf : (⌊Real.exp t⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊Real.exp t⌋₊ ≠ 0 by omega)
  rw [Real.log_div hf (Real.exp_pos t).ne', Real.log_exp]
  field_simp
  ring

theorem logarithmicCumulative_mean_of_nat_mean (w : ℕ → ℝ) {D : ℝ}
    (hmean : Tendsto (logarithmicSourceMean w) atTop (𝓝 D)) :
    Tendsto (fun t : ℝ => logarithmicCumulative w t / t) atTop (𝓝 D) := by
  have hnat : Tendsto (fun t : ℝ => ⌊Real.exp t⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  have hm := (hmean.comp hnat).mul log_floor_exp_div_tendsto_one
  simp only [mul_one] at hm
  apply hm.congr'
  filter_upwards [hnat.eventually (eventually_ge_atTop 2), eventually_gt_atTop (0 : ℝ)] with t ht ht0
  have hf : 1 < (⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast (show 1 < ⌊Real.exp t⌋₊ by omega)
  have hlog : Real.log (⌊Real.exp t⌋₊ : ℝ) ≠ 0 := (Real.log_pos hf).ne'
  dsimp only [Function.comp_def, logarithmicSourceMean, logarithmicCumulative]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

def markedFirstHitPartialSum (K N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑' q, firstHitPartialTerm K N q * f q

theorem markedFirstHitPartialTerm_summable {N : ℕ} (hN : 0 < N) (K : ℕ)
    (f : ℕ → ℝ) {L : ℝ} (hf0 : ∀ q, 0 ≤ f q) (hfL : ∀ q, f q ≤ L) :
    Summable (fun q => firstHitPartialTerm K N q * f q) := by
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (firstHitPartialTerm_nonneg K N q) (hf0 q))
    (fun q => mul_le_mul_of_nonneg_left (hfL q) (firstHitPartialTerm_nonneg K N q))
    ((firstHitPartialTerm_summable hN K).mul_right L)

theorem clockTerm_mono_of_weight_le {w v : ℕ → ℝ} (h : ∀ q, w q ≤ v q)
    (d : ℕ → ℕ) (K q : ℕ) : clockTerm w d K q ≤ clockTerm v d K q := by
  unfold clockTerm
  split_ifs
  · exact div_le_div_of_nonneg_right (h _) (by positivity)
  · exact le_rfl

theorem clockTail_mono_of_weight_le {w v : ℕ → ℝ}
    (hw0 : ∀ q, 0 ≤ w q) (hwv : ∀ q, w q ≤ v q)
    (d : ℕ → ℕ) (K : ℕ) (t : ℝ) (hs : Summable (clockTerm v d K)) :
    clockTail w d K t ≤ clockTail v d K t := by
  have hv0 (q : ℕ) : 0 ≤ v q := (hw0 q).trans (hwv q)
  have ht0 (q : ℕ) : 0 ≤ (if t < Real.log (q + 1 : ℕ) then clockTerm w d K q else 0) := by
    split_ifs
    · exact clockTerm_nonneg hw0 d K q
    · exact le_rfl
  have ht1 (q : ℕ) : (if t < Real.log (q + 1 : ℕ) then clockTerm w d K q else 0) ≤
      clockTerm v d K q := by
    split_ifs
    · exact clockTerm_mono_of_weight_le hwv d K q
    · exact clockTerm_nonneg hv0 d K q
  have hs0 := Summable.of_nonneg_of_le ht0 ht1 hs
  have hs1 : Summable (fun q => if t < Real.log (q + 1 : ℕ) then clockTerm v d K q else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro q
      split_ifs
      · exact clockTerm_nonneg hv0 d K q
      · exact le_rfl
    · intro q
      split_ifs
      · exact le_rfl
      · exact clockTerm_nonneg hv0 d K q
  apply Summable.tsum_le_tsum _ hs0 hs1
  intro q
  split_ifs
  · exact clockTerm_mono_of_weight_le hwv d K q
  · exact le_rfl

theorem clockTerm_mul (w f : ℕ → ℝ) (d : ℕ → ℕ) (K q : ℕ) :
    clockTerm (fun n => w n * f n) d K q = clockTerm w d K q * f (q + 1) := by
  unfold clockTerm
  split_ifs <;> ring

theorem marked_clock_term_eq {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ)
    (hsupport : ∀ q, ¬ (q % 2 = 1 ∧ q % 3 ≠ 0) → f q = 0) (K q : ℕ) :
    clockTerm (fun n => firstHitWeight N n * f n) (firstHitOddDepth N) K q =
      firstHitPartialTerm K N (q + 1) * f (q + 1) / N := by
  have hw : (fun n => firstHitWeight N n * f n) =
      (fun n => oddFirstHitWeight N n * f n) := by
    funext n
    by_cases ho : n % 2 = 1
    · simp only [oddFirstHitWeight, if_pos ho]
    · have hz := hsupport n (fun h => ho h.1)
      simp only [hz, mul_zero]
  rw [hw, clockTerm_mul, actual_clock_term_eq hN]
  ring

theorem marked_clock_tsum {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) {L : ℝ}
    (hf0 : ∀ q, 0 ≤ f q) (hfL : ∀ q, f q ≤ L)
    (hsupport : ∀ q, ¬ (q % 2 = 1 ∧ q % 3 ≠ 0) → f q = 0) (K : ℕ) :
    (∑' q, clockTerm (fun n => firstHitWeight N n * f n) (firstHitOddDepth N) K q) =
      markedFirstHitPartialSum K N f / N := by
  simp only [marked_clock_term_eq hN f hsupport, tsum_div_const]
  have hs := (markedFirstHitPartialTerm_summable hN K f hf0 hfL).tsum_eq_zero_add
  have hz : firstHitPartialTerm K N 0 * f 0 = 0 := by simp [firstHitPartialTerm]
  rw [hz, zero_add] at hs
  exact congrArg (fun x : ℝ => x / N) hs.symm

theorem periodic_marked_firstHit_mean_of_le_one {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (f : ℕ → ℝ) (hp : Function.Periodic f M)
    (hf0 : ∀ q, 0 ≤ f q) (hf1 : ∀ q, f q ≤ 1)
    (hsupport : ∀ q, ¬ (q % 2 = 1 ∧ q % 3 ≠ 0) → f q = 0) :
    Tendsto (fun K : ℕ => markedFirstHitPartialSum K N f / (K : ℝ)) atTop
      (𝓝 (2 * delta * N * actualFirstHitDensity N *
        ((∑ q ∈ Finset.range M, f q) / (M : ℝ)))) := by
  let w : ℕ → ℝ := fun q => firstHitWeight N q * f q
  have hw0 (q : ℕ) : 0 ≤ w q := mul_nonneg (firstHitWeight_bounds N q).1 (hf0 q)
  have hwodd (q : ℕ) : w q ≤ oddFirstHitWeight N q := by
    dsimp only [w]
    by_cases ho : q % 2 = 1
    · rw [oddFirstHitWeight, if_pos ho]
      exact mul_le_of_le_one_right (firstHitWeight_bounds N q).1 (hf1 q)
    · rw [hsupport q (fun h => ho h.1), mul_zero]
      exact (oddFirstHitWeight_bounds N q).1
  have hw1 (q : ℕ) : w q ≤ 1 := (hwodd q).trans (oddFirstHitWeight_bounds N q).2
  have hws (q : ℕ) (hq : ¬ (q % 2 = 1 ∧ ∃ A, iterate A q = N)) : w q = 0 := by
    by_cases ho : q % 2 = 1
    · have hh : ¬ ∃ A, iterate A q = N := fun h => hq ⟨ho, h⟩
      simp [w, firstHitWeight, hh]
    · simp only [w, hsupport q (fun h => ho h.1), mul_zero]
  have hmean : Tendsto (fun t : ℝ => logarithmicCumulative w t / t) atTop
      (𝓝 (actualFirstHitDensity N * ((∑ q ∈ Finset.range M, f q) / (M : ℝ)))) := by
    apply logarithmicCumulative_mean_of_nat_mean
    refine logarithmicSourceMean_of_sourceMean _ (C := 1) ?_
      (actual_firstHitWeight_periodic_sourceMean N f M hM hp)
    intro q
    change |w q| ≤ 1
    rw [abs_of_nonneg (hw0 q)]
    exact hw1 q
  have hs (K : ℕ) : Summable (clockTerm w (firstHitOddDepth N) K) :=
    Summable.of_nonneg_of_le (clockTerm_nonneg hw0 _ K)
      (clockTerm_mono_of_weight_le hwodd _ K) (actual_clock_summable hN K)
  have ht : Tendsto (fun K : ℕ => clockTail w (firstHitOddDepth N) K
      ((6 * Real.log 2) * (K : ℝ) + Real.log N) / (K : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero _ _ (actual_clock_normalized_tail_tendsto_zero hN)
    · intro K
      exact div_nonneg (clockTail_nonneg hw0 _ K _) (Nat.cast_nonneg K)
    · intro K
      exact div_le_div_of_nonneg_right
        (clockTail_mono_of_weight_le hw0 hwodd _ K _ (actual_clock_summable hN K))
        (Nat.cast_nonneg K)
  have hm := weighted_clock_mean_of_exception_density (fun q => ⟨hw0 q, hw1 q⟩)
    (fun q => q % 2 = 1 ∧ ∃ A, iterate A q = N) hws (firstHitOddDepth N)
    (by positivity [delta_pos] : 0 < 2 * delta) (by positivity : 0 < 6 * Real.log 2)
    (Real.log N) hs hmean (fun ε hε _ => actual_firstHitOddDepth_exception_mean_zero N hε) ht
  have hm' := hm.mul_const (N : ℝ)
  convert hm' using 1
  · funext K
    rw [show (∑' q, clockTerm w (firstHitOddDepth N) K q) =
      markedFirstHitPartialSum K N f / N from marked_clock_tsum hN f hf0 hf1 hsupport K]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  · congr 1
    ring

theorem periodic_marked_firstHit_mean {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (f : ℕ → ℝ) (hp : Function.Periodic f M) {L : ℝ} (hL : 0 ≤ L)
    (hf0 : ∀ q, 0 ≤ f q) (hfL : ∀ q, f q ≤ L)
    (hsupport : ∀ q, ¬ (q % 2 = 1 ∧ q % 3 ≠ 0) → f q = 0) :
    Tendsto (fun K : ℕ => markedFirstHitPartialSum K N f / (K : ℝ)) atTop
      (𝓝 (2 * delta * N * actualFirstHitDensity N *
        ((∑ q ∈ Finset.range M, f q) / (M : ℝ)))) := by
  let C : ℝ := L + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  have hp' : Function.Periodic (fun q => f q / C) M := by
    intro q
    change f (q + M) / C = f q / C
    rw [hp q]
  have hfC (q : ℕ) : f q / C ≤ 1 := by
    apply (div_le_one hC).mpr
    dsimp only [C]
    linarith [hfL q]
  have hm := (periodic_marked_firstHit_mean_of_le_one hN hM (fun q => f q / C) hp'
    (fun q => div_nonneg (hf0 q) hC.le) hfC
    (fun q hq => by change f q / C = 0; rw [hsupport q hq, zero_div])).mul_const C
  have hsum (K : ℕ) : markedFirstHitPartialSum K N (fun q => f q / C) =
      markedFirstHitPartialSum K N f / C := by
    unfold markedFirstHitPartialSum
    simp_rw [← mul_div_assoc]
    exact tsum_div_const
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  convert hm using 1
  · funext K
    rw [hsum]
    field_simp
  · congr 1
    rw [← Finset.sum_div]
    field_simp

theorem periodic_marked_firstHit_mean_nonperiodic {N M : ℕ}
    (hN : 0 < N) (hnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r N = N) (hM : 0 < M)
    (f : ℕ → ℝ) (hp : Function.Periodic f M) {L : ℝ} (hL : 0 ≤ L)
    (hf0 : ∀ q, 0 ≤ f q) (hfL : ∀ q, f q ≤ L)
    (hsupport : ∀ q, ¬ (q % 2 = 1 ∧ q % 3 ≠ 0) → f q = 0) :
    Tendsto (fun K : ℕ => markedFirstHitPartialSum K N f / (K : ℝ)) atTop
      (𝓝 (2 * actualDensityValue actualFirstHitDensity N *
        ((∑ q ∈ Finset.range M, f q) / (M : ℝ)))) := by
  have hm := periodic_marked_firstHit_mean hN hM f hp hL hf0 hfL hsupport
  simpa only [actualDensityValue, greenCycleFactor, dif_neg hnp, mul_one, mul_assoc] using hm

#print axioms periodic_marked_firstHit_mean
#print axioms periodic_marked_firstHit_mean_nonperiodic

end
end CollatzCanonical.IntegerStationaryEnvelope
