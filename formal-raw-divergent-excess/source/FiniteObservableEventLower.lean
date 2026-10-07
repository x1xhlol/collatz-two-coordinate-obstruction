import FiniteOccupationSourceMean
import NativeOddEventDensity
import ClosedWindowMeanLimit

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation.DivergentExcess
open Erdos1135.Tao CollatzCanonical.DirichletAbelian CollatzCanonical.NativeTao

private theorem odd_cumulative_mono {f g : ℕ → ℝ}
    (hfg : ∀ q, Odd q → f q ≤ g q) (t : ℝ) :
    oddLogarithmicCumulative f t ≤ oddLogarithmicCumulative g t := by
  unfold oddLogarithmicCumulative logarithmicCumulative
  apply Finset.sum_le_sum
  intro q hq
  by_cases ho : (q + 1) % 2 = 1
  · simp only [if_pos ho]
    exact div_le_div_of_nonneg_right (hfg _ (Nat.odd_iff.mpr ho)) (by positivity)
  · simp only [if_neg ho, zero_div, le_refl]

private theorem odd_cumulative_const_mul (c : ℝ) (f : ℕ → ℝ) (t : ℝ) :
    oddLogarithmicCumulative (fun q => c * f q) t =
      c * oddLogarithmicCumulative f t := by
  unfold oddLogarithmicCumulative logarithmicCumulative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  split_ifs <;> ring

private theorem odd_cumulative_add (f g : ℕ → ℝ) (t : ℝ) :
    oddLogarithmicCumulative (fun q => f q + g q) t =
      oddLogarithmicCumulative f t + oddLogarithmicCumulative g t := by
  unfold oddLogarithmicCumulative logarithmicCumulative
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  split_ifs <;> ring

private theorem odd_cumulative_sum (s : Finset ℕ) (f : ℕ → ℕ → ℝ) (t : ℝ) :
    oddLogarithmicCumulative (fun q => ∑ i ∈ s, f i q) t =
      ∑ i ∈ s, oddLogarithmicCumulative (f i) t := by
  unfold oddLogarithmicCumulative logarithmicCumulative
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  split_ifs <;> simp [Finset.sum_div]

theorem observable_plus_bad_event_bound (s : Finset ℕ) (G : ℕ → Set TaoOddNat)
    {L : ℝ} (f : ℕ → ℝ) (hf : ∀ q : TaoOddNat, 0 ≤ f q.1) (hL : 0 ≤ L)
    (hgood : ∀ q : TaoOddNat, (∀ i ∈ s, q ∈ G i) → L ≤ f q.1)
    (q : TaoOddNat) :
    L ≤ f q.1 + L * ∑ i ∈ s, oddEventWeight (G i)ᶜ q.1 := by
  classical
  have hnonneg : 0 ≤ ∑ i ∈ s, oddEventWeight (G i)ᶜ q.1 :=
    Finset.sum_nonneg (fun i _ => (oddEventWeight_bounds _ _).1)
  by_cases hq : ∀ i ∈ s, q ∈ G i
  · exact (hgood q hq).trans (le_add_of_nonneg_right (mul_nonneg hL hnonneg))
  · push Not at hq
    obtain ⟨i, hi, hbad⟩ := hq
    have hone : oddEventWeight (G i)ᶜ q.1 = 1 := by
      rw [oddEventWeight_of_odd]
      simp [hbad]
    have hsum : 1 ≤ ∑ i ∈ s, oddEventWeight (G i)ᶜ q.1 := by
      rw [← hone]
      exact Finset.single_le_sum (f := fun j => oddEventWeight (G j)ᶜ q.1)
        (fun j _ => (oddEventWeight_bounds (G j)ᶜ q.1).1) hi
    have hm := mul_le_mul_of_nonneg_left hsum hL
    have ho := hf q
    linarith

theorem observable_cumulative_lower_with_bad_events (s : Finset ℕ)
    (G : ℕ → Set TaoOddNat) {L : ℝ} (f : ℕ → ℝ) (hf : ∀ q : TaoOddNat, 0 ≤ f q.1) (hL : 0 ≤ L)
    (hgood : ∀ q : TaoOddNat, (∀ i ∈ s, q ∈ G i) → L ≤ f q.1)
    (t : ℝ) :
    L * oddLogarithmicCumulative (fun _ => 1) t ≤
      oddLogarithmicCumulative f t +
        L * ∑ i ∈ s, oddLogarithmicCumulative (oddEventWeight (G i)ᶜ) t := by
  have h := odd_cumulative_mono (f := fun _ => L * 1)
    (g := fun q => f q + L * ∑ i ∈ s, oddEventWeight (G i)ᶜ q)
    (fun q hq => by simpa only [mul_one] using
      observable_plus_bad_event_bound s G f hf hL hgood (⟨q, hq⟩ : TaoOddNat)) t
  simpa only [odd_cumulative_const_mul, odd_cumulative_add, odd_cumulative_sum] using h

/-- Finite bad-event envelopes on the same arbitrary source cutoff give an
lower bound for its actual normalized source mean. No event mean or independence is used. -/
theorem finite_observable_mean_lower_of_bad_envelopes (s : Finset ℕ)
    (G : ℕ → Set TaoOddNat) (d : ℕ → ℝ) {L : ℝ} (f : ℕ → ℝ) (hf : ∀ q : TaoOddNat, 0 ≤ f q.1) (hL : 0 ≤ L)
    (hgood : ∀ q : TaoOddNat, (∀ i ∈ s, q ∈ G i) → L ≤ f q.1)
    {A : ℝ} (hmean : Tendsto (fun t : ℝ => 2 * oddLogarithmicCumulative f t / t)
      atTop (𝓝 A))
    (hbad : ∀ i ∈ s, ∃ C : ℝ, ∀ᶠ t : ℝ in atTop,
      oddLogarithmicCumulative (oddEventWeight (G i)ᶜ) t ≤ C + d i * t) :
    L * (1 - 2 * ∑ i ∈ s, d i) ≤ A := by
  classical
  choose C hC using fun i : s => hbad i.1 i.2
  let Csum : ℝ := ∑ i : s, C i
  have hbadall : ∀ᶠ t : ℝ in atTop,
      (∑ i ∈ s, oddLogarithmicCumulative (oddEventWeight (G i)ᶜ) t) ≤
        Csum + (∑ i ∈ s, d i) * t := by
    have he := Filter.eventually_all.2 hC
    filter_upwards [he] with t ht
    calc
      (∑ i ∈ s, oddLogarithmicCumulative (oddEventWeight (G i)ᶜ) t) =
          ∑ i : s, oddLogarithmicCumulative (oddEventWeight (G i.1)ᶜ) t :=
        (Finset.sum_coe_sort s _).symm
      _ ≤ ∑ i : s, (C i + d i.1 * t) := Finset.sum_le_sum (fun i _ => ht i)
      _ = Csum + (∑ i ∈ s, d i) * t := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_coe_sort]
  have hlimOne := odd_harmonic_mean_limit.const_mul L
  have hlimOcc := hmean.div_const 2
  have hlimError : Tendsto (fun t : ℝ => L * (Csum / t + ∑ i ∈ s, d i))
      atTop (𝓝 (L * ∑ i ∈ s, d i)) := by
    have h := ((tendsto_inv_atTop_zero.const_mul Csum).add_const (∑ i ∈ s, d i)).const_mul L
    simpa only [div_eq_mul_inv, mul_zero, zero_add] using h
  have hlimOcc' : Tendsto (fun t : ℝ => oddLogarithmicCumulative f t / t)
      atTop (𝓝 (A / 2)) := by
    convert hlimOcc using 1
    ext t
    ring
  have hh := le_of_tendsto_of_tendsto hlimOne (hlimOcc'.add hlimError) (show
      ∀ᶠ t : ℝ in atTop,
        L * (oddLogarithmicCumulative (fun _ => 1) t / t) ≤
          oddLogarithmicCumulative f t / t +
            L * (Csum / t + ∑ i ∈ s, d i) from by
    filter_upwards [hbadall, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have ho := observable_cumulative_lower_with_bad_events s G f hf hL hgood t
    have hb := mul_le_mul_of_nonneg_left ht hL
    have hv : L * oddLogarithmicCumulative (fun _ => 1) t ≤
        oddLogarithmicCumulative f t +
          L * (Csum + (∑ i ∈ s, d i) * t) := by linarith
    have hdiv := div_le_div_of_nonneg_right hv ht0.le
    convert hdiv using 1 <;> field_simp)
  nlinarith

#print axioms observable_plus_bad_event_bound
#print axioms observable_cumulative_lower_with_bad_events
#print axioms finite_observable_mean_lower_of_bad_envelopes

end CollatzCanonical.RawOccupation.DivergentExcess
