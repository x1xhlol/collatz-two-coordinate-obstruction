import OddHarmonicCumulative
import LogTimeMean

set_option autoImplicit false

open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

noncomputable def oddWindowMass (s t : ℝ) : ℝ :=
  oddLogarithmicCumulative (fun _ => 1) t - oddLogarithmicCumulative (fun _ => 1) s

noncomputable def oddWindowNumerator (w : ℕ → ℝ) (s t : ℝ) : ℝ :=
  oddLogarithmicCumulative w t - oddLogarithmicCumulative w s

noncomputable def oddWindowExpectation (w : ℕ → ℝ) (s t : ℝ) : ℝ :=
  oddWindowNumerator w s t / oddWindowMass s t

theorem oddWindowNumerator_bounds {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t : ℝ} (hst : s ≤ t) :
    0 ≤ oddWindowNumerator w s t ∧ oddWindowNumerator w s t ≤ oddWindowMass s t := by
  have hmon := logarithmicCumulative_monotone
    (w := fun n => if n % 2 = 1 then w n else 0)
    (fun n => by dsimp only; split_ifs <;> simp [hw0]) hst
  have hcomp := logarithmicCumulative_monotone
    (w := fun n => if n % 2 = 1 then 1 - w n else 0)
    (fun n => by dsimp only; split_ifs <;> simp [sub_nonneg.mpr (hw1 n)]) hst
  have he (u : ℝ) :
      logarithmicCumulative (fun n => if n % 2 = 1 then 1 - w n else 0) u =
        oddLogarithmicCumulative (fun _ => 1) u - oddLogarithmicCumulative w u := by
    unfold oddLogarithmicCumulative logarithmicCumulative
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only
    split_ifs <;> simp [sub_div]
  rw [he, he] at hcomp
  change 0 ≤ logarithmicCumulative _ t - logarithmicCumulative _ s ∧ _
  exact ⟨sub_nonneg.mpr hmon, by unfold oddWindowNumerator oddWindowMass; linarith⟩

theorem oddWindowMass_pos {s t : ℝ} (hs : Real.log 2 ≤ s) (hwidth : 8 < t - s) :
    0 < oddWindowMass s t := by
  have ht : Real.log 2 ≤ t := by linarith
  have h := (abs_le.mp (odd_harmonic_window_mass_bound hs ht)).1
  change 0 < oddLogarithmicCumulative (fun _ => 1) t -
    oddLogarithmicCumulative (fun _ => 1) s
  linarith

theorem oddWindowExpectation_bounds {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t : ℝ}
    (hst : s ≤ t) (hmass : 0 < oddWindowMass s t) :
    0 ≤ oddWindowExpectation w s t ∧ oddWindowExpectation w s t ≤ 1 := by
  have hB := oddWindowNumerator_bounds hw0 hw1 hst
  exact ⟨div_nonneg hB.1 hmass.le, (div_le_one hmass).mpr hB.2⟩

theorem harmonic_normalization_error {B H L E : ℝ} (hB0 : 0 ≤ B) (hBH : B ≤ H)
    (hH : 0 < H) (hL : 0 < L) (herror : |H - L / 2| ≤ E) :
    |B / L - (B / H) / 2| ≤ E / L := by
  have hratio0 : 0 ≤ B / H := div_nonneg hB0 hH.le
  have hratio1 : B / H ≤ 1 := (div_le_one hH).mpr hBH
  have he : B / L - (B / H) / 2 = (B / H) * (H - L / 2) / L := by
    field_simp
  rw [he, abs_div, abs_mul, abs_of_nonneg hratio0, abs_of_pos hL]
  apply div_le_div_of_nonneg_right _ hL.le
  exact (mul_le_mul hratio1 herror (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- Normalized odd-window expectations differ from twice the unnormalized
moving-window means by only O(1 / window length). -/
theorem oddWindowExpectation_normalization {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t : ℝ}
    (hs : Real.log 2 ≤ s) (hst : s < t) (hmass : 0 < oddWindowMass s t) :
    |oddWindowNumerator w s t / (t - s) - oddWindowExpectation w s t / 2| ≤
      4 / (t - s) := by
  have hB := oddWindowNumerator_bounds hw0 hw1 hst.le
  exact harmonic_normalization_error hB.1 hB.2 hmass (sub_pos.mpr hst)
    (odd_harmonic_window_mass_bound hs (hs.trans hst.le))


theorem oddWindowNumerator_div_eq_windowMean (w : ℕ → ℝ) (a t : ℝ) :
    oddWindowNumerator w t (a * t) / (a * t - t) =
      CollatzCanonical.TwoScale.windowMean (oddLogarithmicCumulative w) a t := by
  unfold oddWindowNumerator CollatzCanonical.TwoScale.windowMean
  rw [show a * t - t = (a - 1) * t by ring]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

theorem oddWindow_normalized_comparison {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t u v : ℝ}
    (hs : Real.log 2 ≤ s) (hu : Real.log 2 ≤ u) (hst : s < t) (huv : u < v)
    (hmassST : 0 < oddWindowMass s t) (hmassUV : 0 < oddWindowMass u v) :
    |oddWindowNumerator w s t / (t - s) - oddWindowNumerator w u v / (v - u)| ≤
      |oddWindowExpectation w s t - oddWindowExpectation w u v| / 2 +
        4 / (t - s) + 4 / (v - u) := by
  have hST := oddWindowExpectation_normalization hw0 hw1 hs hst hmassST
  have hUV := oddWindowExpectation_normalization hw0 hw1 hu huv hmassUV
  have htri₁ := abs_sub_le (oddWindowNumerator w s t / (t - s))
    (oddWindowExpectation w s t / 2) (oddWindowNumerator w u v / (v - u))
  have htri₂ := abs_sub_le (oddWindowExpectation w s t / 2)
    (oddWindowExpectation w u v / 2) (oddWindowNumerator w u v / (v - u))
  rw [abs_sub_comm (oddWindowExpectation w u v / 2)
    (oddWindowNumerator w u v / (v - u))] at htri₂
  have he : |oddWindowExpectation w s t / 2 - oddWindowExpectation w u v / 2| =
      |oddWindowExpectation w s t - oddWindowExpectation w u v| / 2 := by
    rw [← sub_div, abs_div]
    norm_num
  rw [he] at htri₂
  linarith


theorem odd_windowMean_discrepancy_bound {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {a t : ℝ}
    (ha : 1 < a) (ht : 0 < t) (hlog : Real.log 2 ≤ t)
    (hmass₁ : 0 < oddWindowMass t (a * t))
    (hmass₂ : 0 < oddWindowMass (a * t) (a * (a * t))) :
    |CollatzCanonical.TwoScale.windowMean (oddLogarithmicCumulative w) a (a * t) -
      CollatzCanonical.TwoScale.windowMean (oddLogarithmicCumulative w) a t| ≤
      |oddWindowExpectation w (a * t) (a * (a * t)) - oddWindowExpectation w t (a * t)| / 2 +
        8 / ((a - 1) * t) := by
  have ha0 : 0 < a := by linarith
  have hat : t < a * t := by nlinarith
  have haat : a * t < a * (a * t) := mul_lt_mul_of_pos_left hat ha0
  have hL : 0 < a * t - t := sub_pos.mpr hat
  have hden : a * t - t ≤ a * (a * t) - a * t := by
    have hh := mul_le_mul_of_nonneg_right ha.le hL.le
    nlinarith
  have hdiv : 4 / (a * (a * t) - a * t) ≤ 4 / (a * t - t) :=
    div_le_div_of_nonneg_left (by norm_num) hL hden
  have hh := oddWindow_normalized_comparison hw0 hw1 (hlog.trans hat.le) hlog
    haat hat hmass₂ hmass₁
  rw [oddWindowNumerator_div_eq_windowMean w a (a * t),
    oddWindowNumerator_div_eq_windowMean w a t] at hh
  have he : 4 / (a * t - t) + 4 / (a * t - t) = 8 / ((a - 1) * t) := by
    rw [show a * t - t = (a - 1) * t by ring]
    ring
  linarith

#print axioms oddWindowNumerator_bounds
#print axioms oddWindowMass_pos
#print axioms harmonic_normalization_error
#print axioms oddWindowExpectation_normalization
#print axioms oddWindow_normalized_comparison
#print axioms odd_windowMean_discrepancy_bound

end CollatzCanonical.DirichletAbelian
