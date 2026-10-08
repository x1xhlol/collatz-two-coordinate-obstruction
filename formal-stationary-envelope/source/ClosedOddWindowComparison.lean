import OddWindowFiniteProbability

set_option autoImplicit false

open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

/-- Inclusive real window, indexed by n+1 as in the cumulative sum. -/
noncomputable def closedOddWindowNumerator (w : ℕ → ℝ) (s t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico (⌈Real.exp s⌉₊ - 1) ⌊Real.exp t⌋₊,
    (if (n + 1) % 2 = 1 then w (n + 1) else 0) / (n + 1 : ℕ)

noncomputable def closedOddWindowMass (s t : ℝ) : ℝ :=
  closedOddWindowNumerator (fun _ => 1) s t

noncomputable def closedOddWindowExpectation (w : ℕ → ℝ) (s t : ℝ) : ℝ :=
  closedOddWindowNumerator w s t / closedOddWindowMass s t

/-- Closing the lower boundary adds at most one odd source point, with total
harmonic mass at most one and weighted mass between zero and that mass. -/
theorem closedOddWindow_boundary_correction {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ r d : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ d ∧ d ≤ r ∧
      closedOddWindowNumerator w s t = oddWindowNumerator w s t + d ∧
      closedOddWindowMass s t = oddWindowMass s t + r := by
  have hfloor1 : 1 ≤ ⌊Real.exp s⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hs)
  have hceil1 : 1 ≤ ⌈Real.exp s⌉₊ := hfloor1.trans (Nat.floor_le_ceil _)
  have hceil := Nat.ceil_le_floor_add_one (Real.exp s)
  have hfloor := Nat.floor_le_ceil (Real.exp s)
  have hhigh : ⌊Real.exp s⌋₊ ≤ ⌊Real.exp t⌋₊ := Nat.floor_mono (Real.exp_le_exp.mpr hst)
  have hlo : ⌈Real.exp s⌉₊ - 1 ≤ ⌊Real.exp s⌋₊ := by omega
  by_cases he : ⌈Real.exp s⌉₊ - 1 = ⌊Real.exp s⌋₊
  · refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · unfold closedOddWindowNumerator oddWindowNumerator oddLogarithmicCumulative logarithmicCumulative
      rw [he, Finset.sum_Ico_eq_sub _ hhigh, add_zero]
    · unfold closedOddWindowMass closedOddWindowNumerator oddWindowMass
        oddLogarithmicCumulative logarithmicCumulative
      rw [he, Finset.sum_Ico_eq_sub _ hhigh, add_zero]
  · have heq : ⌊Real.exp s⌋₊ = (⌈Real.exp s⌉₊ - 1) + 1 := by omega
    let k := ⌈Real.exp s⌉₊ - 1
    let r : ℝ := (if (k + 1) % 2 = 1 then (1 : ℝ) else 0) / (k + 1 : ℕ)
    let d : ℝ := (if (k + 1) % 2 = 1 then w (k + 1) else 0) / (k + 1 : ℕ)
    have hr0 : 0 ≤ r := by dsimp [r]; split_ifs <;> positivity
    have hr1 : r ≤ 1 := by
      dsimp [r]
      split_ifs
      · apply (div_le_one (by positivity)).mpr
        exact_mod_cast Nat.succ_pos k
      · norm_num
    have hd0 : 0 ≤ d := by
      dsimp [d]
      split_ifs
      · exact div_nonneg (hw0 _) (by positivity)
      · norm_num
    have hdr : d ≤ r := by
      dsimp [d, r]
      split_ifs
      · exact div_le_div_of_nonneg_right (hw1 _) (by positivity)
      · rfl
    have hsplit (f : ℕ → ℝ) : closedOddWindowNumerator f s t =
        oddWindowNumerator f s t +
          (if (k + 1) % 2 = 1 then f (k + 1) else 0) / (k + 1 : ℕ) := by
      unfold closedOddWindowNumerator oddWindowNumerator oddLogarithmicCumulative logarithmicCumulative
      rw [Finset.sum_Ico_eq_sub _ (hlo.trans hhigh), heq, Finset.sum_range_succ]
      dsimp [k]
      ring
    exact ⟨r, d, hr0, hr1, hd0, hdr, hsplit w, hsplit (fun _ => 1)⟩

theorem normalized_boundary_error {B H d r : ℝ}
    (hB0 : 0 ≤ B) (hBH : B ≤ H) (hH : 0 < H)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hd0 : 0 ≤ d) (hdr : d ≤ r) :
    |(B + d) / (H + r) - B / H| ≤ 1 / H := by
  have hHr : 0 < H + r := by linarith
  have hE0 : 0 ≤ B / H := div_nonneg hB0 hH.le
  have hE1 : B / H ≤ 1 := (div_le_one hH).mpr hBH
  have he : (B + d) / (H + r) - B / H = (d - (B / H) * r) / (H + r) := by
    field_simp
    ring
  have hn : |d - (B / H) * r| ≤ r := by
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  rw [he, abs_div, abs_of_pos hHr]
  calc
    |d - (B / H) * r| / (H + r) ≤ r / (H + r) :=
      div_le_div_of_nonneg_right hn hHr.le
    _ ≤ 1 / (H + r) := div_le_div_of_nonneg_right hr1 hHr.le
    _ ≤ 1 / H := div_le_div_of_nonneg_left (by norm_num) hH (by linarith)

theorem closedOddWindowExpectation_sub_open_le {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hmass : 0 < oddWindowMass s t) :
    |closedOddWindowExpectation w s t - oddWindowExpectation w s t| ≤
      1 / oddWindowMass s t := by
  obtain ⟨r, d, hr0, hr1, hd0, hdr, hB, hH⟩ :=
    closedOddWindow_boundary_correction hw0 hw1 hs hst
  have hbounds := oddWindowNumerator_bounds hw0 hw1 hst
  unfold closedOddWindowExpectation oddWindowExpectation
  rw [hB, hH]
  exact normalized_boundary_error hbounds.1 hbounds.2 hmass hr0 hr1 hd0 hdr


theorem closedOddWindowNumerator_eq_inclusive_sum (w : ℕ → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) :
    closedOddWindowNumerator w s t =
      ∑ q ∈ (Finset.Icc ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊).filter (fun q => q % 2 = 1),
        w q / (q : ℝ) := by
  have hf : 1 ≤ ⌊Real.exp s⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hs)
  have hc : 1 ≤ ⌈Real.exp s⌉₊ := hf.trans (Nat.floor_le_ceil _)
  unfold closedOddWindowNumerator
  rw [Finset.sum_Ico_add' (fun q : ℕ => (if q % 2 = 1 then w q else 0) / (q : ℝ))
    (⌈Real.exp s⌉₊ - 1) ⌊Real.exp t⌋₊ 1,
    Nat.sub_add_cancel hc, Finset.Ico_add_one_right_eq_Icc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp

theorem inverse_oddWindowMass_le {s t : ℝ} (hs : Real.log 2 ≤ s)
    (hwidth : 9 ≤ t - s) : 1 / oddWindowMass s t ≤ 18 / (t - s) := by
  have ht : Real.log 2 ≤ t := by linarith
  have hmass := oddWindowMass_pos hs (by linarith : 8 < t - s)
  have hl := (abs_le.mp (odd_harmonic_window_mass_bound hs ht)).1
  change -(4 : ℝ) ≤ oddWindowMass s t - (t - s) / 2 at hl
  apply (div_le_div_iff₀ hmass (by linarith : 0 < t - s)).mpr
  nlinarith

theorem closedOddWindowExpectation_sub_open_le_length {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t : ℝ}
    (hs : Real.log 2 ≤ s) (hwidth : 9 ≤ t - s) :
    |closedOddWindowExpectation w s t - oddWindowExpectation w s t| ≤ 18 / (t - s) := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact (closedOddWindowExpectation_sub_open_le hw0 hw1 (hlog0.trans hs)
    (by linarith) (oddWindowMass_pos hs (by linarith))).trans (inverse_oddWindowMass_le hs hwidth)

theorem open_window_comparison_of_closed {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t u v : ℝ}
    (hs : Real.log 2 ≤ s) (hu : Real.log 2 ≤ u)
    (hwidthST : 9 ≤ t - s) (hwidthUV : 9 ≤ v - u) :
    |oddWindowExpectation w s t - oddWindowExpectation w u v| ≤
      |closedOddWindowExpectation w s t - closedOddWindowExpectation w u v| +
        18 / (t - s) + 18 / (v - u) := by
  have hST := closedOddWindowExpectation_sub_open_le_length hw0 hw1 hs hwidthST
  have hUV := closedOddWindowExpectation_sub_open_le_length hw0 hw1 hu hwidthUV
  have htri₁ := abs_sub_le (oddWindowExpectation w s t)
    (closedOddWindowExpectation w s t) (oddWindowExpectation w u v)
  have htri₂ := abs_sub_le (closedOddWindowExpectation w s t)
    (closedOddWindowExpectation w u v) (oddWindowExpectation w u v)
  rw [abs_sub_comm (oddWindowExpectation w s t) (closedOddWindowExpectation w s t)] at htri₁
  linarith


theorem oddWindow_discrepancy_boundary_error {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t u v : ℝ}
    (hs : Real.log 2 ≤ s) (hu : Real.log 2 ≤ u)
    (hwidthST : 9 ≤ t - s) (hwidthUV : 9 ≤ v - u) :
    |(oddWindowExpectation w s t - oddWindowExpectation w u v) -
      (closedOddWindowExpectation w s t - closedOddWindowExpectation w u v)| ≤
        18 / (t - s) + 18 / (v - u) := by
  have hST := closedOddWindowExpectation_sub_open_le_length hw0 hw1 hs hwidthST
  have hUV := closedOddWindowExpectation_sub_open_le_length hw0 hw1 hu hwidthUV
  have htri := abs_sub_le (oddWindowExpectation w s t - closedOddWindowExpectation w s t) 0
    (oddWindowExpectation w u v - closedOddWindowExpectation w u v)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  rw [abs_sub_comm (oddWindowExpectation w s t) (closedOddWindowExpectation w s t),
    abs_sub_comm (oddWindowExpectation w u v) (closedOddWindowExpectation w u v)] at htri
  have he : (oddWindowExpectation w s t - closedOddWindowExpectation w s t) -
      (oddWindowExpectation w u v - closedOddWindowExpectation w u v) =
      (oddWindowExpectation w s t - oddWindowExpectation w u v) -
        (closedOddWindowExpectation w s t - closedOddWindowExpectation w u v) := by ring
  rw [he] at htri
  linarith

theorem scaled_oddWindow_boundary_error {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {a t : ℝ}
    (ha : 1 < a) (hlog : Real.log 2 ≤ t) (hwidth : 9 ≤ (a - 1) * t) :
    |(oddWindowExpectation w (a * t) (a * (a * t)) - oddWindowExpectation w t (a * t)) -
      (closedOddWindowExpectation w (a * t) (a * (a * t)) -
        closedOddWindowExpectation w t (a * t))| ≤ 36 / ((a - 1) * t) := by
  have hat : t < a * t := by nlinarith
  have hL : 0 < a * t - t := sub_pos.mpr hat
  have hden : a * t - t ≤ a * (a * t) - a * t := by
    have hh := mul_le_mul_of_nonneg_right ha.le hL.le
    nlinarith
  have hwidth₁ : 9 ≤ a * t - t := by nlinarith
  have hh := oddWindow_discrepancy_boundary_error hw0 hw1 (hlog.trans hat.le) hlog
    (hwidth₁.trans hden) hwidth₁
  have hdiv : 18 / (a * (a * t) - a * t) ≤ 18 / (a * t - t) :=
    div_le_div_of_nonneg_left (by norm_num) hL hden
  have he : 18 / (a * t - t) + 18 / (a * t - t) = 36 / ((a - 1) * t) := by
    rw [show a * t - t = (a - 1) * t by ring]
    ring
  linarith

#print axioms closedOddWindow_boundary_correction
#print axioms normalized_boundary_error
#print axioms closedOddWindowExpectation_sub_open_le
#print axioms closedOddWindowNumerator_eq_inclusive_sum
#print axioms open_window_comparison_of_closed
#print axioms scaled_oddWindow_boundary_error

end CollatzCanonical.DirichletAbelian
