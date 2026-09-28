import OddVectorWindows

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.BanachWindow
open CollatzCanonical.DirichletAbelian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem closedOddVector_boundary_correction {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ (r : ℝ) (d : V), 0 ≤ r ∧ r ≤ 1 ∧ ‖d‖ ≤ r ∧
      closedOddVectorNumerator F s t = oddVectorWindowNumerator F s t + d ∧
      closedOddWindowMass s t = oddWindowMass s t + r := by
  have hfloor1 : 1 ≤ ⌊Real.exp s⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hs)
  have hceil1 : 1 ≤ ⌈Real.exp s⌉₊ := hfloor1.trans (Nat.floor_le_ceil _)
  have hceil := Nat.ceil_le_floor_add_one (Real.exp s)
  have hfloor := Nat.floor_le_ceil (Real.exp s)
  have hhigh : ⌊Real.exp s⌋₊ ≤ ⌊Real.exp t⌋₊ := Nat.floor_mono (Real.exp_le_exp.mpr hst)
  have hlo : ⌈Real.exp s⌉₊ - 1 ≤ ⌊Real.exp s⌋₊ := by omega
  by_cases he : ⌈Real.exp s⌉₊ - 1 = ⌊Real.exp s⌋₊
  · refine ⟨0, 0, by norm_num, by norm_num, by simp, ?_, ?_⟩
    · rw [closedOddVectorNumerator_eq_index_sum F hs, he,
        ← oddVectorWindowNumerator_eq_sum F hst, add_zero]
    · unfold closedOddWindowMass closedOddWindowNumerator oddWindowMass
        oddLogarithmicCumulative logarithmicCumulative
      rw [he, Finset.sum_Ico_eq_sub _ hhigh, add_zero]
  · have heq : ⌊Real.exp s⌋₊ = (⌈Real.exp s⌉₊ - 1) + 1 := by omega
    let k := ⌈Real.exp s⌉₊ - 1
    let r : ℝ := (if (k + 1) % 2 = 1 then (1 : ℝ) else 0) / (k + 1 : ℕ)
    have hr0 : 0 ≤ r := by dsimp [r]; split_ifs <;> positivity
    have hr1 : r ≤ 1 := by
      dsimp [r]
      split_ifs
      · apply (div_le_one (by positivity)).mpr
        exact_mod_cast Nat.succ_pos k
      · norm_num
    refine ⟨r, oddVectorTerm F k, hr0, hr1, oddVectorTerm_norm_le hF k, ?_, ?_⟩
    · rw [closedOddVectorNumerator_eq_index_sum F hs]
      unfold oddVectorWindowNumerator oddVectorCumulative
      rw [Finset.sum_Ico_eq_sub _ (hlo.trans hhigh), heq, Finset.sum_range_succ]
      dsimp only [k]
      abel
    · unfold closedOddWindowMass closedOddWindowNumerator oddWindowMass
        oddLogarithmicCumulative logarithmicCumulative
      rw [Finset.sum_Ico_eq_sub _ (hlo.trans hhigh), heq, Finset.sum_range_succ]
      dsimp only [k, r]
      ring

theorem vector_normalized_boundary_error {B d : V} {H r : ℝ}
    (hB : ‖B‖ ≤ H) (hH : 0 < H) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hd : ‖d‖ ≤ r) :
    ‖(H + r)⁻¹ • (B + d) - H⁻¹ • B‖ ≤ 2 / H := by
  have hHr : 0 < H + r := by linarith
  have hi : (H + r)⁻¹ ≤ H⁻¹ := inv_anti₀ hH (by linarith)
  have he : (H + r)⁻¹ • (B + d) - H⁻¹ • B =
      (H + r)⁻¹ • d + ((H + r)⁻¹ - H⁻¹) • B := by module
  rw [he]
  calc
    _ ≤ ‖(H + r)⁻¹ • d‖ + ‖((H + r)⁻¹ - H⁻¹) • B‖ := norm_add_le _ _
    _ = (H + r)⁻¹ * ‖d‖ + (H⁻¹ - (H + r)⁻¹) * ‖B‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hHr.le), abs_of_nonpos (sub_nonpos.mpr hi)]
      ring
    _ ≤ (H + r)⁻¹ * r + (H⁻¹ - (H + r)⁻¹) * H :=
      add_le_add (mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hHr.le))
        (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hi))
    _ = 2 * r / (H + r) := by field_simp; ring
    _ ≤ 2 / (H + r) :=
      div_le_div_of_nonneg_right (by linarith) hHr.le
    _ ≤ 2 / H := div_le_div_of_nonneg_left (by norm_num) hH (by linarith)

theorem closedOddVectorExpectation_sub_open_le {F : ℕ → V}
    (hF : ∀ q, ‖F q‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hmass : 0 < oddWindowMass s t) :
    ‖closedOddVectorExpectation F s t - oddVectorWindowExpectation F s t‖ ≤
      2 / oddWindowMass s t := by
  obtain ⟨r, d, hr0, hr1, hd, hB, hH⟩ := closedOddVector_boundary_correction hF hs hst
  unfold closedOddVectorExpectation oddVectorWindowExpectation
  rw [hB, hH]
  exact vector_normalized_boundary_error (oddVectorWindowNumerator_norm_le_mass hF hst)
    hmass hr0 hr1 hd

theorem closedOddVectorExpectation_sub_open_le_length {F : ℕ → V}
    (hF : ∀ q, ‖F q‖ ≤ 1) {s t : ℝ} (hs : Real.log 2 ≤ s) (hwidth : 9 ≤ t - s) :
    ‖closedOddVectorExpectation F s t - oddVectorWindowExpectation F s t‖ ≤
      36 / (t - s) := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb := closedOddVectorExpectation_sub_open_le hF (hlog0.trans hs)
    (by linarith) (oddWindowMass_pos hs (by linarith))
  have hi := inverse_oddWindowMass_le hs hwidth
  simp only [div_eq_mul_inv] at hb hi ⊢
  linarith

theorem vector_harmonic_normalization_error {B : V} {H L E : ℝ}
    (hB : ‖B‖ ≤ H) (hH : 0 < H) (hL : 0 < L) (herror : |H - L / 2| ≤ E) :
    ‖L⁻¹ • B - (1 / 2 : ℝ) • (H⁻¹ • B)‖ ≤ E / L := by
  have he : L⁻¹ • B - (1 / 2 : ℝ) • (H⁻¹ • B) =
      (L⁻¹ - (1 / 2 : ℝ) * H⁻¹) • B := by module
  rw [he, norm_smul, Real.norm_eq_abs]
  have heq : |L⁻¹ - (1 / 2 : ℝ) * H⁻¹| * ‖B‖ =
      |‖B‖ / L - (‖B‖ / H) / 2| := by
    calc
      _ = |(L⁻¹ - (1 / 2 : ℝ) * H⁻¹) * ‖B‖| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg B)]
      _ = _ := by congr 1; ring
  rw [heq]
  exact harmonic_normalization_error (norm_nonneg B) hB hH hL herror

theorem oddVectorWindowExpectation_normalization {F : ℕ → V}
    (hF : ∀ q, ‖F q‖ ≤ 1) {s t : ℝ}
    (hs : Real.log 2 ≤ s) (hst : s < t) (hmass : 0 < oddWindowMass s t) :
    ‖(t - s)⁻¹ • oddVectorWindowNumerator F s t -
      (1 / 2 : ℝ) • oddVectorWindowExpectation F s t‖ ≤ 4 / (t - s) :=
  vector_harmonic_normalization_error (oddVectorWindowNumerator_norm_le_mass hF hst.le)
    hmass (sub_pos.mpr hst) (odd_harmonic_window_mass_bound hs (hs.trans hst.le))

theorem closedOddVectorExpectation_normalization {F : ℕ → V}
    (hF : ∀ q, ‖F q‖ ≤ 1) {s t : ℝ}
    (hs : Real.log 2 ≤ s) (hwidth : 9 ≤ t - s) :
    ‖(t - s)⁻¹ • oddVectorWindowNumerator F s t -
      (1 / 2 : ℝ) • closedOddVectorExpectation F s t‖ ≤ 22 / (t - s) := by
  have hopen := oddVectorWindowExpectation_normalization hF hs
    (by linarith) (oddWindowMass_pos hs (by linarith))
  have hclosed := closedOddVectorExpectation_sub_open_le_length hF hs hwidth
  have htri := norm_sub_le_norm_sub_add_norm_sub ((t - s)⁻¹ • oddVectorWindowNumerator F s t)
    ((1 / 2 : ℝ) • oddVectorWindowExpectation F s t)
    ((1 / 2 : ℝ) • closedOddVectorExpectation F s t)
  have he : ‖(1 / 2 : ℝ) • oddVectorWindowExpectation F s t -
      (1 / 2 : ℝ) • closedOddVectorExpectation F s t‖ =
      (1 / 2 : ℝ) * ‖closedOddVectorExpectation F s t - oddVectorWindowExpectation F s t‖ := by
    rw [← smul_sub, norm_smul, norm_sub_rev]
    norm_num
  rw [he] at htri
  calc
    _ ≤ _ := htri
    _ ≤ 4 / (t - s) + (1 / 2 : ℝ) * (36 / (t - s)) :=
      add_le_add hopen (mul_le_mul_of_nonneg_left hclosed (by norm_num))
    _ = 22 / (t - s) := by ring

theorem oddVectorWindowNumerator_smul_eq_windowMean (F : ℕ → V) (a t : ℝ) :
    (a * t - t)⁻¹ • oddVectorWindowNumerator F t (a * t) =
      CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) a t := by
  unfold oddVectorWindowNumerator CollatzCanonical.TwoScale.windowMean
  rw [show a * t - t = (a - 1) * t by ring]

theorem closedOddVector_windowMean_discrepancy {F : ℕ → V}
    (hF : ∀ q, ‖F q‖ ≤ 1) {a t : ℝ}
    (ha : 1 < a) (hlog : Real.log 2 ≤ t) (hwidth : 9 ≤ (a - 1) * t) :
    ‖CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) a (a * t) -
      CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) a t‖ ≤
      ‖closedOddVectorExpectation F (a * t) (a * (a * t)) -
        closedOddVectorExpectation F t (a * t)‖ / 2 + 44 / ((a - 1) * t) := by
  have hat : t < a * t := by nlinarith
  have hL : 0 < a * t - t := sub_pos.mpr hat
  have hden : a * t - t ≤ a * (a * t) - a * t := by
    have hh := mul_le_mul_of_nonneg_right ha.le hL.le
    nlinarith
  have hwidth₁ : 9 ≤ a * t - t := by nlinarith
  have hST := closedOddVectorExpectation_normalization hF (hlog.trans hat.le)
    (hwidth₁.trans hden)
  have hUV := closedOddVectorExpectation_normalization hF hlog hwidth₁
  rw [oddVectorWindowNumerator_smul_eq_windowMean F a (a * t)] at hST
  rw [oddVectorWindowNumerator_smul_eq_windowMean F a t] at hUV
  have htri₁ := norm_sub_le_norm_sub_add_norm_sub
    (CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) a (a * t))
    ((1 / 2 : ℝ) • closedOddVectorExpectation F (a * t) (a * (a * t)))
    (CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) a t)
  have htri₂ := norm_sub_le_norm_sub_add_norm_sub
    ((1 / 2 : ℝ) • closedOddVectorExpectation F (a * t) (a * (a * t)))
    ((1 / 2 : ℝ) • closedOddVectorExpectation F t (a * t))
    (CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) a t)
  rw [norm_sub_rev ((1 / 2 : ℝ) • closedOddVectorExpectation F t (a * t))] at htri₂
  have he : ‖(1 / 2 : ℝ) • closedOddVectorExpectation F (a * t) (a * (a * t)) -
      (1 / 2 : ℝ) • closedOddVectorExpectation F t (a * t)‖ =
      ‖closedOddVectorExpectation F (a * t) (a * (a * t)) -
        closedOddVectorExpectation F t (a * t)‖ / 2 := by
    rw [← smul_sub, norm_smul]
    norm_num
    ring
  rw [he] at htri₂
  have hdiv : 22 / (a * (a * t) - a * t) ≤ 22 / (a * t - t) :=
    div_le_div_of_nonneg_left (by norm_num) hL hden
  have heq : 22 / (a * t - t) + 22 / (a * t - t) = 44 / ((a - 1) * t) := by
    rw [show a * t - t = (a - 1) * t by ring]
    ring
  linarith

end CollatzCanonical.BanachWindow

#print axioms CollatzCanonical.BanachWindow.closedOddVector_boundary_correction
#print axioms CollatzCanonical.BanachWindow.closedOddVectorExpectation_sub_open_le_length
#print axioms CollatzCanonical.BanachWindow.closedOddVectorExpectation_normalization
#print axioms CollatzCanonical.BanachWindow.closedOddVector_windowMean_discrepancy
