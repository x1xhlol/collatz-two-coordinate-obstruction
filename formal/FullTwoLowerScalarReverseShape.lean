import FullTwoLowerScalar

namespace CollatzResearch.FullTwoLowerScalar

theorem reversed_offset_shape
    (a b e f g β ε φ : ℝ)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (_he : 0 ≤ e) (_hf : 0 ≤ f) (_hg : 0 ≤ g)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε) (hφ : 0 ≤ φ)
    (hbg : g ≤ b)
    (haf : e * b ≤ a * f) (hag : f * a ≤ a * g)
    (hbe : f * b ≤ b * e) (hbf : g * a ≤ b * f)
    (hfa : b * ε + β ≤ φ) (hga : a * φ ≤ β)
    (hea : a * ε ≤ ε) (heb : b * φ + β ≤ e * β + ε) :
    (β = 0 ∧ ε = 0 ∧ φ = 0) ∨
      (a = 1 ∧ b = 0 ∧ f = 0 ∧ g = 0 ∧ φ = β) := by
  have haf_eq : a * f = e * b := by nlinarith only [haf, hag, hbe, hbf]
  have hag_eq : a * g = f * a := by nlinarith only [haf, hag, hbe, hbf]
  have hbe_eq : b * e = f * b := by nlinarith only [haf, hag, hbe, hbf]
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hgf : g = f := by nlinarith only [hag_eq, hapos]
  have hφβ : φ = β := by
    nlinarith only [hfa, hga, mul_nonneg hb hε, mul_nonneg (sub_nonneg.mpr ha) hφ]
  by_cases ha1 : a = 1
  · by_cases hb0 : b = 0
    · have hf0 : f = 0 := by simpa [ha1, hb0] using haf_eq
      exact Or.inr ⟨ha1, hb0, hf0, hgf.trans hf0, hφβ⟩
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hε0 : ε = 0 := by
        rw [hφβ] at hfa
        nlinarith only [hfa, hbpos, hε]
      have hef : e = f := by nlinarith only [hbe_eq, hbpos]
      have heb' : e ≤ b := by linarith only [hef, hgf, hbg]
      have hmul : e * β ≤ b * β := mul_le_mul_of_nonneg_right heb' hβ
      have hβ0 : β = 0 := by
        rw [hφβ, hε0, add_zero] at heb
        linarith only [heb, hmul, hβ]
      exact Or.inl ⟨hβ0, hε0, hφβ.trans hβ0⟩
  · have hagt : 1 < a := lt_of_le_of_ne ha (Ne.symm ha1)
    have hβ0 : β = 0 := by
      rw [hφβ] at hga
      nlinarith only [hga, hagt, hβ]
    have hε0 : ε = 0 := by nlinarith only [hea, hagt, hε]
    exact Or.inl ⟨hβ0, hε0, hφβ.trans hβ0⟩

#print axioms reversed_offset_shape

end CollatzResearch.FullTwoLowerScalar
