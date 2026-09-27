import FullTwoMatrixAggregate

namespace CollatzCertificate.FullTwoMatrix

open Matrix

theorem repeated_scalar_contradiction
    (a b c d e f g hh c₀ c₁ d₀ d₁ : ℝ)
    (ha : 1 ≤ a) (he : 1 ≤ e) (hc₀ : 1 ≤ c₀) (hd₀ : 1 ≤ d₀)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hc₁ : 0 ≤ c₁) (hd₁ : 0 ≤ d₁)
    (had0 : d₀ ≤ a*d₀+b*d₁) (had1 : d₁ ≤ c*d₀+d*d₁)
    (htd0 : e*d₀+f*d₁ ≤ a*d₀+b*d₁)
    (htd1 : g*d₀+hh*d₁ ≤ c*d₀+d*d₁)
    (hct0 : c₀*(a*a+b*c)+c₁*(c*a+d*c) ≤ c₀*e+c₁*g)
    (hct1 : c₀*(a*b+b*d)+c₁*(c*b+d*d) ≤ c₀*f+c₁*hh)
    (hcomm : b*g=f*c) (hupper : 0 < 2*b+3*f) (hlower : 0 < 2*c+3*g) : False := by
  have hapos : 0 < a := by linarith only [ha]
  have hcpos : 0 < c₀ := by linarith only [hc₀]
  have hdpos : 0 < d₀ := by linarith only [hd₀]
  let z₀ := a*d₀+b*d₁-d₀
  let z₁ := c*d₀+d*d₁-d₁
  have hz₀ : 0 ≤ z₀ := sub_nonneg.mpr had0
  have hz₁ : 0 ≤ z₁ := sub_nonneg.mpr had1
  have hsum : c₀*(a*z₀+b*z₁)+c₁*(c*z₀+d*z₁) ≤ 0 := by
    have h1 := mul_nonneg (le_of_lt hdpos) (sub_nonneg.mpr hct0)
    have h2 := mul_nonneg hd₁ (sub_nonneg.mpr hct1)
    have h3 := mul_nonneg (le_of_lt hcpos) (sub_nonneg.mpr htd0)
    have h4 := mul_nonneg hc₁ (sub_nonneg.mpr htd1)
    dsimp [z₀, z₁]
    nlinarith only [h1, h2, h3, h4]
  have hcz : 0 ≤ c₁*(c*z₀+d*z₁) :=
    mul_nonneg hc₁ (add_nonneg (mul_nonneg hc hz₀) (mul_nonneg hd hz₁))
  have haz : a*z₀+b*z₁ = 0 := by
    have hn := add_nonneg (mul_nonneg (le_of_lt hapos) hz₀) (mul_nonneg hb hz₁)
    nlinarith only [hsum, hcz, hcpos, hn]
  have hz₀zero : z₀ = 0 := by nlinarith only [haz, mul_nonneg hb hz₁, hapos, hz₀]
  have hbz₁ : b*z₁ = 0 := by rw [hz₀zero] at haz; simpa using haz
  have hb₁ : b*d₁ = 0 := by
    have hn := mul_nonneg (sub_nonneg.mpr ha) (le_of_lt hdpos)
    have hn' := mul_nonneg hb hd₁
    dsimp [z₀] at hz₀zero
    nlinarith only [hz₀zero, hn, hn']
  have haone : a = 1 := by
    dsimp [z₀] at hz₀zero
    nlinarith only [hz₀zero, hb₁, hdpos]
  have hbc : b*c = 0 := by
    have heq : b*c*d₀=0 := by
      dsimp [z₁] at hbz₁
      nlinarith only [hbz₁, hb₁, show d*(b*d₁)=0 by rw [hb₁]; ring]
    exact (mul_eq_zero.mp heq).resolve_right (ne_of_gt hdpos)
  have hf₁ : f*d₁ = 0 := by
    rw [haone, one_mul, hb₁, add_zero] at htd0
    have hn := mul_nonneg (sub_nonneg.mpr he) (le_of_lt hdpos)
    have hn' := mul_nonneg hf hd₁
    nlinarith only [htd0, hn, hn']
  have hd₁zero : d₁ = 0 := by
    have heq : (2*b+3*f)*d₁ = 0 := by nlinarith only [hb₁, hf₁]
    exact (mul_eq_zero.mp heq).resolve_left (ne_of_gt hupper)
  have hgc : g ≤ c := by
    rw [hd₁zero] at htd1
    nlinarith only [htd1, hdpos]
  have hcpos' : 0 < c := by linarith only [hlower, hgc]
  have hbzero : b = 0 := (mul_eq_zero.mp hbc).resolve_right (ne_of_gt hcpos')
  have hfpos : 0 < f := by rw [hbzero] at hupper; linarith only [hupper]
  rw [hbzero, zero_mul] at hcomm
  exact (ne_of_gt (mul_pos hfpos hcpos')) hcomm.symm

theorem repeated_digits_contradiction (A C D T : M2)
    (hA : EntrywiseLE 0 A) (hC : EntrywiseLE 0 C) (hD : EntrywiseLE 0 D)
    (hT : EntrywiseLE 0 T)
    (hA₀ : 1 ≤ A 0 0) (hC₀ : 1 ≤ C 0 0) (hD₀ : 1 ≤ D 0 0) (hT₀ : 1 ≤ T 0 0)
    (had : EntrywiseLE D (A*D)) (htd : EntrywiseLE (T*D) (A*D))
    (hct : EntrywiseLE (C*(A*A)) (C*T)) (hcomm : A*T=T*A)
    (h01 : 0 < ((A+A)+(T+T+T)) 0 1)
    (h10 : 0 < ((A+A)+(T+T+T)) 1 0) : False := by
  have hcomm00 := congrFun (congrFun hcomm 0) 0
  have h1 := had 0 0
  have h2 := had 1 0
  have h3 := htd 0 0
  have h4 := htd 1 0
  have h5 := hct 0 0
  have h6 := hct 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at hcomm00 h1 h2 h3 h4 h5 h6
  simp only [Matrix.add_apply] at h01 h10
  apply repeated_scalar_contradiction
    (A 0 0) (A 0 1) (A 1 0) (A 1 1) (T 0 0) (T 0 1) (T 1 0) (T 1 1)
    (C 0 0) (C 0 1) (D 0 0) (D 1 0)
    hA₀ hT₀ hC₀ hD₀ (hA 0 1) (hA 1 0) (hA 1 1) (hT 0 1) (hT 1 0)
    (hC 0 1) (hD 1 0) h1 h2 h3 h4 h5 h6
  · nlinarith only [hcomm00]
  · linarith only [h01]
  · linarith only [h10]

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.repeated_scalar_contradiction
#print axioms CollatzCertificate.FullTwoMatrix.repeated_digits_contradiction
