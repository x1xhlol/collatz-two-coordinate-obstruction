import FullTwoMatrixBasic

namespace CollatzCertificate.FullTwoMatrix

theorem equal_first_diagonals (a b e f g : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hf : 1 ≤ f)
    (hag : a * g = f * a) (hbe : b * e = f * b)
    (haf : a * f = e * b) : a = b ∧ e = f ∧ g = f := by
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hfpos : 0 < f := by linarith
  have hg : g = f := (mul_left_cancel₀ (ne_of_gt hapos)) (by nlinarith only [hag])
  have he : e = f := (mul_left_cancel₀ (ne_of_gt hbpos)) (by nlinarith only [hbe])
  have hab : a = b := by
    rw [he] at haf
    exact (mul_right_cancel₀ (ne_of_gt hfpos)) (by nlinarith only [haf])
  exact ⟨hab, he, hg⟩

theorem upper_scalar_diagonals_one
    (t s alpha beta gamma u v y c₀ c₁ d₀ d₁ : ℝ)
    (ht : 1 ≤ t) (hs : 1 ≤ s)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hv : 0 ≤ v) (hy : 0 ≤ y)
    (hc₀ : 1 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 1 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (hcg00 : c₀ * (t * t) ≤ c₀ * s)
    (hbd00 : s * d₀ + gamma * d₁ ≤ t * d₀ + beta * d₁)
    (had10 : d₁ ≤ u * d₁) (hbd10 : y * d₁ ≤ v * d₁)
    (hcg01 : c₀ * (t * beta + alpha * v) + c₁ * (u * v) ≤
      c₀ * gamma + c₁ * y) : t = 1 ∧ s = 1 := by
  have hcpos : 0 < c₀ := by linarith only [hc₀]
  have hdpos : 0 < d₀ := by linarith only [hd₀]
  have hts : t * t ≤ s := by nlinarith only [hcg00, hcpos]
  have hst : s ≤ t := by
    by_contra hn
    have hdiff : 0 < s - t := sub_pos.mpr (lt_of_not_ge hn)
    have hprod : 0 < (beta - gamma) * d₁ := by
      nlinarith only [hbd00, mul_pos hdiff hdpos]
    have hd1pos : 0 < d₁ := by
      by_contra hz
      have hz' : d₁ = 0 := le_antisymm (le_of_not_gt hz) hd₁
      simpa [hz'] using hprod
    have hbg : gamma < beta := by
      by_contra hge
      have hnon : 0 ≤ (gamma - beta) * d₁ :=
        mul_nonneg (sub_nonneg.mpr (le_of_not_gt hge)) hd₁
      nlinarith
    have hu : 1 ≤ u := by nlinarith only [had10, hd1pos]
    have hyv : y ≤ v := by nlinarith only [hbd10, hd1pos]
    have hyuv : y ≤ u * v := by
      nlinarith only [hyv, mul_nonneg (sub_nonneg.mpr hu) hv]
    have hcg : t * beta + alpha * v ≤ gamma := by
      have h1 := mul_le_mul_of_nonneg_left hyuv hc₁
      nlinarith only [hcg01, h1, hcpos]
    have hbeta' : beta ≤ t * beta + alpha * v := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr ht) hbeta, mul_nonneg halpha hv]
    linarith
  constructor <;> nlinarith [sq_nonneg (t - 1)]


theorem lower_scalar_diagonals_one
    (t s alpha beta eps phi gamma u v w x y c₀ c₁ d₀ d₁ : ℝ)
    (ht : 1 ≤ t) (hs : 1 ≤ s)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hc₀ : 1 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 1 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (hbd00 : s * d₀ ≤ t * d₀)
    (hce00 : c₀ * t + c₁ * beta ≤ c₀ * s + c₁ * eps)
    (hcf00 : c₀ * (t*t) + c₁ * ((t+u)*alpha) ≤ c₀*s+c₁*phi)
    (hcg00 : c₀ * (t*t) + c₁ * (t*alpha+u*beta) ≤ c₀*s+c₁*gamma)
    (hce01 : c₁*v ≤ c₁*w) (hcf01 : c₁*(u*u) ≤ c₁*x)
    (hcg01 : c₁*(u*v) ≤ c₁*y)
    (haf11 : u*x = w*v) (hag11 : u*y = x*u) (hbf11 : v*x = y*u)
    (hbd10 : gamma*d₀+y*d₁ ≤ beta*d₀+v*d₁)
    (hae10 : eps*t+w*alpha ≤ alpha*s+u*eps)
    (hag10 : phi*t+x*alpha ≤ alpha*s+u*gamma) : t = 1 ∧ s = 1 := by
  have hcpos : 0 < c₀ := by linarith only [hc₀]
  have hdpos : 0 < d₀ := by linarith only [hd₀]
  have hst : s ≤ t := by nlinarith only [hbd00, hdpos]
  suffices htone : t ≤ 1 by constructor <;> linarith
  by_contra hn
  have htgt : 1 < t := lt_of_not_ge hn
  have hgap : 0 < t*t-s := by nlinarith only [hst, htgt]
  have hprod : 0 < c₁*(phi-(t+u)*alpha) := by
    nlinarith only [hcf00, mul_pos hcpos hgap]
  have hc1pos : 0 < c₁ := by
    by_contra hz
    have hz' : c₁ = 0 := le_antisymm (le_of_not_gt hz) hc₁
    simpa [hz'] using hprod
  have hphi : (t+u)*alpha < phi := by
    by_contra hz
    have hz' := mul_nonpos_of_nonneg_of_nonpos hc₁ (sub_nonpos.mpr (le_of_not_gt hz))
    nlinarith only [hprod, hz']
  have hvw : v ≤ w := by nlinarith only [hce01, hc1pos]
  have hux : u*u ≤ x := by nlinarith only [hcf01, hc1pos]
  have huy : u*v ≤ y := by nlinarith only [hcg01, hc1pos]
  have hbe : beta ≤ eps := by
    have h1 := mul_nonneg (le_of_lt hcpos) (sub_nonneg.mpr hst)
    nlinarith only [hce00, h1, hc1pos]
  have hgamma : t*alpha+u*beta < gamma := by
    have h1 := mul_pos hcpos hgap
    by_contra hz
    have h2 := mul_nonneg hc₁ (sub_nonneg.mpr (le_of_not_gt hz))
    nlinarith only [hcg00, h1, h2]
  have hphialpha : alpha < phi := by
    have h1 := mul_nonneg (show 0 ≤ t+u-1 by linarith) halpha
    nlinarith only [hphi, h1]
  by_cases huz : u = 0
  · have hwv : w*v = 0 := by simpa [huz] using haf11.symm
    have hvz : v = 0 := by nlinarith only [hwv, hv, sq_nonneg v, mul_nonneg (sub_nonneg.mpr hvw) hv]
    have h1 := mul_nonneg hx halpha
    have h2 := mul_nonneg (sub_nonneg.mpr hst) halpha
    have h3 := mul_pos (show 0 < t by linarith) (sub_pos.mpr hphialpha)
    simp only [huz, zero_mul, add_zero] at hag10
    nlinarith only [hag10, h1, h2, h3]
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm huz)
    have hxp : 0 < x := by nlinarith only [hux, sq_pos_of_pos hup]
    have hyx : y = x := by nlinarith only [hag11, hup]
    have hvu : v = u := by rw [hyx] at hbf11; nlinarith only [hbf11, hxp]
    have hwx : w = x := by rw [hvu] at haf11; nlinarith only [haf11, hup]
    have hux' : u ≤ x := by simpa [hvu, hwx] using hvw
    have hgb : gamma ≤ beta := by
      rw [hyx, hvu] at hbd10
      have h1 := mul_nonneg (sub_nonneg.mpr hux') hd₁
      nlinarith only [hbd10, h1, hdpos]
    have hul : u < 1 := by
      by_contra hn
      have h1 := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hbeta
      have h2 := mul_nonneg (show 0 ≤ t by linarith) halpha
      nlinarith only [hgamma, hgb, h1, h2]
    have hea : eps ≤ alpha := by
      rw [hwx] at hae10
      have h1 := mul_nonneg (show 0 ≤ t-s+x-u by linarith) halpha
      have h2 : 0 < t-u := by linarith
      by_contra hn
      have h3 := mul_pos h2 (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith only [hae10, h1, h3]
    have hga : gamma ≤ alpha := by linarith
    have h1 := mul_nonneg hu (sub_nonneg.mpr hga)
    have h2 := mul_nonneg (sub_nonneg.mpr hux') halpha
    have h3 := mul_nonneg (sub_nonneg.mpr hst) halpha
    have h4 := mul_pos (show 0 < t by linarith) (sub_pos.mpr hphialpha)
    nlinarith only [hag10, h1, h2, h3, h4]

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.equal_first_diagonals
#print axioms CollatzCertificate.FullTwoMatrix.upper_scalar_diagonals_one

#print axioms CollatzCertificate.FullTwoMatrix.lower_scalar_diagonals_one
