import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace CollatzResearch.ReversedTriangularTernaryBounds

theorem ternary_secondary_bounds (l α β ν p q e f g u v w : ℝ)
    (hα : 0 ≤ α) (hαl : α < l) (hβl : β < l)
    (hp : 0 ≤ p) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hf : 0 ≤ f)
    (hδ : 0 < (l - α) * q - (l - β) * p)
    (hea : l * u + p * e ≤ ν * p + u * α)
    (hfa : l * u + q * e ≤ ν * p + v * α)
    (hga : l * v + p * f ≤ ν * p + w * α)
    (heb : l * v + q * f ≤ ν * q + u * β)
    (hgb : l * w + q * g ≤ ν * q + w * β)
    (hdiag : α * g = α * f) : e ≤ ν ∧ f ≤ ν ∧ g ≤ ν := by
  have hl : 0 < l := lt_of_le_of_lt hα hαl
  have hq : 0 < q := by
    by_contra hn
    have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hαl).le (le_of_not_gt hn)
    have h2 := mul_nonneg (sub_pos.mpr hβl).le hp
    linarith only [hδ, h1, h2]
  have hg : g ≤ ν := by
    by_contra hn
    have h1 := mul_pos hq (sub_pos.mpr (lt_of_not_ge hn))
    have h2 := mul_nonneg (sub_pos.mpr hβl).le hw
    nlinarith only [hgb, h1, h2]
  have he : e ≤ ν := by
    by_contra hn
    have hne : 0 < e - ν := sub_pos.mpr (lt_of_not_ge hn)
    have h1 := mul_nonneg (sub_pos.mpr hαl).le hu
    have h2 := mul_nonneg hp hne.le
    have hpz : p * (e - ν) = 0 := by
      apply le_antisymm
      · nlinarith only [hea, h1]
      · exact h2
    have hp0 : p = 0 := (mul_eq_zero.mp hpz).resolve_right (ne_of_gt hne)
    have huz : (l - α) * u = 0 := by
      apply le_antisymm
      · nlinarith only [hea, h2]
      · exact h1
    have hu0 : u = 0 := (mul_eq_zero.mp huz).resolve_left (ne_of_gt (sub_pos.mpr hαl))
    have h3 := mul_nonneg hq.le hf
    have h4 := mul_nonneg (sub_pos.mpr hαl).le hv
    have h5 := mul_pos hq hne
    rw [hp0, hu0] at hfa
    rw [hu0] at heb
    nlinarith only [hfa, heb, h3, h4, h5]
  have hfb : f ≤ ν := by
    rcases eq_or_lt_of_le hα with ha0 | ha0
    · have hα0 : α = 0 := ha0.symm
      by_contra hn
      have hnf : 0 < f - ν := sub_pos.mpr (lt_of_not_ge hn)
      have h1 := mul_nonneg hl.le hv
      have h2 := mul_nonneg hp hnf.le
      have hpz : p * (f - ν) = 0 := by
        rw [hα0] at hga
        apply le_antisymm
        · nlinarith only [hga, h1]
        · exact h2
      have hp0 : p = 0 := (mul_eq_zero.mp hpz).resolve_right (ne_of_gt hnf)
      have hvz : l * v = 0 := by
        rw [hα0] at hga
        apply le_antisymm
        · nlinarith only [hga, h2]
        · exact h1
      have hv0 : v = 0 := (mul_eq_zero.mp hvz).resolve_left (ne_of_gt hl)
      have huz : l * u = 0 := by
        rw [hp0, hα0] at hea
        apply le_antisymm
        · nlinarith only [hea]
        · exact mul_nonneg hl.le hu
      have hu0 : u = 0 := (mul_eq_zero.mp huz).resolve_left (ne_of_gt hl)
      have h3 := mul_pos hq hnf
      rw [hv0, hu0] at heb
      nlinarith only [heb, h3]
    · have hfg : f = g := by nlinarith only [hdiag, ha0]
      rw [hfg]
      exact hg
  exact ⟨he, hfb, hg⟩

end CollatzResearch.ReversedTriangularTernaryBounds

#print axioms CollatzResearch.ReversedTriangularTernaryBounds.ternary_secondary_bounds
