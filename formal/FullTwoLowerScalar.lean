import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace CollatzResearch.FullTwoLowerScalar

structure ForwardWeak (a b e f g α β ε φ γ δ : ℝ) : Prop where
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  e_nonneg : 0 ≤ e
  f_nonneg : 0 ≤ f
  g_nonneg : 0 ≤ g
  alpha_nonneg : 0 ≤ α
  beta_nonneg : 0 ≤ β
  epsilon_nonneg : 0 ≤ ε
  phi_nonneg : 0 ≤ φ
  gamma_nonneg : 0 ≤ γ
  delta_nonneg : 0 ≤ δ
  e_boundary : b ≤ e
  f_boundary : a * a ≤ f
  af_matrix : e * b ≤ a * f
  ag_matrix : f * a ≤ a * g
  be_matrix : f * b ≤ b * e
  bf_matrix : g * a ≤ b * f
  bd_offset : g * δ + γ ≤ b * δ + β
  ae_offset : e * α + ε ≤ a * ε + α
  af_offset : e * β + ε ≤ a * φ + α
  ag_offset : f * α + φ ≤ a * γ + α
  be_offset : f * β + φ ≤ b * ε + β
  bf_offset : g * α + γ ≤ b * φ + β
  e_offset : β ≤ ε
  f_offset : a * α + α ≤ φ
  g_offset : a * β + α ≤ γ

theorem forward_classification
    {a b e f g α β ε φ γ δ : ℝ}
    (h : ForwardWeak a b e f g α β ε φ γ δ) :
    (α = 0 ∧ β = 0 ∧ ε = 0 ∧ φ = 0 ∧ γ = 0) ∨
      (a = 0 ∧ b = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧
        0 < α ∧ β = α ∧ ε = α ∧ φ = α ∧ γ = α) := by
  rcases h with ⟨ha, hb, he, hf, hg, hα, hβ, hε, hφ, hγ, hδ,
    heb, hfaa, haf, hag, hbe, hbf, hbd₀, hae₀, haf₀, hag₀, hbe₀, hbf₀,
    hεβ, hφα, hγα⟩
  have haf_eq : a * f = e * b := by nlinarith only [haf, hag, hbe, hbf]
  have hag_eq : a * g = f * a := by nlinarith only [haf, hag, hbe, hbf]
  have hbe_eq : b * e = f * b := by nlinarith only [haf, hag, hbe, hbf]
  by_cases ha0 : a = 0
  · subst a
    have hb0 : b = 0 := by
      have heb0 : e * b = 0 := by simpa using haf_eq.symm
      rcases mul_eq_zero.mp heb0 with he0 | hb0
      · linarith only [heb, hb, he0]
      · exact hb0
    subst b
    simp only [zero_mul, zero_add] at *
    have hφα_eq : φ = α := by nlinarith only [hag₀, hφα, mul_nonneg hf hα]
    have hβα : β = α := by
      nlinarith only [hφα_eq, hbe₀, hae₀, hεβ, mul_nonneg hf hβ,
        mul_nonneg he hα]
    have hεα : ε = α := by nlinarith only [hβα, hεβ, hae₀, mul_nonneg he hα]
    have hγα_eq : γ = α := by nlinarith only [hβα, hγα, hbf₀, mul_nonneg hg hα]
    by_cases hα0 : α = 0
    · exact Or.inl ⟨hα0, hβα.trans hα0, hεα.trans hα0,
        hφα_eq.trans hα0, hγα_eq.trans hα0⟩
    · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have he0 : e = 0 := by nlinarith only [hae₀, hεα, he, hαpos]
      have hf0 : f = 0 := by nlinarith only [hag₀, hφα_eq, hf, hαpos]
      have hg0 : g = 0 := by nlinarith only [hbf₀, hβα, hγα_eq, hg, hαpos]
      exact Or.inr ⟨True.intro, True.intro, he0, hf0, hg0, hαpos,
        hβα, hεα, hφα_eq, hγα_eq⟩
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hfpos : 0 < f := lt_of_lt_of_le (mul_pos hapos hapos) hfaa
    have hbpos : 0 < b := by
      by_contra h
      have hb0 : b = 0 := by linarith only [hb, h]
      have hapf : 0 < a * f := mul_pos hapos hfpos
      rw [hb0, mul_zero] at haf_eq
      linarith only [hapf, haf_eq]
    have hef : e = f := by nlinarith only [hbpos, hbe_eq]
    have hgf : g = f := by nlinarith only [hapos, hag_eq]
    have hab : a = b := by
      rw [hef] at haf_eq
      nlinarith only [haf_eq, hfpos]
    subst b
    subst e
    subst g
    have hγβ : γ ≤ β := by
      nlinarith only [hbd₀, mul_nonneg (sub_nonneg.mpr heb) hδ]
    by_cases ha1 : 1 ≤ a
    · have hβmul : β ≤ a * β := by nlinarith only [mul_nonneg (sub_nonneg.mpr ha1) hβ]
      have hα0 : α = 0 := by linarith only [hγα, hγβ, hβmul, hα]
      have hγeq : γ = β := by linarith only [hγα, hγβ, hβmul, hα]
      have hmul : a * β = β := by linarith only [hγα, hγβ, hβmul, hα]
      have hφβ : φ ≤ β := by rw [hα0, hγeq] at hag₀; nlinarith only [hag₀, hmul]
      have hmulφ : a * φ ≤ a * β := mul_le_mul_of_nonneg_left hφβ ha
      have hβf : β ≤ f * β := by
        have h1f : 1 ≤ f := ha1.trans heb
        nlinarith only [mul_nonneg (sub_nonneg.mpr h1f) hβ]
      have hε0 : ε = 0 := by nlinarith only [haf₀, hmulφ, hmul, hα0, hβf, hε]
      have hβ0 : β = 0 := by linarith only [hεβ, hε0, hβ]
      have hφ0 : φ = 0 := by linarith only [hφβ, hβ0, hφ]
      exact Or.inl ⟨hα0, hβ0, hε0, hφ0, hγeq.trans hβ0⟩
    · have ha_lt : a < 1 := lt_of_not_ge ha1
      have hεα : ε ≤ α := by
        have hh : (1 - a) * ε ≤ (1 - a) * α := by
          nlinarith only [hae₀, mul_nonneg (sub_nonneg.mpr heb) hα]
        exact le_of_mul_le_mul_left hh (sub_pos.mpr ha_lt)
      have habeta : a * β ≤ 0 := by linarith only [hγα, hγβ, hεβ, hεα]
      have hβ0 : β = 0 := by nlinarith only [habeta, hapos, hβ]
      have hαle : α ≤ γ := by simpa [hβ0] using hγα
      have hγ0 : γ = 0 := by linarith only [hγβ, hβ0, hγ]
      have hα0 : α = 0 := by linarith only [hαle, hγ0, hα]
      have hε0 : ε = 0 := by linarith only [hεα, hα0, hε]
      have hφ0 : φ = 0 := by
        have hh : φ ≤ 0 := by simpa [hα0, hγ0] using hag₀
        exact le_antisymm hh hφ
      exact Or.inl ⟨hα0, hβ0, hε0, hφ0, hγ0⟩

theorem forward_gaps_zero
    {a b e f g α β ε φ γ δ : ℝ}
    (h : ForwardWeak a b e f g α β ε φ γ δ) :
    ε = β ∧ φ = a * α + α ∧ γ = a * β + α := by
  rcases forward_classification h with hz | hz
  · rcases hz with ⟨hα, hβ, hε, hφ, hγ⟩
    simp [hα, hβ, hε, hφ, hγ]
  · rcases hz with ⟨ha, _, _, _, _, _, hβ, hε, hφ, hγ⟩
    simp [ha, hβ, hε, hφ, hγ]

theorem reversed_gaps_zero
    (a b f g α β φ γ κ : ℝ)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hα : 0 ≤ α) (_hβ : 0 ≤ β) (hφ : 0 ≤ φ) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (hbg : g ≤ b) (hβγ : γ ≤ β)
    (hga_matrix : a * f ≤ g * a)
    (hgc_offset : b * (a * κ + α) + β ≤ g * κ + γ)
    (hga_offset : a * φ + α ≤ g * α + γ)
    (hfb_offset : a * γ + α ≤ f * β + φ) :
    α = 0 ∧ β = γ := by
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hba : b ≤ b * a := by nlinarith only [mul_nonneg hb (sub_nonneg.mpr ha)]
  have hbag : g ≤ b * a := hbg.trans hba
  have hprod : 0 ≤ (b * a - g) * κ := mul_nonneg (sub_nonneg.mpr hbag) hκ
  have hβα : b * α = 0 := by
    nlinarith only [hgc_offset, hβγ, hprod, mul_nonneg hb hα]
  have hβeq : β = γ := by nlinarith only [hgc_offset, hβγ, hprod, mul_nonneg hb hα]
  have hα0 : α = 0 := by
    by_contra hn
    have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hn)
    have hb0 : b = 0 := (mul_eq_zero.mp hβα).resolve_right hn
    have hg0 : g = 0 := by linarith only [hbg, hb0, hg]
    have hf0 : f = 0 := by nlinarith only [hga_matrix, hg0, ha, hf]
    have haφ : φ ≤ a * φ := by nlinarith only [mul_nonneg (sub_nonneg.mpr ha) hφ]
    have haγ : γ ≤ a * γ := by nlinarith only [mul_nonneg (sub_nonneg.mpr ha) hγ]
    rw [hg0] at hga_offset
    rw [hf0] at hfb_offset
    nlinarith only [hga_offset, hfb_offset, haφ, haγ, hαp]
  exact ⟨hα0, hβeq⟩

#print axioms forward_classification
#print axioms forward_gaps_zero
#print axioms reversed_gaps_zero

end CollatzResearch.FullTwoLowerScalar
