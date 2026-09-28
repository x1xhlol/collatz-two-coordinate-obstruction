/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.HoldPMF
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# Section 7 Full Hold Expectations

This module records basic summability and bounded-expectation facts for Tao's
Section 7 `Hold` PMF.  It is renewal-only support for later `Q` vocabulary; it
does not define the actual infinite `Q`, prove a renewal estimate, or prove
Proposition 7.3.
-/

open scoped BigOperators Topology

namespace Erdos1135SecondScale
namespace Tao

theorem pmf_map_tsum_mul_ofReal_bounded
    {α β : Type*} (p : PMF α) (f : α → β) (W : β → ℝ) :
    (∑' b : β, p.map f b * ENNReal.ofReal (W b)) =
      ∑' a : α, p a * ENNReal.ofReal (W (f a)) := by
  classical
  calc
    (∑' b : β, p.map f b * ENNReal.ofReal (W b)) =
        ∑' b : β, (∑' a : α, if b = f a then p a else 0) *
          ENNReal.ofReal (W b) := by
      apply tsum_congr
      intro b
      rw [PMF.map_apply]
    _ = ∑' b : β, ∑' a : α,
        (if b = f a then p a else 0) * ENNReal.ofReal (W b) := by
      apply tsum_congr
      intro b
      rw [ENNReal.tsum_mul_right]
    _ = ∑' a : α, ∑' b : β,
        (if b = f a then p a else 0) * ENNReal.ofReal (W b) := by
      rw [ENNReal.tsum_comm]
    _ = ∑' a : α, p a * ENNReal.ofReal (W (f a)) := by
      apply tsum_congr
      intro a
      rw [tsum_eq_single (f a)]
      · simp
      · intro b hb
        simp [hb]

/-- Transport a bounded real expectation through a possibly non-injective PMF map. -/
theorem pmf_map_weighted_tsum_toReal_eq_of_bounded01
    {α β : Type*} (p : PMF α) (f : α → β) (W : β → ℝ)
    (hW0 : ∀ b, 0 ≤ W b) (hW1 : ∀ b, W b ≤ 1) :
    (Summable fun b : β => (p.map f b).toReal * W b) ∧
    (Summable fun a : α => (p a).toReal * W (f a)) ∧
    (∑' b : β, (p.map f b).toReal * W b) =
      ∑' a : α, (p a).toReal * W (f a) := by
  classical
  let gB : β → ENNReal := fun b => p.map f b * ENNReal.ofReal (W b)
  let gA : α → ENNReal := fun a => p a * ENNReal.ofReal (W (f a))
  have hENN : (∑' b : β, gB b) = ∑' a : α, gA a := by
    simpa [gB, gA] using pmf_map_tsum_mul_ofReal_bounded p f W
  have hAfin : (∑' a : α, gA a) ≠ ⊤ := by
    have hle : (∑' a : α, gA a) ≤ ∑' a : α, p a := by
      apply ENNReal.tsum_le_tsum
      intro a
      have hweight : ENNReal.ofReal (W (f a)) ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal (hW1 (f a))
      simpa [gA] using
        mul_le_mul_of_nonneg_left hweight (show 0 ≤ p a from bot_le)
    rw [PMF.tsum_coe] at hle
    intro htop
    rw [htop] at hle
    exact (not_le_of_gt ENNReal.one_lt_top) hle
  have hBfin : (∑' b : β, gB b) ≠ ⊤ := by
    rw [hENN]
    exact hAfin
  have hsumB : Summable fun b : β => (gB b).toReal :=
    ENNReal.summable_toReal hBfin
  have hsumA : Summable fun a : α => (gA a).toReal :=
    ENNReal.summable_toReal hAfin
  have htermB : ∀ b : β, (p.map f b).toReal * W b = (gB b).toReal := by
    intro b
    simp [gB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hW0 b)]
  have htermA : ∀ a : α, (p a).toReal * W (f a) = (gA a).toReal := by
    intro a
    simp [gA, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hW0 (f a))]
  refine ⟨hsumB.congr (fun b => (htermB b).symm),
    hsumA.congr (fun a => (htermA a).symm), ?_⟩
  calc
    (∑' b : β, (p.map f b).toReal * W b) =
        ∑' b : β, (gB b).toReal := tsum_congr htermB
    _ = (∑' b : β, gB b).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro b
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top
    _ = (∑' a : α, gA a).toReal := by rw [hENN]
    _ = ∑' a : α, (gA a).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro a
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top
    _ = ∑' a : α, (p a).toReal * W (f a) :=
      tsum_congr (fun a => (htermA a).symm)

theorem taoSection7HoldPMF_summable_toReal :
    Summable fun h : TaoSection7RenewalPoint => (taoSection7HoldPMF h).toReal := by
  exact ENNReal.summable_toReal taoSection7HoldPMF.tsum_coe_ne_top

theorem taoSection7HoldPMF_tsum_toReal :
    (∑' h : TaoSection7RenewalPoint, (taoSection7HoldPMF h).toReal) = 1 := by
  simpa using
    (ENNReal.tsum_toReal_eq
      (f := fun h : TaoSection7RenewalPoint => taoSection7HoldPMF h)
      (fun h => taoSection7HoldPMF.apply_ne_top h)).symm

/-- Full expectation against Tao's Section 7 `Hold` PMF. -/
noncomputable def taoSection7HoldExpectationFull
    (F : TaoSection7RenewalPoint → ℝ) : ℝ :=
  ∑' h : TaoSection7RenewalPoint, (taoSection7HoldPMF h).toReal * F h

theorem taoSection7HoldExpectationFull_summable_of_bounded01
    {F : TaoSection7RenewalPoint → ℝ}
    (hF0 : ∀ h, 0 ≤ F h) (hF1 : ∀ h, F h ≤ 1) :
    Summable fun h : TaoSection7RenewalPoint =>
      (taoSection7HoldPMF h).toReal * F h := by
  refine Summable.of_norm_bounded taoSection7HoldPMF_summable_toReal ?_
  intro h
  have hmass : 0 ≤ (taoSection7HoldPMF h).toReal := ENNReal.toReal_nonneg
  have hFabs : |F h| ≤ 1 := by
    rw [abs_of_nonneg (hF0 h)]
    exact hF1 h
  calc
    ‖(taoSection7HoldPMF h).toReal * F h‖
        = (taoSection7HoldPMF h).toReal * |F h| := by
          simp [Real.norm_eq_abs, abs_of_nonneg hmass]
    _ ≤ (taoSection7HoldPMF h).toReal * 1 := by
          exact mul_le_mul_of_nonneg_left hFabs hmass
    _ = (taoSection7HoldPMF h).toReal := by ring

theorem taoSection7HoldExpectationFull_nonneg_of_nonneg
    {F : TaoSection7RenewalPoint → ℝ} (hF0 : ∀ h, 0 ≤ F h) :
    0 ≤ taoSection7HoldExpectationFull F := by
  unfold taoSection7HoldExpectationFull
  exact tsum_nonneg (by
    intro h
    exact mul_nonneg ENNReal.toReal_nonneg (hF0 h))

theorem taoSection7HoldExpectationFull_le_one_of_bounded01
    {F : TaoSection7RenewalPoint → ℝ}
    (hF0 : ∀ h, 0 ≤ F h) (hF1 : ∀ h, F h ≤ 1) :
    taoSection7HoldExpectationFull F ≤ 1 := by
  unfold taoSection7HoldExpectationFull
  calc
    (∑' h : TaoSection7RenewalPoint, (taoSection7HoldPMF h).toReal * F h)
        ≤ ∑' h : TaoSection7RenewalPoint, (taoSection7HoldPMF h).toReal := by
          exact
            (taoSection7HoldExpectationFull_summable_of_bounded01 hF0 hF1).tsum_le_tsum
              (by
                intro h
                have hmass : 0 ≤ (taoSection7HoldPMF h).toReal :=
                  ENNReal.toReal_nonneg
                calc
                  (taoSection7HoldPMF h).toReal * F h
                      ≤ (taoSection7HoldPMF h).toReal * 1 := by
                        exact mul_le_mul_of_nonneg_left (hF1 h) hmass
                  _ = (taoSection7HoldPMF h).toReal := by ring)
              taoSection7HoldPMF_summable_toReal
    _ = 1 := taoSection7HoldPMF_tsum_toReal

theorem taoSection7HoldExpectationFull_mono_of_bounded01
    {F G : TaoSection7RenewalPoint → ℝ}
    (hF0 : ∀ h, 0 ≤ F h) (hF1 : ∀ h, F h ≤ 1)
    (hG0 : ∀ h, 0 ≤ G h) (hG1 : ∀ h, G h ≤ 1)
    (hFG : ∀ h, F h ≤ G h) :
    taoSection7HoldExpectationFull F ≤ taoSection7HoldExpectationFull G := by
  unfold taoSection7HoldExpectationFull
  exact
    (taoSection7HoldExpectationFull_summable_of_bounded01 hF0 hF1).tsum_le_tsum
      (by
        intro h
        exact mul_le_mul_of_nonneg_left (hFG h) ENNReal.toReal_nonneg)
      (taoSection7HoldExpectationFull_summable_of_bounded01 hG0 hG1)

theorem taoSection7HoldExpectationFull_tendsto_of_bounded01
    {F : ℕ → TaoSection7RenewalPoint → ℝ}
    {G : TaoSection7RenewalPoint → ℝ}
    (hlim : ∀ h,
      Filter.Tendsto (fun K : ℕ => F K h) Filter.atTop (𝓝 (G h)))
    (hF0 : ∀ K h, 0 ≤ F K h)
    (hF1 : ∀ K h, F K h ≤ 1) :
    Filter.Tendsto
      (fun K : ℕ => taoSection7HoldExpectationFull (fun h => F K h))
      Filter.atTop
      (𝓝 (taoSection7HoldExpectationFull G)) := by
  unfold taoSection7HoldExpectationFull
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun h : TaoSection7RenewalPoint => (taoSection7HoldPMF h).toReal)
    taoSection7HoldPMF_summable_toReal ?_ ?_
  · intro h
    exact (hlim h).const_mul (taoSection7HoldPMF h).toReal
  · exact Filter.Eventually.of_forall fun K h => by
      have hmass : 0 ≤ (taoSection7HoldPMF h).toReal := ENNReal.toReal_nonneg
      have hFabs : |F K h| ≤ 1 := by
        rw [abs_of_nonneg (hF0 K h)]
        exact hF1 K h
      calc
        ‖(taoSection7HoldPMF h).toReal * F K h‖
            = |(taoSection7HoldPMF h).toReal * F K h| := Real.norm_eq_abs _
        _ = (taoSection7HoldPMF h).toReal * |F K h| := by
            rw [abs_mul, abs_of_nonneg hmass]
        _ ≤ (taoSection7HoldPMF h).toReal * 1 := by
            exact mul_le_mul_of_nonneg_left hFabs hmass
        _ = (taoSection7HoldPMF h).toReal := by ring

end Tao
end Erdos1135SecondScale
