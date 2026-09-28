import BanachPassageTransport
import NaturalPassageBridge

open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
open Erdos1135 CollatzCanonical.NativeTao CollatzCylinderPacking.Arithmetic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem natural_vector_comparison (F : ℕ → V) (hF : ∀ q, ‖F q‖ ≤ 1)
    {x y : ℝ} (hx : 1 ≤ x)
    (hpass : ∀ (q : ℕ), Odd q → ∀ τ,
      Tao.syracuseFirstHitAtMostReal x q τ → F q = F ((Tao.syracuse^[τ]) q))
    (hwindow : (ND.oddBlock y).Nonempty)
    (hmass : 0 < Tao.logFinsetMass (ND.oddBlock y)) :
    ‖pmfMeanV (ND.uniformOddBlockPMF y hwindow) (fun q => F q.1) -
      pmfMeanV (ND.logOddBlockPMF y hmass) (fun q => F q.1)‖ ≤
      2 * ND.uniformNoHitProbability x y hwindow +
      2 * Tao.syracuseNoHitRealWindowProb x (Tao.taoNyLo y) (Tao.taoNyHi y ND.alpha) hmass +
      ND.passFullL1 x y hx hwindow hmass := by
  classical
  have hgood (q : {n // n ∈ ND.oddBlock y})
      (hq : ¬¬Tao.syracuseHitsAtMostReal q.1 x) :
      F q.1 = F (ND.passLocationOrOne x q.1 hx).1 := by
    have hx0 : 0 ≤ x := by linarith
    have hh := (Tao.syracuseHitsAtMostReal_iff_floor hx0).mp (not_not.mp hq)
    have hn := Tao.syracuseFirstHitAtMost_of_hitsAtMost q.1 ⌊x⌋₊ hh
    have hreal := (Tao.syracuseFirstHitAtMostReal_iff_floor hx0).mpr hn
    rw [natural_pass_eq_native, native_real_passLocation_eq_of_first hx hreal]
    exact hpass q.1 (Nat.odd_iff.mpr (Tao.oddLogWindow_mem.mp q.2).2.2) _ hreal
  have he := finiteMeanV_two_passage_bound
    (fun q => ((ND.uniformOddBlockPMF y hwindow) q).toReal)
    (fun q => ((ND.logOddBlockPMF y hmass) q).toReal)
    (fun q => F q.1) (fun q => F q.1)
    (fun q => ND.passLocationOrOne x q.1 hx) (fun q => ND.passLocationOrOne x q.1 hx)
    (fun q => F q.1)
    (fun q => ¬Tao.syracuseHitsAtMostReal q.1 x)
    (fun q => ¬Tao.syracuseHitsAtMostReal q.1 x)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (fun q => hF q.1) (fun q => hF q.1) (fun q => hF q.1) hgood hgood
  rw [finiteBadMass_eq_native_probability, finiteBadMass_eq_native_probability,
    finite_landing_fullL1_eq_native_TV] at he
  exact he

theorem eventually_natural_vector_comparison (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (hpass : EventuallyPassageInvariant F) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (_hx : 1 ≤ x) (branch : Tao.TaoSection5SourceBranch),
      let y := ND.transportSourceY x branch
      ∃ hwindow : (ND.oddBlock y).Nonempty,
      ∃ hmass : 0 < Tao.logFinsetMass (ND.oddBlock y),
      ‖pmfMeanV (ND.uniformOddBlockPMF y hwindow) (fun q => F q.1) -
        pmfMeanV (ND.logOddBlockPMF y hmass) (fun q => F q.1)‖ ≤
        368 * x ^ (-(1 / 32000 : ℝ)) + 2 * C * x ^ (-c) +
          384256 * (Real.log x) ^ (-(1 / 40 : ℝ)) := by
  obtain ⟨errNoHit, errTV, C, c, hC, hc, hrates, hTV⟩ :=
    Tao.taoProp111RealFirstPassageStabilizationRate_checked
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [unconditional_natural_passage_rates, hrates, hpass] with x hND hr hxpass
  intro hx branch
  obtain ⟨hw₁, hm₁, hu₁, ht₁⟩ := hND hx .alpha
  obtain ⟨hw₂, hm₂, hu₂, ht₂⟩ := hND hx .alphaSq
  have hpair : Tao.TaoProp111RealWindowPair x
      (Tao.taoNyLo (ND.transportSourceY x .alpha))
      (Tao.taoNyHi (ND.transportSourceY x .alpha) ND.alpha)
      (Tao.taoNyLo (ND.transportSourceY x .alphaSq))
      (Tao.taoNyHi (ND.transportSourceY x .alphaSq) ND.alpha) := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hl₁, hl₂, _⟩ := hTV x _ _ _ _ hx hpair hm₁ hm₂
  have hno := hr.2.2.1
  cases branch
  · refine ⟨hw₁, hm₁, ?_⟩
    have h := natural_vector_comparison F hF hx hxpass hw₁ hm₁
    linarith
  · refine ⟨hw₂, hm₂, ?_⟩
    have h := natural_vector_comparison F hF hx hxpass hw₂ hm₂
    linarith

theorem natural_vector_comparison_error_tendsto_zero {C c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
      368 * x ^ (-(1 / 32000 : ℝ)) + 2 * C * x ^ (-c) +
        384256 * (Real.log x) ^ (-(1 / 40 : ℝ))) atTop (𝓝 0) := by
  have hu := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1 / 32000)).const_mul 368
  have hl := (tendsto_rpow_neg_atTop hc).const_mul (2 * C)
  have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1 / 40)).comp
    Real.tendsto_log_atTop).const_mul 384256
  simpa only [mul_zero, zero_add, Function.comp_def] using (hu.add hl).add ht

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.natural_vector_comparison
#print axioms CollatzCanonical.LabelLaw.eventually_natural_vector_comparison
#print axioms CollatzCanonical.LabelLaw.natural_vector_comparison_error_tendsto_zero
