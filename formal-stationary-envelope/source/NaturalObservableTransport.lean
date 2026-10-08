import NaturalPassageBridge

set_option autoImplicit false

namespace CollatzCanonical.NativeTao
open Erdos1135 CollatzClockAudit CollatzCylinderPacking.Arithmetic

theorem natural_small_landing_transport {x y : ℝ} (hx : 1 ≤ x)
    (hwindow : (ND.oddBlock y).Nonempty)
    (hmass : 0 < Tao.logFinsetMass (ND.oddBlock y)) :
    Tao.pmfProb (ND.uniformOddBlockPMF y hwindow)
      {q | ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ)} ≤
    Tao.pmfProb (ND.logOddBlockPMF y hmass)
      {q | ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ)} +
      ND.passFullL1 x y hx hwindow hmass := by
  have h := Tao.abs_pmfProb_sub_le_taoTV
    (ND.uniformPassLaw x y hx hwindow) (ND.logPassLaw x y hx hmass)
    {z | (z.1 : ℝ) ≤ x ^ (1 / 2 : ℝ)}
  rw [ND.uniformPassLaw, ND.logPassLaw,
    Tao.pmfProb_map_preimage, Tao.pmfProb_map_preimage] at h
  exact (sub_le_iff_le_add.mp ((abs_le.mp h).2)).trans_eq (add_comm _ _)

theorem natural_large_passage_good {x y : ℝ} (hx : 1 ≤ x) (N : ℕ)
    (hNsqrt : (N : ℝ) ≤ x ^ (1 / 2 : ℝ))
    (q : {n // n ∈ ND.oddBlock y})
    (hq : ¬ ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ)) :
    GoodOddBarrierLanding q.1 (ND.passLocationOrOne x q.1 hx).1 N x := by
  have ho : Odd q.1 := Nat.odd_iff.mpr (Tao.oddLogWindow_mem.mp q.2).2.2
  have hg := (native_large_landing_iff x hx ⟨q.1, ho⟩).mpr (lt_of_not_ge hq)
  obtain ⟨n, hn, hlarge⟩ := hg
  rw [natural_pass_eq_native, native_real_passLocation_eq_of_first hx hn]
  apply native_real_first_passage_goodLanding (by linarith) ho hn
  exact_mod_cast lt_of_le_of_lt hNsqrt hlarge

theorem natural_basin_comparison {x y : ℝ} (hx : 1 ≤ x) (N : ℕ)
    (hN : (N : ℝ) ≤ x) (hNsqrt : (N : ℝ) ≤ x ^ (1 / 2 : ℝ))
    (hwindow : (ND.oddBlock y).Nonempty)
    (hmass : 0 < Tao.logFinsetMass (ND.oddBlock y)) :
    |Tao.pmfExpectation (ND.uniformOddBlockPMF y hwindow) (fun q => basinIndicator N q.1) -
      Tao.pmfExpectation (ND.logOddBlockPMF y hmass) (fun q => basinIndicator N q.1)| ≤
      2 * Tao.pmfProb (ND.logOddBlockPMF y hmass)
        {q | ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ)} +
      2 * ND.passFullL1 x y hx hwindow hmass := by
  have h := native_basin_passage_expectation
    (ND.uniformOddBlockPMF y hwindow) (ND.logOddBlockPMF y hmass)
    (fun q => q.1) (fun q => q.1)
    (fun q => ND.passLocationOrOne x q.1 hx) (fun q => ND.passLocationOrOne x q.1 hx)
    (fun z => z.1)
    (fun q => ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ))
    (fun q => ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ))
    N x hN (fun q hq => natural_large_passage_good hx N hNsqrt q hq)
    (fun q hq => natural_large_passage_good hx N hNsqrt q hq)
  have hp := natural_small_landing_transport hx hwindow hmass
  change _ ≤ _ + _ + ND.passFullL1 x y hx hwindow hmass at h
  linarith

theorem natural_weight_comparison (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x y : ℝ} (hx : 1 ≤ x) (N : ℕ),
      (N : ℝ) ≤ x → (N : ℝ) ≤ x ^ (1 / 2 : ℝ) →
      ∀ (hwindow : (ND.oddBlock y).Nonempty)
        (hmass : 0 < Tao.logFinsetMass (ND.oddBlock y)),
      |Tao.pmfExpectation (ND.uniformOddBlockPMF y hwindow) (fun q => firstHitWeight N q.1) -
        Tao.pmfExpectation (ND.logOddBlockPMF y hmass) (fun q => firstHitWeight N q.1)| ≤
        2 * C * x ^ (b - 1) +
        2 * Tao.pmfProb (ND.logOddBlockPMF y hmass)
          {q | ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ)} +
        2 * ND.passFullL1 x y hx hwindow hmass := by
  obtain ⟨C, hC, hbound⟩ := native_firstHitWeight_passage_expectation b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro x y hx N hN hNsqrt hwindow hmass
  have hpositive (q : {n // n ∈ ND.oddBlock y}) : 0 < q.1 := by
    have ho := (Tao.oddLogWindow_mem.mp q.2).2.2
    omega
  have h := hbound (ND.uniformOddBlockPMF y hwindow) (ND.logOddBlockPMF y hmass)
    (fun q => q.1) (fun q => q.1)
    (fun q => ND.passLocationOrOne x q.1 hx) (fun q => ND.passLocationOrOne x q.1 hx)
    (fun z => z.1)
    (fun q => ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ))
    (fun q => ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ))
    N x hpositive hpositive hx hN
    (fun q hq => natural_large_passage_good hx N hNsqrt q hq)
    (fun q hq => natural_large_passage_good hx N hNsqrt q hq)
  have hp := natural_small_landing_transport hx hwindow hmass
  change _ ≤ _ + _ + _ + ND.passFullL1 x y hx hwindow hmass at h
  linarith

#print axioms natural_basin_comparison
#print axioms natural_weight_comparison

end CollatzCanonical.NativeTao
