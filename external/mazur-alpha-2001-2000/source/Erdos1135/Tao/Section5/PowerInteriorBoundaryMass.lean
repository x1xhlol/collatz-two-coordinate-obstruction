/-
Modified 2026-09-28 for the independent alpha = 2001/2000 replay of
Mazur's Proposition 1.11 formalization, pinned at ca3dd0d63920.
The changes are documented in alpha-2001-2000.patch and the replay report.
Original copyright and license notices are retained; see LICENSE and NOTICE.
-/

import Erdos1135.Tao.Section5.PowerInteriorFacts
import Erdos1135.Tao.Probability.LogWindowQuarterMass

/-!
# Section 5 Repaired-Interior Boundary Mass

This leaf specializes neutral odd harmonic-window estimates to the two
Section 5 source branches. It proves the discarded repaired-boundary ratio
and contains no passage event, PMF, Fourier, or atom-probability assembly.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

noncomputable section

/-- Full source window with the repaired power interior removed. -/
noncomputable def taoSection5PowerInteriorDiscarded
    (B : ℕ) (branch : TaoSection5SourceBranch) : Finset ℕ :=
  oddLogWindow (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) \
    taoSection5PowerInterior B branch

/-- Eventual geometric and logarithmic scale facts needed for normalized
boundary loss. -/
structure TaoSection5PowerInteriorBoundaryMassFacts (B : ℕ) : Prop where
  geometry : TaoSection5PowerInteriorFacts B
  residue : TaoSection5ResidueScheduleFacts B
  log_large : 24000 ≤ Real.log B

theorem eventually_taoSection5PowerInteriorBoundaryMassFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5PowerInteriorBoundaryMassFacts B := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_taoSection5PowerInteriorFacts,
      eventually_taoSection5ResidueScheduleFacts,
      hlog.eventually_ge_atTop (24000 : ℝ)]
      with B geometry residue log_large
  exact ⟨geometry, residue, log_large⟩

private theorem TaoSection5PowerInteriorBoundaryMassFacts.log_sourceY
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    Real.log (taoSection5SourceY B branch) =
      taoSection5BranchExponent branch * Real.log B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast facts.residue.one_le_B
  rw [taoSection5SourceY_eq_branch_rpow]
  exact Real.log_rpow hBpos _

private theorem TaoSection5PowerInteriorBoundaryMassFacts.two_le_sourceY
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    (2 : ℝ) ≤ taoSection5SourceY B branch := by
  have hBtwo : 2 ≤ B := by
    by_contra hnot
    have hlarge := facts.log_large
    have hBsmall : B ≤ 1 := by omega
    interval_cases B <;> norm_num at hlarge
  have hBcast : (1 : ℝ) ≤ B := by
    exact_mod_cast (show 1 ≤ B by omega)
  rw [taoSection5SourceY_eq_branch_rpow]
  have hself : (B : ℝ) ≤
      Real.rpow B (taoSection5BranchExponent branch) :=
    Real.self_le_rpow_of_one_le hBcast
      (one_le_taoSection5BranchExponent branch)
  exact (by exact_mod_cast hBtwo : (2 : ℝ) ≤ B).trans hself

private theorem TaoSection5PowerInteriorBoundaryMassFacts.log_width
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    12 ≤ (taoAlpha - 1) *
      Real.log (taoSection5SourceY B branch) := by
  have hlogBNonneg : 0 ≤ Real.log B := facts.log_large.trans' (by norm_num)
  have hbranch : Real.log B ≤
      taoSection5BranchExponent branch * Real.log B := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_taoSection5BranchExponent branch) hlogBNonneg
  have hlarge := facts.log_large
  rw [facts.log_sourceY branch]
  norm_num [taoAlpha]
  nlinarith [hlarge, hbranch]

private theorem TaoSection5PowerInteriorBoundaryMassFacts.one_le_delta_log_sourceY
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    1 ≤ taoSection5PowerInteriorDelta B *
      Real.log (taoSection5SourceY B branch) := by
  have hlogBPos : 0 < Real.log B := by nlinarith [facts.log_large]
  have hlogBOne : 1 ≤ Real.log B := by nlinarith [facts.log_large]
  have hfactor :
      taoSection5PowerInteriorDelta B * Real.log B =
        Real.rpow (Real.log B) (9 / 10 : ℝ) := by
    unfold taoSection5PowerInteriorDelta
    have hadd := Real.rpow_add hlogBPos (-1 / 10 : ℝ) (1 : ℝ)
    calc
      Real.rpow (Real.log B) (-1 / 10 : ℝ) * Real.log B =
          Real.rpow (Real.log B) (-1 / 10 : ℝ) *
            Real.rpow (Real.log B) (1 : ℝ) := by
        congr 1
        exact (Real.rpow_one _).symm
      _ = Real.rpow (Real.log B) ((-1 / 10 : ℝ) + 1) := hadd.symm
      _ = Real.rpow (Real.log B) (9 / 10 : ℝ) := by norm_num
  have hone : 1 ≤ Real.rpow (Real.log B) (9 / 10 : ℝ) :=
    Real.one_le_rpow hlogBOne (by norm_num)
  have hbranch : Real.log B ≤
      taoSection5BranchExponent branch * Real.log B := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_taoSection5BranchExponent branch) hlogBPos.le
  have hdeltaNonneg : 0 ≤ taoSection5PowerInteriorDelta B :=
    facts.geometry.delta_pos.le
  rw [facts.log_sourceY branch]
  have hmul := mul_le_mul_of_nonneg_left hbranch hdeltaNonneg
  rw [← hfactor] at hone
  exact hone.trans hmul

theorem TaoSection5PowerInteriorBoundaryMassFacts.source_mass_lower
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    Real.log (taoSection5SourceY B branch) / 8000 ≤
      logFinsetMass
        (oddLogWindow (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)) := by
  have habSource : taoSection5SourceLo B branch ≤
      taoSection5SourceHi B branch := by
    have h := facts.residue.width branch
    omega
  have habRounded :
      Nat.ceil (taoSection5SourceY B branch) ≤
        Nat.floor (Real.rpow (taoSection5SourceY B branch) taoAlpha) := by
    simpa only [taoSection5SourceLo, taoSection5SourceHi, taoNyLo, taoNyHi]
      using habSource
  have hmass := one_quarter_log_width_le_rounded_power_oddWindow_mass
    (facts.two_le_sourceY branch) taoAlpha_one_lt
    habRounded
    (facts.log_width branch)
  calc
    Real.log (taoSection5SourceY B branch) / 8000 =
        ((taoAlpha - 1) / 4) *
          Real.log (taoSection5SourceY B branch) := by
      norm_num [taoAlpha]
      ring
    _ ≤ _ := by
      simpa only [taoSection5SourceLo, taoSection5SourceHi, taoNyLo, taoNyHi]
        using hmass

theorem TaoSection5PowerInteriorBoundaryMassFacts.discarded_eq_strips
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    taoSection5PowerInteriorDiscarded B branch =
      oddLogWindow (taoSection5SourceLo B branch)
          (Nat.ceil (taoSection5PowerInteriorLower B branch) - 1) ∪
        oddLogWindow
          (Nat.floor (taoSection5PowerInteriorUpper B branch) + 1)
          (taoSection5SourceHi B branch) := by
  have hlo : taoSection5SourceLo B branch ≤
      Nat.ceil (taoSection5PowerInteriorLower B branch) := by
    unfold taoSection5SourceLo taoNyLo
    exact Nat.ceil_mono (facts.geometry.source_le_lower branch)
  have hhi : Nat.floor (taoSection5PowerInteriorUpper B branch) ≤
      taoSection5SourceHi B branch := by
    unfold taoSection5SourceHi taoNyHi
    exact Nat.floor_mono (facts.geometry.upper_le_source branch)
  have hlowerOne : 1 ≤
      Nat.ceil (taoSection5PowerInteriorLower B branch) :=
    (facts.residue.one_le_lo branch).trans hlo
  ext n
  simp only [taoSection5PowerInteriorDiscarded, Finset.mem_sdiff,
    oddLogWindow_mem, mem_taoSection5PowerInterior_iff, Finset.mem_union]
  constructor
  · rintro ⟨⟨hnlo, hnhi, hnodd⟩, hnInterior⟩
    by_cases hnLower : n < Nat.ceil (taoSection5PowerInteriorLower B branch)
    · exact Or.inl ⟨hnlo, by omega, hnodd⟩
    · have hnUpper : Nat.floor (taoSection5PowerInteriorUpper B branch) < n := by
        by_contra hnot
        exact hnInterior ⟨by omega, by omega, hnodd⟩
      exact Or.inr ⟨by omega, hnhi, hnodd⟩
  · rintro (hnLower | hnUpper)
    · refine ⟨⟨hnLower.1, ?_, hnLower.2.2⟩, ?_⟩
      · have hroom := facts.geometry.endpoint_room branch
        exact hnLower.2.1.trans (by omega)
      · intro hnInterior
        omega
    · refine ⟨⟨?_, hnUpper.2.1, hnUpper.2.2⟩, ?_⟩
      · exact hlo.trans (by
          have hroom := facts.geometry.endpoint_room branch
          omega)
      · intro hnInterior
        omega

theorem TaoSection5PowerInteriorBoundaryMassFacts.discarded_mass_le
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    logFinsetMass (taoSection5PowerInteriorDiscarded B branch) ≤
      2 + 2 * taoSection5PowerInteriorDelta B *
        Real.log (taoSection5SourceY B branch) := by
  let lower := oddLogWindow (taoSection5SourceLo B branch)
    (Nat.ceil (taoSection5PowerInteriorLower B branch) - 1)
  let upper := oddLogWindow
    (Nat.floor (taoSection5PowerInteriorUpper B branch) + 1)
    (taoSection5SourceHi B branch)
  have hdisjoint : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro n hnLower hnUpper
    dsimp [lower, upper] at hnLower hnUpper
    rw [oddLogWindow_mem] at hnLower hnUpper
    have hroom := facts.geometry.endpoint_room branch
    omega
  have hlower : logFinsetMass lower ≤
      1 + taoSection5PowerInteriorDelta B *
        Real.log (taoSection5SourceY B branch) := by
    simpa only [lower, taoSection5SourceLo, taoNyLo,
      taoSection5PowerInteriorLower] using
        lower_power_boundary_oddWindow_mass_le
          (show (1 : ℝ) ≤ taoSection5SourceY B branch from
            le_trans (by norm_num) (facts.two_le_sourceY branch))
          facts.geometry.delta_pos.le
  have hupper : logFinsetMass upper ≤
      1 + taoSection5PowerInteriorDelta B *
        Real.log (taoSection5SourceY B branch) := by
    simpa only [upper, taoSection5SourceHi, taoNyHi,
      taoSection5PowerInteriorUpper] using
        upper_power_boundary_oddWindow_mass_le
          (alpha := taoAlpha)
          (show (1 : ℝ) ≤ taoSection5SourceY B branch from
            le_trans (by norm_num) (facts.two_le_sourceY branch))
          facts.geometry.delta_pos.le
  rw [facts.discarded_eq_strips branch]
  change logFinsetMass (lower ∪ upper) ≤ _
  unfold logFinsetMass at hlower hupper ⊢
  rw [Finset.sum_union hdisjoint]
  nlinarith

theorem TaoSection5PowerInteriorBoundaryMassFacts.discarded_ratio_le
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    logFinsetMass (taoSection5PowerInteriorDiscarded B branch) /
        logFinsetMass
          (oddLogWindow (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch)) ≤
      32000 * taoSection5PowerInteriorDelta B := by
  let L := Real.log (taoSection5SourceY B branch)
  let D := logFinsetMass
    (oddLogWindow (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch))
  have hLPos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (lt_of_lt_of_le (by norm_num)
      (facts.two_le_sourceY branch))
  have hden : L / 8000 ≤ D := by
    simpa only [L, D] using facts.source_mass_lower branch
  have hDPos : 0 < D := (div_pos hLPos (by norm_num)).trans_le hden
  have hdelta : 0 ≤ taoSection5PowerInteriorDelta B :=
    facts.geometry.delta_pos.le
  have hnum :
      logFinsetMass (taoSection5PowerInteriorDiscarded B branch) ≤
        4 * taoSection5PowerInteriorDelta B * L := by
    have hraw := facts.discarded_mass_le branch
    have hone := facts.one_le_delta_log_sourceY branch
    dsimp [L] at hraw hone ⊢
    nlinarith
  apply (div_le_iff₀ hDPos).2
  have hscaled := mul_le_mul_of_nonneg_left hden
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32000) hdelta)
  nlinarith [hnum, hscaled]

theorem TaoSection5PowerInteriorBoundaryMassFacts.discarded_prob_le
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    logFinsetProb
        (oddLogWindow (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))
        ((↑(taoSection5PowerInterior B branch) : Set ℕ)ᶜ) ≤
      32000 * taoSection5PowerInteriorDelta B := by
  classical
  simpa [logFinsetProb, taoSection5PowerInteriorDiscarded, logFinsetMass,
    Finset.sdiff_eq_filter]
    using facts.discarded_ratio_le branch

theorem eventually_taoSection5PowerInteriorBoundaryRatio :
    ∀ᶠ B : ℕ in atTop,
      ∀ branch : TaoSection5SourceBranch,
        logFinsetMass (taoSection5PowerInteriorDiscarded B branch) /
            logFinsetMass
              (oddLogWindow (taoSection5SourceLo B branch)
                (taoSection5SourceHi B branch)) ≤
          32000 * taoSection5PowerInteriorDelta B := by
  filter_upwards [eventually_taoSection5PowerInteriorBoundaryMassFacts]
    with B facts
  exact facts.discarded_ratio_le

end

end Tao
end Erdos1135
