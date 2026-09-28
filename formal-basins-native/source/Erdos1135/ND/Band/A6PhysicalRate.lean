import Erdos1135.ND.Band.A6PhysicalQuadratureRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A6 Fixed-`C` Physical Rate

This leaf converts the checked lower-endpoint `N0 / nu` packet into the
source logarithmic three-halves rate.  It proves both finite local-error
bounds and the eventual moderate-window guard with `C` fixed before the
threshold variable.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The source-shaped logarithmic rate at the Section 5 schedule. -/
def ndA6PhysicalRate (B : ℕ) : ℝ :=
  let N : ℝ := Tao.taoSection5N0 B
  Real.log N ^ (3 / 2 : ℝ) / Real.sqrt N

/-- The Section 5 floor schedule tends to infinity. -/
theorem ndTendsto_taoSection5N0_atTop :
    Filter.Tendsto Tao.taoSection5N0 Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro n
  filter_upwards [Filter.eventually_ge_atTop (2 ^ (10 * n) : ℕ)] with B hB
  have hlog : 10 * n ≤ Nat.log 2 B :=
    Nat.le_log_of_pow_le (by norm_num) hB
  unfold Tao.taoSection5N0
  omega

/-- The physical A6 rate tends to zero along the Section 5 floor schedule. -/
theorem tendsto_ndA6PhysicalRate_zero :
    Filter.Tendsto ndA6PhysicalRate Filter.atTop (nhds 0) := by
  have hreal : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ (3 / 2 : ℝ) / x ^ (1 / 2 : ℝ))
      Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hschedule : Filter.Tendsto
      (fun B : ℕ => (Tao.taoSection5N0 B : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp ndTendsto_taoSection5N0_atTop
  apply (hreal.comp hschedule).congr'
  filter_upwards [] with B
  simp [ndA6PhysicalRate, Real.sqrt_eq_rpow]

/-- The checked T2 packet at the physical lower tube endpoint. -/
theorem ndA6PhysicalN0_div_tubeLo_mem_Icc
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (Tao.taoSection5N0 B : ℝ) /
        (ndA5TubeLo
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) : ℝ) ∈
      Set.Icc (1374 / 100 : ℝ) (4244 / 100 : ℝ) := by
  classical
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let lo := ndA5TubeLo A W
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [A, W] using hTube.nonempty
  have hWpos : 0 < W := by
    obtain ⟨nu, hnu⟩ := hne
    exact (abs_nonneg (ndA5StrictAffineSweep A nu : ℝ)).trans_lt
      (Finset.mem_filter.mp hnu).2
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : lo ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hloMem : lo ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr hlohi
  have hcell : NDA5InteriorCellFacts B j lo branch C M :=
    hTube.pointwise lo (by simpa [A, W, lo] using hloMem)
  have hsub : lo + Tao.taoSection5M0 B - Tao.taoSection5M0 B = lo := by
    omega
  have hlower := hcell.t2.n0_div_nu_lower
  have hupper := hcell.t2.n0_div_nu_upper
  rw [hsub] at hlower hupper
  constructor
  · simpa [A, W, lo] using hlower
  · simpa [A, W, lo] using hupper

private theorem ndA6Physical_ratio_rate_packet
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    0 ≤ C ∧ 0 ≤ ndA6PhysicalRate B ∧
      ndA6PhysicalLinearRatio B j branch C M ≤
        (4244 / 100 : ℝ) * C * ndA6PhysicalRate B ∧
      ndA6PhysicalCubicRatio B j branch C M ≤
        (4244 / 100 : ℝ) ^ 2 * C ^ 3 * ndA6PhysicalRate B := by
  classical
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let lo := ndA5TubeLo A W
  let N : ℝ := Tao.taoSection5N0 B
  let L := Real.log N
  let u := Real.sqrt L / Real.sqrt N
  let rho := ndA6PhysicalRate B
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [A, W] using hTube.nonempty
  have hWpos : 0 < W := by
    obtain ⟨nu, hnu⟩ := hne
    exact (abs_nonneg (ndA5StrictAffineSweep A nu : ℝ)).trans_lt
      (Finset.mem_filter.mp hnu).2
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : lo ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hloMem : lo ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr hlohi
  have hcell : NDA5InteriorCellFacts B j lo branch C M :=
    hTube.pointwise lo (by simpa [A, W, lo] using hloMem)
  have hloNat : 0 < lo := by
    simpa [A, W, lo] using hTube.lo_pos
  have hlo : (0 : ℝ) < lo := by exact_mod_cast hloNat
  have hsub : lo + Tao.taoSection5M0 B - Tao.taoSection5M0 B = lo := by
    omega
  have hkRaw := hcell.t2.n0_div_nu_upper
  have hkLowerRaw := hcell.t2.n0_div_nu_lower
  rw [hsub] at hkRaw hkLowerRaw
  have hk : N / (lo : ℝ) ≤ (4244 / 100 : ℝ) := by
    simpa [N] using hkRaw
  have hkLower : (1374 / 100 : ℝ) ≤ N / (lo : ℝ) := by
    simpa [N] using hkLowerRaw
  have hNlower : (1374 / 100 : ℝ) * (lo : ℝ) ≤ N :=
    (le_div_iff₀ hlo).mp hkLower
  have hloOne : (1 : ℝ) ≤ lo := by exact_mod_cast hloNat
  have hNthree : (3 : ℝ) < N := by nlinarith
  have hNpos : 0 < N := by linarith
  have hLone : (1 : ℝ) < L := by
    dsimp [L]
    exact (Real.lt_log_iff_exp_lt hNpos).2
      (Real.exp_one_lt_three.trans hNthree)
  have hL0 : 0 ≤ L := by linarith
  have hC0 : 0 ≤ C := by linarith [hcell.one_half_le_C]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hu : 0 ≤ u := div_nonneg (Real.sqrt_nonneg _) hsN.le
  have hLpow : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    rw [Real.rpow_div_two_eq_sqrt 3 hL0]
    calc
      Real.sqrt L ^ (3 : ℝ) = Real.sqrt L ^ (3 : ℕ) :=
        Real.rpow_natCast _ 3
      _ = Real.sqrt L ^ 2 * Real.sqrt L := by ring
      _ = L * Real.sqrt L := by rw [Real.sq_sqrt hL0]
  have hrho : rho = L * u := by
    dsimp [rho, ndA6PhysicalRate, N, L, u]
    rw [hLpow]
    ring
  have hrho0 : 0 ≤ rho := by
    rw [hrho]
    positivity
  have hWform : W = C * (Real.sqrt N * Real.sqrt L) := by
    dsimp [W, N, L, ndA5TubeWidth]
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  have haEq : ndA6PhysicalLinearRatio B j branch C M =
      (N / (lo : ℝ)) * C * u := by
    change W / (lo : ℝ) = (N / (lo : ℝ)) * C * u
    rw [hWform]
    dsimp [u]
    field_simp [hlo.ne', hsN.ne']
    nlinarith [Real.sq_sqrt hNpos.le]
  have htEq : W ^ 2 / (lo : ℝ) =
      (N / (lo : ℝ)) * C ^ 2 * L := by
    rw [hWform, mul_pow, mul_pow, Real.sq_sqrt hNpos.le,
      Real.sq_sqrt hL0]
    ring
  have hbEq : ndA6PhysicalCubicRatio B j branch C M =
      ndA6PhysicalLinearRatio B j branch C M * (W ^ 2 / (lo : ℝ)) := by
    change W ^ 3 / (lo : ℝ) ^ 2 =
      (W / (lo : ℝ)) * (W ^ 2 / (lo : ℝ))
    field_simp [hlo.ne']
  have haFine : ndA6PhysicalLinearRatio B j branch C M ≤
      (4244 / 100 : ℝ) * C * u := by
    rw [haEq]
    calc
      (N / (lo : ℝ)) * C * u = (N / (lo : ℝ)) * (C * u) := by ring
      _ ≤ (4244 / 100 : ℝ) * (C * u) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg hC0 hu)
      _ = _ := by ring
  have huRho : u ≤ rho := by
    rw [hrho]
    calc
      u = 1 * u := by ring
      _ ≤ L * u := mul_le_mul_of_nonneg_right hLone.le hu
  have haRate : ndA6PhysicalLinearRatio B j branch C M ≤
      (4244 / 100 : ℝ) * C * rho :=
    haFine.trans
      (mul_le_mul_of_nonneg_left huRho
        (mul_nonneg (by norm_num) hC0))
  have htFine : W ^ 2 / (lo : ℝ) ≤
      (4244 / 100 : ℝ) * C ^ 2 * L := by
    rw [htEq]
    calc
      (N / (lo : ℝ)) * C ^ 2 * L =
          (N / (lo : ℝ)) * (C ^ 2 * L) := by ring
      _ ≤ (4244 / 100 : ℝ) * (C ^ 2 * L) :=
        mul_le_mul_of_nonneg_right hk
          (mul_nonneg (sq_nonneg C) hL0)
      _ = _ := by ring
  have ht0 : 0 ≤ W ^ 2 / (lo : ℝ) :=
    div_nonneg (sq_nonneg W) hlo.le
  have hbRate : ndA6PhysicalCubicRatio B j branch C M ≤
      (4244 / 100 : ℝ) ^ 2 * C ^ 3 * rho := by
    rw [hbEq]
    calc
      ndA6PhysicalLinearRatio B j branch C M * (W ^ 2 / (lo : ℝ)) ≤
          ((4244 / 100 : ℝ) * C * u) *
            ((4244 / 100 : ℝ) * C ^ 2 * L) :=
        mul_le_mul haFine htFine ht0 (by positivity)
      _ = (4244 / 100 : ℝ) ^ 2 * C ^ 3 * (L * u) := by ring
      _ = _ := by rw [← hrho]
  exact ⟨hC0, hrho0, haRate, hbRate⟩

/-- The physical linear tube ratio has the exact source-rate majorant used by
later endpoint-uniform A6 consumers. -/
theorem ndA6PhysicalLinearRatio_le_rate
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    ndA6PhysicalLinearRatio B j branch C M ≤
      (4244 / 100 : ℝ) * C * ndA6PhysicalRate B :=
  (ndA6Physical_ratio_rate_packet hTube).2.2.1

/-- The physical moderate-window budget is controlled by the source rate. -/
theorem ndA6PhysicalModerateBudget_le_rate
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    ndA6PhysicalModerateBudget B j branch C M ≤
      16 * ((4244 / 100 : ℝ) * C +
        (4244 / 100 : ℝ) ^ 2 * C ^ 3) * ndA6PhysicalRate B := by
  rcases ndA6Physical_ratio_rate_packet hTube with ⟨_, _, ha, hb⟩
  unfold ndA6PhysicalModerateBudget
  calc
    16 * (ndA6PhysicalLinearRatio B j branch C M +
        ndA6PhysicalCubicRatio B j branch C M) ≤
      16 * ((4244 / 100 : ℝ) * C * ndA6PhysicalRate B +
        (4244 / 100 : ℝ) ^ 2 * C ^ 3 * ndA6PhysicalRate B) :=
      mul_le_mul_of_nonneg_left (add_le_add ha hb) (by norm_num)
    _ = _ := by ring

/-- The complete physical local error is controlled by the source rate. -/
theorem ndA6PhysicalUniformError_le_rate
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    ndA6PhysicalUniformError B j branch C M ≤
      76000 * (C + C ^ 3) * ndA6PhysicalRate B := by
  rcases ndA6Physical_ratio_rate_packet hTube with ⟨hC, hrho, ha, hb⟩
  have hCρ : 0 ≤ C * ndA6PhysicalRate B := mul_nonneg hC hrho
  have hC3ρ : 0 ≤ C ^ 3 * ndA6PhysicalRate B :=
    mul_nonneg (by positivity) hrho
  unfold ndA6PhysicalUniformError
  calc
    44 * ndA6PhysicalLinearRatio B j branch C M +
        42 * ndA6PhysicalCubicRatio B j branch C M ≤
      44 * ((4244 / 100 : ℝ) * C * ndA6PhysicalRate B) +
        42 * ((4244 / 100 : ℝ) ^ 2 * C ^ 3 * ndA6PhysicalRate B) :=
      add_le_add
        (mul_le_mul_of_nonneg_left ha (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = (46684 / 25 : ℝ) * (C * ndA6PhysicalRate B) +
        (47280282 / 625 : ℝ) * (C ^ 3 * ndA6PhysicalRate B) := by ring
    _ ≤ 76000 * (C * ndA6PhysicalRate B) +
        76000 * (C ^ 3 * ndA6PhysicalRate B) :=
      add_le_add
        (mul_le_mul_of_nonneg_right (by norm_num) hCρ)
        (mul_le_mul_of_nonneg_right (by norm_num) hC3ρ)
    _ = _ := by ring

/-- For each fixed admissible `C`, the physical moderate-window guard holds
eventually, uniformly over the band, branch, and shift parameters. -/
theorem eventually_ndA6PhysicalModerate
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in Filter.atTop,
      (300000 : ℝ) ≤ Real.log B ∧
        ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (M : ℝ),
          NDA5InteriorTubeFacts B j branch C M →
            ndA6PhysicalModerateBudget B j branch C M ≤ 1 := by
  let K := 16 * ((4244 / 100 : ℝ) * C +
    (4244 / 100 : ℝ) ^ 2 * C ^ 3)
  have hCpos : 0 < C := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hC
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hsmall : ∀ᶠ B : ℕ in Filter.atTop,
      ndA6PhysicalRate B < 1 / K :=
    tendsto_ndA6PhysicalRate_zero.eventually_lt_const (one_div_pos.mpr hKpos)
  have hlog : ∀ᶠ B : ℕ in Filter.atTop,
      (300000 : ℝ) ≤ Real.log B :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto
        (fun B : ℕ => (B : ℝ)) Filter.atTop Filter.atTop)).eventually_ge_atTop 300000
  filter_upwards [hlog, hsmall] with B hlogB hrate
  refine ⟨hlogB, ?_⟩
  intro branch j M hTube
  calc
    ndA6PhysicalModerateBudget B j branch C M ≤
        K * ndA6PhysicalRate B := by
      simpa [K] using ndA6PhysicalModerateBudget_le_rate hTube
    _ ≤ K * (1 / K) := mul_le_mul_of_nonneg_left hrate.le hKpos.le
    _ = 1 := by field_simp [hKpos.ne']

end

end ND
end Erdos1135
