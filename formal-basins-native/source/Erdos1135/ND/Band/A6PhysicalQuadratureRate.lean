import Erdos1135.ND.Band.A6PhysicalInterior
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A6 Physical Native Quadrature Rate

This finite leaf bounds the checked native strict-fiber quadrature remainder
by the half-power scale consumed by the later fixed-`C` A6 interior wrapper.
-/

namespace Erdos1135
namespace ND

noncomputable section

set_option maxHeartbeats 1500000 in
/-- Under the physical moderate-window guard, the native Gaussian remainder
is already in a uniform inverse-square-root class. -/
theorem ndA6PhysicalGaussianQuadratureError_le_invSqrtN0
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hmoderate : ndA6PhysicalModerateBudget B j branch C M ≤ 1) :
    ndA6PhysicalGaussianQuadratureError B j branch C M ≤
      42 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  classical
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let lo := ndA5TubeLo A W
  let S := ndA6PhysicalCenter B j branch M
  let N : ℝ := Tao.taoSection5N0 B
  let R : ℝ := ndA5TubeRadius W
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [A, W] using hTube.nonempty
  have hWpos : 0 < W := by
    obtain ⟨nu, hnu⟩ := hne
    have hstrict := (Finset.mem_filter.mp hnu).2
    exact (abs_nonneg (ndA5StrictAffineSweep A nu : ℝ)).trans_lt hstrict
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : ndA5TubeLo A W ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hloMem : lo ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr (by simpa [lo] using hlohi)
  have hcell : NDA5InteriorCellFacts B j lo branch C M :=
    hTube.pointwise lo (by simpa [A, W] using hloMem)
  have hloPos : (0 : ℝ) < lo := by exact_mod_cast hTube.lo_pos
  have hsub : lo + Tao.taoSection5M0 B - Tao.taoSection5M0 B = lo := by
    omega
  have hratioLowerRaw := hcell.t2.n0_div_nu_lower
  have hratioUpperRaw := hcell.t2.n0_div_nu_upper
  rw [hsub] at hratioLowerRaw hratioUpperRaw
  have hratioLower : (1374 / 100 : ℝ) ≤ N / (lo : ℝ) := by
    simpa [N] using hratioLowerRaw
  have hratioUpper : N / (lo : ℝ) ≤ (4244 / 100 : ℝ) := by
    simpa [N] using hratioUpperRaw
  have hNpos : 0 < N := by
    have hmul := (le_div_iff₀ hloPos).mp hratioLower
    nlinarith
  have hNnonneg : 0 ≤ N := hNpos.le
  have hS : 0 < S := by
    simpa [S] using
      (ndA6PhysicalCenter_pos_and_close_of_interior hlogB hTube).1
  have hW71 : (71 : ℝ) ≤ W := by
    simpa [W] using
      ndA5TubeWidth_ge_seventy_one hcell.one_half_le_C hlogB
  have hceilReal : (71 : ℝ) ≤ (Nat.ceil W : ℝ) :=
    hW71.trans (Nat.le_ceil W)
  have hceilNat : 71 ≤ Nat.ceil W := by exact_mod_cast hceilReal
  have hRadiusNat : 70 ≤ ndA5TubeRadius W := by
    unfold ndA5TubeRadius
    omega
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < ndA5TubeRadius W by omega)
  have hRadiusSucc : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  have hRlower : W - 1 ≤ R := by
    have h := Nat.le_ceil W
    rw [← hRadiusSucc] at h
    push_cast at h
    simpa [R] using (sub_le_iff_le_add.mpr h)
  have hRW : (70 / 71 : ℝ) * W ≤ R := by
    have hfrac : (70 / 71 : ℝ) * W ≤ W - 1 := by
      nlinarith
    exact hfrac.trans hRlower
  have hcrossing : ndA5StrictAffineSweep A lo = (ndA5TubeRadius W : ℤ) := by
    simpa [A, W, lo] using hTube.endpoint_crossings.1
  have hresidual := ndA5StrictAffineSweep_sub_affine_mem_Ioc A lo
  rw [hcrossing] at hresidual
  have hcenterDiff :
      A - ndA5PhaseDelta * (lo : ℝ) =
        ndA5PhaseDelta * (S - (lo : ℝ)) := by
    dsimp [A, S, ndA6PhysicalCenter]
    field_simp [ndA5PhaseDelta_mem_Ioo.1.ne']
  rw [hcenterDiff] at hresidual
  change 0 < R - ndA5PhaseDelta * (S - (lo : ℝ)) ∧
    R - ndA5PhaseDelta * (S - (lo : ℝ)) ≤ 1 at hresidual
  have hloLtS : (lo : ℝ) < S := by
    have hRlarge : (1 : ℝ) < R := by
      dsimp [R]
      exact_mod_cast (show 1 < ndA5TubeRadius W by omega)
    by_contra hnot
    have hdiff : S - (lo : ℝ) ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    have hmul : ndA5PhaseDelta * (S - (lo : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ndA5PhaseDelta_mem_Ioo.1.le hdiff
    nlinarith [hresidual.2]
  have hlogLe : ndA5LogFourThirds ≤ (1 / 3 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 4 / 3 by norm_num)
    norm_num [ndA5LogFourThirds] at h ⊢
    exact h
  have hcoef :
      (12 / 25 : ℝ) ≤ (4 / 25 : ℝ) / ndA5LogFourThirds := by
    apply (le_div_iff₀ ndA5LogFourThirds_pos).2
    nlinarith
  have hshiftTerm :
      (12 / 25 : ℝ) * W ≤
        ((4 / 25 : ℝ) * W) / ndA5LogFourThirds := by
    calc
      (12 / 25 : ℝ) * W ≤
          ((4 / 25 : ℝ) / ndA5LogFourThirds) * W :=
        mul_le_mul_of_nonneg_right hcoef hWpos.le
      _ = ((4 / 25 : ℝ) * W) / ndA5LogFourThirds := by ring
  have hmargin := ndA5InteriorContainmentMargin hcell.one_half_le_C hlogB
  have hDle : (W + 1) / ndA5PhaseDelta ≤ (63 / 25 : ℝ) * W := by
    nlinarith
  have hcenterW : S - (lo : ℝ) < (63 / 25 : ℝ) * W := by
    have hphysical : lo ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) := by simpa [A, W] using hloMem
    have hclose := abs_natCast_sub_ndA6PhysicalCenter_lt_of_mem_fullTube
      hphysical
    have hsigned : S - (lo : ℝ) ≤ |(lo : ℝ) - S| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact (hsigned.trans_lt hclose).trans_le hDle
  let a := W / (lo : ℝ)
  let b := W ^ 3 / (lo : ℝ) ^ 2
  have hH : 16 * (a + b) ≤ 1 := by
    simpa [ndA6PhysicalModerateBudget, ndA6PhysicalLinearRatio,
      ndA6PhysicalCubicRatio, A, W, lo, a, b] using hmoderate
  have ha : 0 ≤ a := div_nonneg hWpos.le hloPos.le
  have hb : 0 ≤ b := div_nonneg (by positivity) (sq_nonneg _)
  have haSmall : a ≤ 1 / 16 := by nlinarith
  have hSratio : S / (lo : ℝ) < (463 / 400 : ℝ) := by
    have hcenterDiv : (S - (lo : ℝ)) / (lo : ℝ) <
        (63 / 25 : ℝ) * a := by
      apply (div_lt_iff₀ hloPos).2
      dsimp [a]
      field_simp [hloPos.ne']
      nlinarith [hcenterW]
    have hdecomp : S / (lo : ℝ) =
        1 + (S - (lo : ℝ)) / (lo : ℝ) := by
      field_simp [hloPos.ne']
      ring
    rw [hdecomp]
    nlinarith
  have hNSratio : (5496 / 463 : ℝ) < N / S := by
    apply (lt_div_iff₀ hS).2
    have hlowerMul := (le_div_iff₀ hloPos).mp hratioLower
    have hSupper := (div_lt_iff₀ hloPos).mp hSratio
    nlinarith
  have hClower : (1 / 2 : ℝ) ≤ C := hcell.one_half_le_C
  have hloOne : (1 : ℝ) ≤ lo := by exact_mod_cast hTube.lo_pos
  have hlowerMul := (le_div_iff₀ hloPos).mp hratioLower
  have hNgtEight : (8 : ℝ) < N := by nlinarith
  have hlogNpos : 0 < Real.log N := Real.log_pos (by nlinarith)
  have hNsqrt : 0 ≤ N * Real.log N := mul_nonneg hNnonneg hlogNpos.le
  have hWsq : W ^ 2 = C ^ 2 * (N * Real.log N) := by
    dsimp [W, N, ndA5TubeWidth]
    rw [mul_pow, Real.sq_sqrt hNsqrt]
  have hRsq : ((70 / 71 : ℝ) ^ 2) * W ^ 2 ≤ R ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (mul_nonneg (by norm_num) hWpos.le) hRpos.le).2 hRW
  have hexponent : (1 / 2 : ℝ) * Real.log N ≤ R ^ 2 / (4 * S) := by
    have hC2 : (1 / 4 : ℝ) ≤ C ^ 2 := by nlinarith [sq_nonneg (C - 1 / 2)]
    have hNS := (lt_div_iff₀ hS).mp hNSratio
    rw [hWsq] at hRsq
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * S)).2
    nlinarith
  have hlogNGtTwo : (2 : ℝ) < Real.log N := by
    have hlogMono := Real.strictMonoOn_log
      (show (0 : ℝ) < 8 by norm_num) hNpos hNgtEight
    have hlogEight : (2 : ℝ) < Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      have h := Real.log_two_gt_d9
      norm_num at h ⊢
      nlinarith
    exact hlogEight.trans hlogMono
  have hSleRsq : S ≤ R ^ 2 := by
    have honeLog : (1 : ℝ) < (1 / 2 : ℝ) * Real.log N := by
      linarith only [hlogNGtTwo]
    have hone : (1 : ℝ) < R ^ 2 / (4 * S) := honeLog.trans_le hexponent
    have hfourS : 4 * S < R ^ 2 :=
      by
        simpa only [one_mul] using
          (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * S)).mp hone
    have hSfour : S ≤ 4 * S := by linarith only [hS]
    exact hSfour.trans hfourS.le
  have hsqrtSpos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hsqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsqrtSleR : Real.sqrt S ≤ R := by
    rw [Real.sqrt_le_iff]
    exact ⟨hRpos.le, hSleRsq⟩
  have hpeakBasic : ndA6Gaussian S 0 ≤ 1 / Real.sqrt S := by
    rw [ndA6Gaussian_zero]
    have hfourPi : (1 : ℝ) ≤ 4 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hsqrtLe : Real.sqrt S ≤ Real.sqrt (4 * Real.pi * S) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    simpa only [inv_eq_one_div] using
      one_div_le_one_div_of_le hsqrtSpos hsqrtLe
  have hNleS : N ≤ 49 * S := by
    have hupperMul := (div_le_iff₀ hloPos).mp hratioUpper
    nlinarith
  have hsqrtNle : Real.sqrt N ≤ 7 * Real.sqrt S := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    rw [mul_pow, Real.sq_sqrt hS.le]
    norm_num
    exact hNleS
  have hpeak : ndA6Gaussian S 0 ≤ 7 / Real.sqrt N := by
    calc
      ndA6Gaussian S 0 ≤ 1 / Real.sqrt S := hpeakBasic
      _ ≤ 7 / Real.sqrt N := by
        apply (div_le_div_iff₀ hsqrtSpos hsqrtNpos).2
        simpa [mul_comm] using hsqrtNle
  have hexpTail :
      Real.exp (-(R ^ 2 / (4 * S))) ≤ 1 / Real.sqrt N := by
    have hhalf : Real.log N / 2 ≤ R ^ 2 / (4 * S) := by
      simpa [div_eq_mul_inv, mul_comm] using hexponent
    have hmono : Real.exp (-(R ^ 2 / (4 * S))) ≤
        Real.exp (-(Real.log N / 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg hhalf)
    calc
      Real.exp (-(R ^ 2 / (4 * S))) ≤
          Real.exp (-(Real.log N / 2)) := hmono
      _ = 1 / Real.sqrt N := by
        rw [← Real.log_sqrt hNnonneg, Real.exp_neg, Real.exp_log hsqrtNpos]
        simp only [one_div]
  have hgaussR : ndA6Gaussian S R ≤
      (1 / Real.sqrt S) * (1 / Real.sqrt N) := by
    have hprefactor : (Real.sqrt (4 * Real.pi * S))⁻¹ ≤
        1 / Real.sqrt S := by
      simpa only [ndA6Gaussian_zero] using hpeakBasic
    unfold ndA6Gaussian
    exact mul_le_mul hprefactor hexpTail (Real.exp_pos _).le
      (one_div_nonneg.mpr hsqrtSpos.le)
  have hinvDelta : 1 / ndA5PhaseDelta < (63 / 25 : ℝ) := by
    have hscaled : W / ndA5PhaseDelta < (W + 1) / ndA5PhaseDelta := by
      apply (div_lt_div_iff₀ ndA5PhaseDelta_mem_Ioo.1
        ndA5PhaseDelta_mem_Ioo.1).2
      nlinarith
    have hmul : (1 / ndA5PhaseDelta) * W < (63 / 25 : ℝ) * W := by
      calc
        (1 / ndA5PhaseDelta) * W = W / ndA5PhaseDelta := by ring
        _ < (W + 1) / ndA5PhaseDelta := hscaled
        _ ≤ (63 / 25 : ℝ) * W := hDle
    exact lt_of_mul_lt_mul_right hmul hWpos.le
  have hpeakPart :
      (2 + 1 / ndA5PhaseDelta) * ndA6Gaussian S 0 ≤
        (791 / 25 : ℝ) / Real.sqrt N := by
    have hcoefPeak : 2 + 1 / ndA5PhaseDelta ≤ (113 / 25 : ℝ) := by
      linarith
    calc
      (2 + 1 / ndA5PhaseDelta) * ndA6Gaussian S 0 ≤
          (113 / 25 : ℝ) * (7 / Real.sqrt N) :=
        mul_le_mul hcoefPeak hpeak (ndA6Gaussian_nonneg S 0)
          (by positivity)
      _ = (791 / 25 : ℝ) / Real.sqrt N := by ring
  have htailPart :
      (4 * S / (ndA5PhaseDelta * R)) * ndA6Gaussian S R ≤
        (252 / 25 : ℝ) / Real.sqrt N := by
    have hcoefTail : 4 * (1 / ndA5PhaseDelta) ≤ (252 / 25 : ℝ) := by
      linarith
    have hsqrtRatio : Real.sqrt S / R ≤ 1 := by
      exact (div_le_one hRpos).2 hsqrtSleR
    calc
      (4 * S / (ndA5PhaseDelta * R)) * ndA6Gaussian S R ≤
          (4 * (1 / ndA5PhaseDelta)) * (Real.sqrt S / R) *
            (1 / Real.sqrt N) := by
        have hcoefNonneg :
            0 ≤ 4 * S / (ndA5PhaseDelta * R) :=
          div_nonneg
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hS.le)
            (mul_nonneg ndA5PhaseDelta_mem_Ioo.1.le hRpos.le)
        have hmul :
            (4 * S / (ndA5PhaseDelta * R)) * ndA6Gaussian S R ≤
              (4 * S / (ndA5PhaseDelta * R)) *
                ((1 / Real.sqrt S) * (1 / Real.sqrt N)) :=
          mul_le_mul_of_nonneg_left hgaussR hcoefNonneg
        calc
          (4 * S / (ndA5PhaseDelta * R)) * ndA6Gaussian S R ≤
              (4 * S / (ndA5PhaseDelta * R)) *
                ((1 / Real.sqrt S) * (1 / Real.sqrt N)) := hmul
          _ = (4 * (1 / ndA5PhaseDelta)) * (Real.sqrt S / R) *
                (1 / Real.sqrt N) := by
            field_simp [ndA5PhaseDelta_mem_Ioo.1.ne', hRpos.ne',
              hsqrtSpos.ne']
            rw [Real.sq_sqrt hS.le]
      _ ≤ (252 / 25 : ℝ) * 1 * (1 / Real.sqrt N) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoefTail hsqrtRatio (by positivity) (by positivity))
          (one_div_nonneg.mpr hsqrtNpos.le)
      _ = (252 / 25 : ℝ) / Real.sqrt N := by ring
  change
    (2 + 1 / ndA5PhaseDelta) * ndA6Gaussian S 0 +
        (4 * S / (ndA5PhaseDelta * R)) * ndA6Gaussian S R ≤
      42 / Real.sqrt N
  calc
    _ ≤ (791 / 25 : ℝ) / Real.sqrt N +
        (252 / 25 : ℝ) / Real.sqrt N := add_le_add hpeakPart htailPart
    _ ≤ 42 / Real.sqrt N := by
      have hinvSqrt : 0 ≤ 1 / Real.sqrt N := one_div_nonneg.mpr hsqrtNpos.le
      calc
        (791 / 25 : ℝ) / Real.sqrt N +
            (252 / 25 : ℝ) / Real.sqrt N =
          (1043 / 25 : ℝ) * (1 / Real.sqrt N) := by ring
        _ ≤ 42 * (1 / Real.sqrt N) :=
          mul_le_mul_of_nonneg_right (by norm_num) hinvSqrt
        _ = 42 / Real.sqrt N := by ring

end

end ND
end Erdos1135
