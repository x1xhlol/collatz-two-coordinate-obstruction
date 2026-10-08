import Erdos1135.ND.Band.A6PhysicalCenter

/-!
# A6 Physical Moderate Window

This leaf discharges the pointwise eta and zeta guards from one finite scalar
moderate-window hypothesis at the physical lower tube endpoint.  It also
extracts the full local/recentering error as `44*a + 42*b` while preserving
the Gaussian sum.  Fixed-`C` eventuality and Gaussian quadrature remain
separate downstream gates.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- The intrinsic linear moderate-window ratio `W / nu_-`. -/
def ndA6TubeLinearRatio (B : ℕ) (C A : ℝ) : ℝ :=
  ndA5TubeWidth B C /
    (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)

/-- The intrinsic cubic moderate-window ratio `W^3 / nu_-^2`. -/
def ndA6TubeCubicRatio (B : ℕ) (C A : ℝ) : ℝ :=
  ndA5TubeWidth B C ^ 3 /
    (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) ^ 2

/-- The shared finite eta/zeta budget at an arbitrary affine phase. -/
def ndA6TubeModerateBudget (B : ℕ) (C A : ℝ) : ℝ :=
  16 * (ndA6TubeLinearRatio B C A + ndA6TubeCubicRatio B C A)

/-- The uniform local/recentering error at an arbitrary affine phase. -/
def ndA6TubeUniformError (B : ℕ) (C A : ℝ) : ℝ :=
  44 * ndA6TubeLinearRatio B C A +
    42 * ndA6TubeCubicRatio B C A

/-- The physical linear moderate-window ratio `W / nu_-`. -/
def ndA6PhysicalLinearRatio
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) : ℝ :=
  ndA5TubeWidth B C /
    (ndA5TubeLo
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C) : ℝ)

/-- The physical cubic moderate-window ratio `W^3 / nu_-^2`. -/
def ndA6PhysicalCubicRatio
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) : ℝ :=
  ndA5TubeWidth B C ^ 3 /
    (ndA5TubeLo
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C) : ℝ) ^ 2

/-- The one shared finite smallness budget for physical eta and zeta. -/
def ndA6PhysicalModerateBudget
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) : ℝ :=
  16 * (ndA6PhysicalLinearRatio B j branch C M +
    ndA6PhysicalCubicRatio B j branch C M)

/-- The scalar XI.3/XI.4 error retained after Gaussian-weighted extraction. -/
def ndA6PhysicalUniformError
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) : ℝ :=
  44 * ndA6PhysicalLinearRatio B j branch C M +
    42 * ndA6PhysicalCubicRatio B j branch C M

/-- The physical linear ratio is the intrinsic ratio at the physical phase. -/
theorem ndA6PhysicalLinearRatio_eq_tubeLinearRatio
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) :
    ndA6PhysicalLinearRatio B j branch C M =
      ndA6TubeLinearRatio B C
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M) := by rfl

/-- The physical cubic ratio is the intrinsic ratio at the physical phase. -/
theorem ndA6PhysicalCubicRatio_eq_tubeCubicRatio
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) :
    ndA6PhysicalCubicRatio B j branch C M =
      ndA6TubeCubicRatio B C
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M) := by rfl

/-- The physical moderate budget is the intrinsic physical-phase budget. -/
theorem ndA6PhysicalModerateBudget_eq_tubeModerateBudget
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) :
    ndA6PhysicalModerateBudget B j branch C M =
      ndA6TubeModerateBudget B C
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M) := by rfl

/-- The physical uniform error is the intrinsic physical-phase error. -/
theorem ndA6PhysicalUniformError_eq_tubeUniformError
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) :
    ndA6PhysicalUniformError B j branch C M =
      ndA6TubeUniformError B C
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M) := by rfl

set_option maxHeartbeats 500000 in
/-- Under one moderate-window guard, the arbitrary-phase intrinsic XI.3/XI.4
insertion has uniform coefficient `44*a + 42*b`.  Every error summand remains
Gaussian-weighted; no tube-cardinality factor is introduced. -/
theorem abs_ndA5TubeRawMass_sub_sum_tubeCenterGaussian_le_uniform_of_analytic
    {B : ℕ} {C A : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5AnalyticTubeFacts B C A)
    (hmoderate : ndA6TubeModerateBudget B C A ≤ 1) :
    |ndA5TubeRawMass A (ndA5TubeWidth B C) -
        ∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6TubeCenter A)
            (ndA5StrictAffineSweep A nu : ℝ)| ≤
      ndA6TubeUniformError B C A *
        ∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6TubeCenter A)
            (ndA5StrictAffineSweep A nu : ℝ) := by
  classical
  let W := ndA5TubeWidth B C
  let S := ndA6TubeCenter A
  let lo := ndA5TubeLo A W
  let D := (W + 1) / ndA5PhaseDelta
  let a := W / (lo : ℝ)
  let b := W ^ 3 / (lo : ℝ) ^ 2
  let c := 1 / (2 * (lo : ℝ) + 1)
  let E := 44 * a + 42 * b
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [W] using hTube.nonempty
  have hWpos : 0 < W := by
    simpa [W] using hTube.width_pos
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hloNat : 0 < lo := by
    simpa [lo, W] using hTube.lo_pos
  have hloPos : (0 : ℝ) < lo := by exact_mod_cast hloNat
  obtain ⟨hS, _hclose⟩ :=
    ndA6TubeCenter_pos_and_close_of_analytic hlogB hTube
  have hW71 : (71 : ℝ) ≤ W := by
    simpa [W] using
      ndA5TubeWidth_ge_seventy_one hTube.one_half_le_C hlogB
  have hceilReal : (71 : ℝ) ≤ (Nat.ceil W : ℝ) :=
    hW71.trans (Nat.le_ceil W)
  have hceilNat : 71 ≤ Nat.ceil W := by exact_mod_cast hceilReal
  have hRadius : 70 ≤ ndA5TubeRadius W := by
    unfold ndA5TubeRadius
    omega
  have hcrossing :
      ndA5StrictAffineSweep A lo = (ndA5TubeRadius W : ℤ) := by
    simpa [W, lo] using hTube.endpoint_crossings.1
  have hresidual := ndA5StrictAffineSweep_sub_affine_mem_Ioc A lo
  rw [hcrossing] at hresidual
  have hRadiusReal : (1 : ℝ) < ((ndA5TubeRadius W : ℤ) : ℝ) := by
    exact_mod_cast (show 1 < ndA5TubeRadius W by omega)
  have haffinePos :
      0 < A - ndA5PhaseDelta * (lo : ℝ) := by
    linarith [hresidual.2]
  have hcenterDiff :
      A - ndA5PhaseDelta * (lo : ℝ) =
        ndA5PhaseDelta * (S - (lo : ℝ)) := by
    dsimp [S, ndA6TubeCenter]
    field_simp [ndA5PhaseDelta_mem_Ioo.1.ne']
  rw [hcenterDiff] at haffinePos
  have hloLtS : (lo : ℝ) < S := by
    rcases (mul_pos_iff.mp haffinePos) with hpositive | hnegative
    · linarith [hpositive.2]
    · exact (lt_asymm ndA5PhaseDelta_mem_Ioo.1 hnegative.1).elim
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
  have hmargin :
      ((4 / 25 : ℝ) * W) / ndA5LogFourThirds + D ≤ 3 * W := by
    simpa [D, W] using
      ndA5InteriorContainmentMargin hTube.one_half_le_C hlogB
  have hDle : D ≤ (63 / 25 : ℝ) * W := by
    nlinarith
  have hH : 16 * (a + b) ≤ 1 := by
    simpa [ndA6TubeModerateBudget, ndA6TubeLinearRatio,
      ndA6TubeCubicRatio, W, lo, a, b] using hmoderate
  have ha : 0 ≤ a := div_nonneg hWpos.le hloPos.le
  have hb : 0 ≤ b := div_nonneg (by positivity) (sq_nonneg _)
  have hab : a + b ≤ 1 / 16 := by nlinarith
  have hbEq : b = W * a ^ 2 := by
    dsimp [a, b]
    field_simp [hloPos.ne']
  have hbLower : 71 * a ^ 2 ≤ b := by
    rw [hbEq]
    exact mul_le_mul_of_nonneg_right hW71 (sq_nonneg a)
  have haLt : a < 1 / 40 := by
    nlinarith
  have hzetaCap : 2 * a + b < 1 / 9 := by
    nlinarith
  have hloLe : ∀ nu ∈ ndA5FullTube A W, lo ≤ nu := by
    intro nu hnu
    have hIcc : nu ∈ Finset.Icc (ndA5TubeLo A W) (ndA5TubeHi A W) := by
      rw [← hEq]
      exact hnu
    exact (Finset.mem_Icc.mp hIcc).1
  have hpointwise : ∀ nu ∈ ndA5FullTube A W,
      ndA6LocalEta nu
          (Int.natAbs (ndA5StrictAffineSweep A nu)) ≤ 1 ∧
        ndA6GaussianRecenterZeta (nu : ℝ) S
            (ndA5StrictAffineSweep A nu : ℝ) ≤ 1 ∧
        ndA6LocalRelativeError nu
              (Int.natAbs (ndA5StrictAffineSweep A nu)) *
            (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ) S
              (ndA5StrictAffineSweep A nu : ℝ)) +
          2 * ndA6GaussianRecenterZeta (nu : ℝ) S
            (ndA5StrictAffineSweep A nu : ℝ) ≤ E := by
    intro nu hnu
    let d := Int.natAbs (ndA5StrictAffineSweep A nu)
    let x := (ndA5StrictAffineSweep A nu : ℝ)
    let zeta := ndA6GaussianRecenterZeta (nu : ℝ) S x
    have hnuNatPos : 0 < nu := by
      have hraw := (hTube.pointwise nu
        (by simpa [W] using hnu)).t2.nu_pos
      simpa using hraw
    have hnuPos : (0 : ℝ) < nu := by exact_mod_cast hnuNatPos
    have hloNuNat : lo ≤ nu := hloLe nu hnu
    have hloNu : (lo : ℝ) ≤ nu := by exact_mod_cast hloNuNat
    have htube : |x| < W := by
      dsimp [x]
      exact (Finset.mem_filter.mp hnu).2
    have hdCast : (d : ℝ) = |x| := by
      dsimp [d, x]
      rw [Nat.cast_natAbs]
      norm_cast
    have hdLe : (d : ℝ) ≤ W := by
      rw [hdCast]
      exact htube.le
    have hinv : 1 / (nu : ℝ) ≤ 1 / (lo : ℝ) := by
      apply (div_le_div_iff₀ hnuPos hloPos).2
      simpa using hloNu
    have hlinear : (d : ℝ) / (nu : ℝ) ≤ a := by
      calc
        (d : ℝ) / (nu : ℝ) =
            (d : ℝ) * (1 / (nu : ℝ)) := by ring
        _ ≤ W * (1 / (lo : ℝ)) :=
          mul_le_mul hdLe hinv (by positivity) hWpos.le
        _ = a := by dsimp [a]; ring
    have hdCube : (d : ℝ) ^ 3 ≤ W ^ 3 := by
      have hfactor :
          0 ≤ (W - (d : ℝ)) *
            (W ^ 2 + W * (d : ℝ) + (d : ℝ) ^ 2) := by
        exact mul_nonneg (sub_nonneg.mpr hdLe) (by positivity)
      nlinarith
    have hinvSq :
        (1 / (nu : ℝ)) ^ 2 ≤ (1 / (lo : ℝ)) ^ 2 := by
      have hfactor :
          0 ≤ (1 / (lo : ℝ) - 1 / (nu : ℝ)) *
            (1 / (lo : ℝ) + 1 / (nu : ℝ)) := by
        exact mul_nonneg (sub_nonneg.mpr hinv) (by positivity)
      nlinarith
    have hcubic :
        (d : ℝ) ^ 3 / (nu : ℝ) ^ 2 ≤ b := by
      calc
        (d : ℝ) ^ 3 / (nu : ℝ) ^ 2 =
            (d : ℝ) ^ 3 * (1 / (nu : ℝ)) ^ 2 := by ring
        _ ≤ W ^ 3 * (1 / (lo : ℝ)) ^ 2 :=
          mul_le_mul hdCube hinvSq (by positivity) (by positivity)
        _ = b := by dsimp [b]; ring
    have hetaH : ndA6LocalEta nu d ≤ 16 * (a + b) := by
      unfold ndA6LocalEta
      exact mul_le_mul_of_nonneg_left
        (add_le_add hlinear hcubic) (by norm_num)
    have hetaOne : ndA6LocalEta nu d ≤ 1 := hetaH.trans hH
    have hcenterD : |(nu : ℝ) - S| ≤ D := by
      have h := abs_natCast_sub_ndA6TubeCenter_lt_of_mem_fullTube hnu
      change |(nu : ℝ) - S| < D at h
      exact h.le
    have hcenterW : |(nu : ℝ) - S| ≤ (63 / 25 : ℝ) * W :=
      hcenterD.trans hDle
    have hinvS : 1 / S ≤ 1 / (lo : ℝ) := by
      apply (div_le_div_iff₀ hS hloPos).2
      linarith
    have hinvSSq : (1 / S) ^ 2 ≤ (1 / (lo : ℝ)) ^ 2 := by
      exact (sq_le_sq₀ (one_div_nonneg.mpr hS.le)
        (one_div_nonneg.mpr hloPos.le)).2 hinvS
    have hxSq : x ^ 2 ≤ W ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg x) hWpos.le).2 htube.le
      simpa only [sq_abs] using h
    have hfirstZeta :
        (3 / 4 : ℝ) * |(nu : ℝ) - S| / S ≤
          (189 / 100 : ℝ) * a := by
      have hproduct : |(nu : ℝ) - S| * (1 / S) ≤
          ((63 / 25 : ℝ) * W) * (1 / (lo : ℝ)) :=
        mul_le_mul hcenterW hinvS (one_div_nonneg.mpr hS.le)
          (mul_nonneg (by norm_num) hWpos.le)
      calc
        (3 / 4 : ℝ) * |(nu : ℝ) - S| / S =
            (3 / 4 : ℝ) *
              (|(nu : ℝ) - S| * (1 / S)) := by ring
        _ ≤ (3 / 4 : ℝ) *
              (((63 / 25 : ℝ) * W) * (1 / (lo : ℝ))) :=
          mul_le_mul_of_nonneg_left hproduct (by norm_num)
        _ = (189 / 100 : ℝ) * a := by dsimp [a]; ring
    have hxCenter :
        x ^ 2 * |(nu : ℝ) - S| ≤
          W ^ 2 * ((63 / 25 : ℝ) * W) :=
      mul_le_mul hxSq hcenterW (abs_nonneg _) (sq_nonneg _)
    have hsecondZeta :
        (3 / 8 : ℝ) * x ^ 2 * |(nu : ℝ) - S| / S ^ 2 ≤
          (189 / 200 : ℝ) * b := by
      have hproduct :
          (x ^ 2 * |(nu : ℝ) - S|) * (1 / S) ^ 2 ≤
            (W ^ 2 * ((63 / 25 : ℝ) * W)) *
              (1 / (lo : ℝ)) ^ 2 :=
        mul_le_mul hxCenter hinvSSq (sq_nonneg _)
          (mul_nonneg (sq_nonneg _)
            (mul_nonneg (by norm_num) hWpos.le))
      calc
        (3 / 8 : ℝ) * x ^ 2 * |(nu : ℝ) - S| / S ^ 2 =
            (3 / 8 : ℝ) *
              ((x ^ 2 * |(nu : ℝ) - S|) * (1 / S) ^ 2) := by ring
        _ ≤ (3 / 8 : ℝ) *
              ((W ^ 2 * ((63 / 25 : ℝ) * W)) *
                (1 / (lo : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hproduct (by norm_num)
        _ = (189 / 200 : ℝ) * b := by dsimp [b]; ring
    have hzetaAB : zeta ≤ 2 * a + b := by
      change
        (3 / 4 : ℝ) * |(nu : ℝ) - S| / S +
            (3 / 8 : ℝ) * x ^ 2 * |(nu : ℝ) - S| / S ^ 2 ≤
          2 * a + b
      calc
        _ ≤ (189 / 100 : ℝ) * a + (189 / 200 : ℝ) * b :=
          add_le_add hfirstZeta hsecondZeta
        _ ≤ 2 * a + 1 * b :=
          add_le_add
            (mul_le_mul_of_nonneg_right (by norm_num) ha)
            (mul_le_mul_of_nonneg_right (by norm_num) hb)
        _ = 2 * a + b := by ring
    have hzetaNonneg : 0 ≤ zeta := by
      dsimp [zeta]
      exact ndA6GaussianRecenterZeta_nonneg hS
    have hzetaOne : zeta ≤ 1 := by
      have honeNinth : (1 / 9 : ℝ) ≤ 1 := by norm_num
      exact hzetaAB.trans (hzetaCap.le.trans honeNinth)
    have hcentral :
        1 / (((2 * nu + 1 : ℕ) : ℝ)) ≤ c := by
      dsimp [c]
      apply one_div_le_one_div_of_le
        (by positivity : (0 : ℝ) < 2 * (lo : ℝ) + 1)
      have htwice := mul_le_mul_of_nonneg_left hloNu (by norm_num : (0 : ℝ) ≤ 2)
      have hden := add_le_add_right htwice 1
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hden ⊢
      simpa [add_comm] using hden
    have hepsilon : ndA6LocalRelativeError nu d ≤ c + 32 * a + 32 * b := by
      unfold ndA6LocalRelativeError
      calc
        1 / (((2 * nu + 1 : ℕ) : ℝ)) + 2 * ndA6LocalEta nu d ≤
            c + 2 * (16 * (a + b)) :=
          add_le_add hcentral
            (mul_le_mul_of_nonneg_left hetaH (by norm_num))
        _ = c + 32 * a + 32 * b := by ring
    have hcHalf : c ≤ 1 / (2 * (lo : ℝ)) := by
      dsimp [c]
      have htwoloPos : (0 : ℝ) < 2 * (lo : ℝ) :=
        mul_pos (by norm_num) hloPos
      have hplusPos : (0 : ℝ) < 2 * (lo : ℝ) + 1 :=
        add_pos_of_pos_of_nonneg htwoloPos (by norm_num)
      apply (div_le_div_iff₀ hplusPos htwoloPos).2
      have hden : 2 * (lo : ℝ) ≤ 2 * (lo : ℝ) + 1 :=
        le_add_of_nonneg_right (by norm_num)
      simpa only [one_mul] using hden
    have hhalfA : 1 / (2 * (lo : ℝ)) ≤ a / 142 := by
      have hdouble : (142 : ℝ) ≤ 2 * W := by
        calc
          (142 : ℝ) = 2 * 71 := by norm_num
          _ ≤ 2 * W := mul_le_mul_of_nonneg_left hW71 (by norm_num)
      have hcoefW : (1 / 2 : ℝ) ≤ W / 142 := by
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
          (by norm_num : (0 : ℝ) < 142)).2
        simpa [mul_comm] using hdouble
      calc
        1 / (2 * (lo : ℝ)) = (1 / 2) * (1 / (lo : ℝ)) := by ring
        _ ≤ (W / 142) * (1 / (lo : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoefW (one_div_nonneg.mpr hloPos.le)
        _ = a / 142 := by dsimp [a]; ring
    have hcA : c ≤ a / 142 := hcHalf.trans hhalfA
    have hepsilonBoundNonneg : 0 ≤ c + 32 * a + 32 * b := by
      have hcNonneg : 0 ≤ c := by
        dsimp [c]
        positivity
      exact add_nonneg
        (add_nonneg hcNonneg (mul_nonneg (by norm_num) ha))
        (mul_nonneg (by norm_num) hb)
    have hfactor : 1 + 2 * zeta ≤ 11 / 9 := by
      have hzetaNinth : zeta ≤ (1 / 9 : ℝ) := hzetaAB.trans hzetaCap.le
      calc
        1 + 2 * zeta ≤ 1 + 2 * (1 / 9 : ℝ) :=
          by
            simpa [add_comm] using
              add_le_add_left
                (mul_le_mul_of_nonneg_left hzetaNinth
                  (by norm_num : (0 : ℝ) ≤ 2)) 1
        _ = 11 / 9 := by norm_num
    have hweighted :
        ndA6LocalRelativeError nu d * (1 + 2 * zeta) + 2 * zeta ≤
          (11 / 9 : ℝ) * c + (388 / 9 : ℝ) * a +
            (370 / 9 : ℝ) * b := by
      have hproduct := mul_le_mul hepsilon hfactor
        (by positivity : 0 ≤ 1 + 2 * zeta) hepsilonBoundNonneg
      have htwice : 2 * zeta ≤ 2 * (2 * a + b) :=
        mul_le_mul_of_nonneg_left hzetaAB (by norm_num)
      calc
        ndA6LocalRelativeError nu d * (1 + 2 * zeta) + 2 * zeta ≤
            (c + 32 * a + 32 * b) * (11 / 9) +
              2 * (2 * a + b) := add_le_add hproduct htwice
        _ = (11 / 9 : ℝ) * c + (388 / 9 : ℝ) * a +
              (370 / 9 : ℝ) * b := by ring
    have hfinal :
        ndA6LocalRelativeError nu d * (1 + 2 * zeta) + 2 * zeta ≤ E := by
      dsimp [E]
      nlinarith
    simpa [d, x, zeta] using ⟨hetaOne, hzetaOne, hfinal⟩
  have heta : ∀ nu ∈ ndA5FullTube A W,
      ndA6LocalEta nu (Int.natAbs (ndA5StrictAffineSweep A nu)) ≤ 1 := by
    intro nu hnu
    exact (hpointwise nu hnu).1
  have hzeta : ∀ nu ∈ ndA5FullTube A W,
      ndA6GaussianRecenterZeta (nu : ℝ) S
        (ndA5StrictAffineSweep A nu : ℝ) ≤ 1 := by
    intro nu hnu
    exact (hpointwise nu hnu).2.1
  have hmain :=
    abs_ndA5TubeRawMass_sub_sum_tubeCenterGaussian_le_of_analytic
      hlogB hTube (by simpa [W] using heta) (by simpa [W, S] using hzeta)
  calc
    |ndA5TubeRawMass A W -
        ∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)| ≤
        ∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ) *
            (ndA6LocalRelativeError nu
                  (Int.natAbs (ndA5StrictAffineSweep A nu)) *
                (1 + 2 * ndA6GaussianRecenterZeta (nu : ℝ) S
                  (ndA5StrictAffineSweep A nu : ℝ)) +
              2 * ndA6GaussianRecenterZeta (nu : ℝ) S
                (ndA5StrictAffineSweep A nu : ℝ)) := by
      simpa [W, S] using hmain
    _ ≤ ∑ nu ∈ ndA5FullTube A W,
        ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ) * E := by
      apply Finset.sum_le_sum
      intro nu hnu
      exact mul_le_mul_of_nonneg_left (hpointwise nu hnu).2.2
        (ndA6Gaussian_nonneg _ _)
    _ = E * ∑ nu ∈ ndA5FullTube A W,
        ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro nu hnu
      ring
    _ = ndA6TubeUniformError B C A *
        ∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6TubeCenter A)
            (ndA5StrictAffineSweep A nu : ℝ) := by
      simp [E, a, b, W, S, lo, ndA6TubeUniformError,
        ndA6TubeLinearRatio, ndA6TubeCubicRatio]

/-- Physical-phase intrinsic specialization of the uniform analytic theorem. -/
theorem abs_ndA5TubeRawMass_sub_sum_physicalCenterGaussian_le_uniform_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hmoderate : ndA6PhysicalModerateBudget B j branch C M ≤ 1) :
    |ndA5TubeRawMass
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) -
        ∑ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6PhysicalCenter B j branch M)
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)| ≤
      ndA6PhysicalUniformError B j branch C M *
        ∑ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6PhysicalCenter B j branch M)
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) := by
  have hmoderate' : ndA6TubeModerateBudget B C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M) ≤ 1 := by
    simpa only [ndA6PhysicalModerateBudget_eq_tubeModerateBudget] using hmoderate
  simpa only [ndA6PhysicalCenter, ndA6TubeCenter,
      ndA6PhysicalUniformError_eq_tubeUniformError] using
    (abs_ndA5TubeRawMass_sub_sum_tubeCenterGaussian_le_uniform_of_analytic
      hlogB (NDA5InteriorTubeFacts.toAnalytic hTube) hmoderate')

/-- Under one source-shaped moderate-window guard, the complete physical
XI.3/XI.4 insertion has uniform coefficient `44*a + 42*b`.  Every error
summand remains Gaussian-weighted; no tube-cardinality factor is introduced. -/
theorem abs_ndA5BandRawMass_sub_sum_physicalCenterGaussian_le_uniform
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hmoderate : ndA6PhysicalModerateBudget B j branch C M ≤ 1) :
    |ndA5BandRawMass B branch C j M -
        ∑ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6PhysicalCenter B j branch M)
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ)| ≤
      ndA6PhysicalUniformError B j branch C M *
        ∑ nu ∈ ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C),
          ndA6Gaussian (ndA6PhysicalCenter B j branch M)
            (ndA5StrictAffineSweep
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) := by
  rw [ndA5BandRawMass_eq_tubeRawMass_of_interior hTube]
  exact abs_ndA5TubeRawMass_sub_sum_physicalCenterGaussian_le_uniform_of_interior
    hlogB hTube hmoderate

section Canaries

example {a b W : ℝ} (ha : 0 ≤ a)
    (hW : 71 ≤ W) (hbEq : b = W * a ^ 2)
    (hsmall : 16 * (a + b) ≤ 1) :
    a < 1 / 40 ∧ 2 * a + b < 1 / 9 := by
  have hbLower : 71 * a ^ 2 ≤ b := by
    rw [hbEq]
    exact mul_le_mul_of_nonneg_right hW (sq_nonneg a)
  constructor <;> nlinarith

example {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : c ≤ a / 142) :
    (11 / 9 : ℝ) * c + (388 / 9 : ℝ) * a +
        (370 / 9 : ℝ) * b ≤ 44 * a + 42 * b := by
  nlinarith

end Canaries

end

end ND
end Erdos1135
