import Erdos1135.ND.Band.A6PhysicalRate

/-!
# A6 Physical Interior Rate

This leaf absorbs the checked physical local and native-quadrature errors into
one fixed-`C` source rate.  Its final wrapper keeps the literal A5 padding,
band, positivity, and shift guards visible.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The source-shaped physical rate is nonnegative at every schedule value,
including its irrelevant small-value conventions. -/
theorem ndA6PhysicalRate_nonneg (B : ℕ) :
    0 ≤ ndA6PhysicalRate B := by
  unfold ndA6PhysicalRate
  positivity

private theorem ndA6Physical_invSqrt_rate_packet
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (3 : ℝ) < (Tao.taoSection5N0 B : ℝ) ∧
      1 / Real.sqrt (Tao.taoSection5N0 B : ℝ) ≤ ndA6PhysicalRate B := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let lo := ndA5TubeLo A W
  let N : ℝ := Tao.taoSection5N0 B
  let L := Real.log N
  have hloNat : 0 < lo := by
    simpa [A, W, lo] using hTube.lo_pos
  have hlo : (0 : ℝ) < lo := by exact_mod_cast hloNat
  have hloOne : (1 : ℝ) ≤ lo := by exact_mod_cast hloNat
  have hratio := ndA6PhysicalN0_div_tubeLo_mem_Icc hTube
  have hlower : (1374 / 100 : ℝ) ≤ N / (lo : ℝ) := by
    simpa [A, W, lo, N] using hratio.1
  have hmul : (1374 / 100 : ℝ) * (lo : ℝ) ≤ N :=
    (le_div_iff₀ hlo).mp hlower
  have hNthree : (3 : ℝ) < N := by nlinarith
  have hNpos : 0 < N := by linarith
  have hLone : (1 : ℝ) < L := by
    dsimp [L]
    exact (Real.lt_log_iff_exp_lt hNpos).2
      (Real.exp_one_lt_three.trans hNthree)
  have hpowOne : (1 : ℝ) ≤ L ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow hLone.le (by norm_num)
  have hsqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  refine ⟨by simpa [N] using hNthree, ?_⟩
  change 1 / Real.sqrt N ≤ L ^ (3 / 2 : ℝ) / Real.sqrt N
  exact (div_le_div_iff_of_pos_right hsqrtNpos).2 hpowOne

/-- On every checked interior tube, the inverse-square-root quadrature scale
is dominated by the source logarithmic three-halves rate. -/
theorem one_div_sqrt_taoSection5N0_le_ndA6PhysicalRate_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    1 / Real.sqrt (Tao.taoSection5N0 B : ℝ) ≤ ndA6PhysicalRate B :=
  (ndA6Physical_invSqrt_rate_packet hTube).2

set_option maxHeartbeats 500000 in
/-- Deterministic physical A6 interior rate.  The native strict-multiplicity
quadrature term and the local/quadrature cross term are both retained before
the final scalar weakening. -/
theorem abs_ndA5BandRawMass_sub_invDelta_le_physicalRate
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hmoderate : ndA6PhysicalModerateBudget B j branch C M ≤ 1) :
    |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤
      3650000 * (C + C ^ 3) * ndA6PhysicalRate B := by
  classical
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let N : ℝ := Tao.taoSection5N0 B
  let E := ndA6PhysicalUniformError B j branch C M
  let Q := ndA6PhysicalGaussianQuadratureError B j branch C M
  let rho := ndA6PhysicalRate B
  let X := C + C ^ 3
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [A, W] using hTube.nonempty
  obtain ⟨nu, hnu⟩ := hne
  have hWpos : 0 < W := by
    exact (abs_nonneg (ndA5StrictAffineSweep A nu : ℝ)).trans_lt
      (Finset.mem_filter.mp hnu).2
  have hcell : NDA5InteriorCellFacts B j nu branch C M :=
    hTube.pointwise nu (by simpa [A, W] using hnu)
  have hC : (1 / 2 : ℝ) ≤ C := hcell.one_half_le_C
  have hC0 : 0 ≤ C := by linarith
  have hlinear0 : 0 ≤ ndA6PhysicalLinearRatio B j branch C M := by
    unfold ndA6PhysicalLinearRatio
    exact div_nonneg hWpos.le (Nat.cast_nonneg _)
  have hcubic0 : 0 ≤ ndA6PhysicalCubicRatio B j branch C M := by
    unfold ndA6PhysicalCubicRatio
    exact div_nonneg (by positivity) (sq_nonneg _)
  have hE0 : 0 ≤ E := by
    dsimp [E, ndA6PhysicalUniformError]
    exact add_nonneg
      (mul_nonneg (by norm_num) hlinear0)
      (mul_nonneg (by norm_num) hcubic0)
  have hrho0 : 0 ≤ rho := by
    simpa [rho] using ndA6PhysicalRate_nonneg B
  have hinner : 0 ≤ C ^ 2 + C / 2 + 5 / 4 := by positivity
  have hfactor := mul_nonneg (sub_nonneg.mpr hC) hinner
  have hXlower : (5 / 8 : ℝ) ≤ X := by
    dsimp [X]
    nlinarith
  rcases ndA6Physical_invSqrt_rate_packet hTube with ⟨hNthree, hinvRate⟩
  have hNthree' : (3 : ℝ) < N := by simpa [N] using hNthree
  have hNpos : 0 < N := by linarith
  have hsqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsqrtNone : (1 : ℝ) ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]
    linarith
  have hinvOne : 1 / Real.sqrt N ≤ (1 : ℝ) := by
    simpa only [one_div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsqrtNone
  have hQsqrt : Q ≤ 42 / Real.sqrt N := by
    simpa [Q, N] using
      ndA6PhysicalGaussianQuadratureError_le_invSqrtN0
        hlogB hTube hmoderate
  have hQrate : Q ≤ 42 * rho := by
    calc
      Q ≤ 42 / Real.sqrt N := hQsqrt
      _ = 42 * (1 / Real.sqrt N) := by ring
      _ ≤ 42 * rho := by
        apply mul_le_mul_of_nonneg_left
        · simpa [N, rho] using hinvRate
        · norm_num
  have hQfortyTwo : Q ≤ 42 := by
    calc
      Q ≤ 42 / Real.sqrt N := hQsqrt
      _ = 42 * (1 / Real.sqrt N) := by ring
      _ ≤ 42 * 1 := mul_le_mul_of_nonneg_left hinvOne (by norm_num)
      _ = 42 := by ring
  have hmargin :
      ((4 / 25 : ℝ) * W) / ndA5LogFourThirds +
          (W + 1) / ndA5PhaseDelta ≤ 3 * W := by
    simpa [W] using ndA5InteriorContainmentMargin hC hlogB
  have hfirst0 :
      0 ≤ ((4 / 25 : ℝ) * W) / ndA5LogFourThirds :=
    div_nonneg
      (mul_nonneg (by norm_num) hWpos.le)
      ndA5LogFourThirds_pos.le
  have hwide : (W + 1) / ndA5PhaseDelta ≤ 3 * W := by
    linarith
  have hscaled : W / ndA5PhaseDelta < (W + 1) / ndA5PhaseDelta := by
    exact (div_lt_div_iff_of_pos_right ndA5PhaseDelta_mem_Ioo.1).2
      (by linarith)
  have hinvDelta : 1 / ndA5PhaseDelta < (3 : ℝ) := by
    have hmul : (1 / ndA5PhaseDelta) * W < 3 * W := by
      calc
        (1 / ndA5PhaseDelta) * W = W / ndA5PhaseDelta := by ring
        _ < (W + 1) / ndA5PhaseDelta := hscaled
        _ ≤ 3 * W := hwide
    exact lt_of_mul_lt_mul_right hmul hWpos.le
  have hbracket : 1 / ndA5PhaseDelta + Q ≤ 48 := by
    linarith
  have hErate : E ≤ 76000 * X * rho := by
    simpa [E, X, rho] using ndA6PhysicalUniformError_le_rate hTube
  have hEbracket :
      E * (1 / ndA5PhaseDelta + Q) ≤ 3648000 * X * rho := by
    calc
      E * (1 / ndA5PhaseDelta + Q) ≤ E * 48 :=
        mul_le_mul_of_nonneg_left hbracket hE0
      _ ≤ (76000 * X * rho) * 48 :=
        mul_le_mul_of_nonneg_right hErate (by norm_num)
      _ = 3648000 * X * rho := by ring
  have hfinite :
      |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤
        E * (1 / ndA5PhaseDelta + Q) + Q := by
    simpa [E, Q] using
      abs_ndA5BandRawMass_sub_invDelta_le_of_physicalModerate
        hlogB hTube hmoderate
  have hcoef : 3648000 * X + 42 ≤ 3650000 * X := by
    nlinarith
  calc
    |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤
        E * (1 / ndA5PhaseDelta + Q) + Q := hfinite
    _ ≤ 3648000 * X * rho + 42 * rho :=
      add_le_add hEbracket hQrate
    _ = (3648000 * X + 42) * rho := by ring
    _ ≤ 3650000 * X * rho :=
      mul_le_mul_of_nonneg_right hcoef hrho0
    _ = 3650000 * (C + C ^ 3) * ndA6PhysicalRate B := by
      rfl

/-- Literal source-guard A6 interior consumer.  The padding guard remains an
implication premise; its own eventual producer belongs to A5. -/
theorem eventually_a6PhysicalInterior_of_sourceGuards
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in Filter.atTop,
      3 * ndA5TubeWidth B C ≤
          (33 / 500000 : ℝ) * Real.log B →
        ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ),
          j < ndA5BandCount B branch →
            ∀ M : ℝ, 0 < M →
              |ndA5InteriorShift B M| ≤
                  (4 / 25 : ℝ) * ndA5TubeWidth B C →
                |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤
                  3650000 * (C + C ^ 3) * ndA6PhysicalRate B := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ),
    eventually_ndA6PhysicalModerate C hC] with B hB hlarge
  intro hpadding branch j hj M hM hshift
  have hTube : NDA5InteriorTubeFacts B j branch C M :=
    ndA5InteriorTubeFacts_of_guards
      hB hlarge.1 hC hM hpadding hshift hj
  exact abs_ndA5BandRawMass_sub_invDelta_le_physicalRate
    hlarge.1 hTube (hlarge.2 branch j M hTube)

end

end ND
end Erdos1135
