import Erdos1135.ND.Band.A5Regularity
import Erdos1135.ND.Band.A5StrictBandLevels
import Erdos1135.ND.Band.A6StrictMultiplicity

/-!
# A5 First-Shift Raw Comparison

This leaf starts the zero-extended two-profile L1 gate.  Its first endpoint is
the pointwise comparison on the common support of the phases `A` and `A + 1`.
The comparison changes the physical endpoint level while keeping the outer
natural index fixed; it is therefore distinct from the existing consecutive-
index regularity theorem.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Translating the phase by one translates the signed strict affine sweep by
one at the same natural index. -/
theorem ndA5StrictAffineSweep_add_one (A : ℝ) (nu : ℕ) :
    ndA5StrictAffineSweep (A + 1) nu =
      ndA5StrictAffineSweep A nu + 1 := by
  have htranslate := ndA5PhysicalLevelInt_add_nat A nu 1
  norm_num at htranslate
  have hbase :=
    ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A nu
  have hshift :=
    ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep (A + 1) nu
  omega

/-- On the common support, the first-shift raw profile differs from the base
profile by at most the same relative tube error used in A5 regularity.

Only the base analytic packet is needed: its positive signed endpoint remains
positive after translation, while explicit shifted-tube membership supplies
the second raw support indicator. -/
theorem abs_ndA5RawQ_add_one_sub_le_two_mul_width_div_of_analytic
    {B nu : ℕ} {C A : ℝ}
    (hTube0 : NDA5AnalyticTubeFacts B C A)
    (hnu0 : nu ∈ ndA5FullTube A (ndA5TubeWidth B C))
    (hnu1 : nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C)) :
    |ndA5RawQ (A + 1) (ndA5TubeWidth B C) nu -
        ndA5RawQ A (ndA5TubeWidth B C) nu| ≤
      2 * (ndA5TubeWidth B C / (nu : ℝ)) *
        ndA5RawQ A (ndA5TubeWidth B C) nu := by
  let W := ndA5TubeWidth B C
  let L := ndA5PhysicalLevel A nu
  let q := ndA5RawQ A W nu
  have hcell0 : NDA5AnalyticCellFacts B nu C A :=
    hTube0.pointwise nu (by simpa [W] using hnu0)
  have hnuPos : 0 < nu := by simpa using hcell0.t2.nu_pos
  have hnuReal : (0 : ℝ) < nu := by exact_mod_cast hnuPos
  have hqNonneg : 0 ≤ q := ndA5RawQ_nonneg A W nu
  have hWone : (1 : ℝ) < W := by
    simpa [W] using one_lt_ndA5TubeWidth_of_analytic hTube0
  have hWNonneg : (0 : ℝ) ≤ W := by linarith
  have hWle : W ≤ (nu : ℝ) / 8 := by
    simpa [W] using hcell0.t2.width_le_nu_div_eight
  have hlevelInt := ndA5PhysicalLevelInt_add_nat A nu 1
  norm_num at hlevelInt
  have hlevelNat :
      ndA5PhysicalLevel (A + 1) nu = L + 1 := by
    have hshiftPos : 0 ≤ ndA5PhysicalLevelInt (A + 1) nu := by
      have hbasePos := hcell0.level.int_pos
      rw [hlevelInt]
      omega
    have hshiftCast :
        (ndA5PhysicalLevel (A + 1) nu : ℤ) =
          ndA5PhysicalLevelInt (A + 1) nu := by
      unfold ndA5PhysicalLevel
      exact Int.toNat_of_nonneg hshiftPos
    have hcast :
        (ndA5PhysicalLevel (A + 1) nu : ℤ) =
          (L : ℤ) + 1 := by
      rw [hshiftCast, hlevelInt,
        ← hcell0.level.nat_cast_eq]
    exact_mod_cast hcast
  have hrawRec :
      ndA5RawQ (A + 1) W nu =
        q * (L : ℝ) / (2 * ((L - nu + 1 : ℕ) : ℝ)) := by
    dsimp [q]
    rw [ndA5RawQ_of_mem (by simpa [W] using hnu1),
      ndA5RawQ_of_mem (by simpa [W] using hnu0), hlevelNat]
    exact ndGeom2EndpointMass_succ hnuPos hcell0.level.nu_le_nat
  have hdInt :
      (L : ℤ) - 2 * (nu : ℤ) = ndA5StrictAffineSweep A nu := by
    dsimp [L]
    rw [hcell0.level.nat_cast_eq]
    exact ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A nu
  have hdReal := congrArg (fun z : ℤ => (z : ℝ)) hdInt
  push_cast at hdReal
  have htube : |(ndA5StrictAffineSweep A nu : ℝ)| < W :=
    (Finset.mem_filter.mp hnu0).2
  have hdev : |(L : ℝ) - 2 * (nu : ℝ)| < W := by
    rw [hdReal]
    exact htube
  let x : ℝ := (L : ℝ) - 2 * (nu : ℝ)
  let g : ℝ := (L : ℝ) - (nu : ℝ) + 1
  have hx : |x| < W := by simpa [x] using hdev
  have hxBounds := abs_lt.mp hx
  have hLnu : nu ≤ L := by simpa [L] using hcell0.level.nu_le_nat
  have hgCast : ((L - nu + 1 : ℕ) : ℝ) = g := by
    rw [Nat.cast_add, Nat.cast_sub hLnu]
    push_cast
    rfl
  have hgPos : 0 < g := by
    dsimp [g]
    have hLnuReal : (nu : ℝ) ≤ L := by exact_mod_cast hLnu
    linarith
  have hdefect :
      (L : ℝ) / (2 * ((L - nu + 1 : ℕ) : ℝ)) - 1 =
        (-x - 2) / (2 * g) := by
    rw [hgCast]
    field_simp [hgPos.ne']
    dsimp [x, g]
    ring
  have habsNum : |-x - 2| ≤ |x| + 2 := by
    simpa [sub_eq_add_neg] using abs_add_le (-x) (-2)
  have habsNumLt : |-x - 2| < W + 2 :=
    habsNum.trans_lt (by linarith)
  have hnEightW : 8 * W ≤ (nu : ℝ) := by nlinarith
  have hcoef : 0 ≤ 3 * W - 2 := by linarith
  have hnCoef :
      (8 * W) * (3 * W - 2) ≤ (nu : ℝ) * (3 * W - 2) :=
    mul_le_mul_of_nonneg_right hnEightW hcoef
  have hWPos : 0 < W := by linarith
  have hxMul : -W * W < W * x := by
    have h := mul_lt_mul_of_pos_left hxBounds.1 hWPos
    nlinarith
  have hspan :
      (W + 2) * (nu : ℝ) ≤ 4 * W * g := by
    dsimp [x, g] at hxMul ⊢
    nlinarith
  have hnumScaled :
      |-x - 2| * (nu : ℝ) ≤ 4 * W * g := by
    calc
      |-x - 2| * (nu : ℝ) ≤ (W + 2) * (nu : ℝ) :=
        mul_le_mul_of_nonneg_right habsNumLt.le hnuReal.le
      _ ≤ 4 * W * g := hspan
  have hratio :
      |(L : ℝ) / (2 * ((L - nu + 1 : ℕ) : ℝ)) - 1| ≤
        2 * (W / (nu : ℝ)) := by
    rw [hdefect, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * g)]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * g)).2
    rw [show 2 * (W / (nu : ℝ)) * (2 * g) =
      (4 * W * g) / (nu : ℝ) by ring]
    exact (le_div_iff₀ hnuReal).2 hnumScaled
  have hfactor :
      q * (L : ℝ) / (2 * ((L - nu + 1 : ℕ) : ℝ)) - q =
        q * ((L : ℝ) / (2 * ((L - nu + 1 : ℕ) : ℝ)) - 1) := by
    ring
  change |ndA5RawQ (A + 1) W nu - q| ≤
    2 * (W / (nu : ℝ)) * q
  rw [hrawRec, hfactor, abs_mul, abs_of_nonneg hqNonneg]
  calc
    q * |(L : ℝ) / (2 * ((L - nu + 1 : ℕ) : ℝ)) - 1| ≤
        q * (2 * (W / (nu : ℝ))) :=
      mul_le_mul_of_nonneg_left hratio hqNonneg
    _ = 2 * (W / (nu : ℝ)) * q := by ring

private theorem ndA5TubeRadius_lt_shiftedComparison
    {W : ℝ} (hW : 0 < W) :
    (ndA5TubeRadius W : ℝ) < W := by
  have hceil : 0 < Nat.ceil W := Nat.ceil_pos.mpr hW
  have hradius : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  have h := Nat.ceil_lt_add_one hW.le
  rw [← hradius] at h
  push_cast at h
  linarith

private theorem ndA5TubeWidth_le_radius_add_one_shiftedComparison
    {W : ℝ} (hW : 0 < W) :
    W ≤ (ndA5TubeRadius W : ℝ) + 1 := by
  have hceil : 0 < Nat.ceil W := Nat.ceil_pos.mpr hW
  have hradius : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  have h := Nat.le_ceil W
  rw [← hradius] at h
  push_cast at h
  exact h

/-- The indices lost when the phase is translated by one are exactly the
top signed-radius fiber of the base tube. -/
theorem ndA5FullTube_sdiff_add_one_eq_topFiber
    {A W : ℝ} (hW : 0 < W) :
    ndA5FullTube A W \ ndA5FullTube (A + 1) W =
      (ndA5FullTube A W).filter (fun nu =>
        ndA5StrictAffineSweep A nu = (ndA5TubeRadius W : ℤ)) := by
  classical
  let R := ndA5TubeRadius W
  have hRlt : (R : ℝ) < W := by
    simpa [R] using ndA5TubeRadius_lt_shiftedComparison hW
  have hWle : W ≤ (R : ℝ) + 1 := by
    simpa [R] using ndA5TubeWidth_le_radius_add_one_shiftedComparison hW
  ext nu
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hnu0, hnu1not⟩
    have hbounds := Finset.mem_Icc.mp
      (ndA5StrictAffineSweep_mem_Icc_of_mem_fullTube hW hnu0)
    have hlevel :
        ndA5StrictAffineSweep A nu = (R : ℤ) := by
      by_contra hne
      have hplusBounds :
          -(R : ℤ) ≤ ndA5StrictAffineSweep A nu + 1 ∧
            ndA5StrictAffineSweep A nu + 1 ≤ (R : ℤ) := by
        omega
      apply hnu1not
      apply (mem_ndA5FullTube_iff hW (A + 1) nu).mpr
      rw [ndA5StrictAffineSweep_add_one, abs_lt]
      have hlower :
          -((R : ℝ)) ≤
            (ndA5StrictAffineSweep A nu + 1 : ℤ) := by
        exact_mod_cast hplusBounds.1
      have hupper :
          ((ndA5StrictAffineSweep A nu + 1 : ℤ) : ℝ) ≤ R := by
        exact_mod_cast hplusBounds.2
      constructor <;> linarith
    exact ⟨hnu0, hlevel⟩
  · rintro ⟨hnu0, hlevel⟩
    refine ⟨hnu0, ?_⟩
    intro hnu1
    have htube := (mem_ndA5FullTube_iff hW (A + 1) nu).mp hnu1
    rw [ndA5StrictAffineSweep_add_one, hlevel] at htube
    have hnonneg :
        (0 : ℝ) ≤ ((R : ℤ) + 1 : ℤ) := by positivity
    rw [abs_of_nonneg hnonneg] at htube
    push_cast at htube
    linarith

/-- The indices gained when the phase is translated by one are exactly the
bottom signed-radius fiber of the shifted tube. -/
theorem ndA5FullTube_add_one_sdiff_eq_bottomFiber
    {A W : ℝ} (hW : 0 < W) :
    ndA5FullTube (A + 1) W \ ndA5FullTube A W =
      (ndA5FullTube (A + 1) W).filter (fun nu =>
        ndA5StrictAffineSweep (A + 1) nu =
          -(ndA5TubeRadius W : ℤ)) := by
  classical
  let R := ndA5TubeRadius W
  have hRlt : (R : ℝ) < W := by
    simpa [R] using ndA5TubeRadius_lt_shiftedComparison hW
  have hWle : W ≤ (R : ℝ) + 1 := by
    simpa [R] using ndA5TubeWidth_le_radius_add_one_shiftedComparison hW
  ext nu
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hnu1, hnu0not⟩
    have hbounds := Finset.mem_Icc.mp
      (ndA5StrictAffineSweep_mem_Icc_of_mem_fullTube hW hnu1)
    have hlevel :
        ndA5StrictAffineSweep (A + 1) nu = -(R : ℤ) := by
      by_contra hne
      have hminusBounds :
          -(R : ℤ) ≤ ndA5StrictAffineSweep (A + 1) nu - 1 ∧
            ndA5StrictAffineSweep (A + 1) nu - 1 ≤ (R : ℤ) := by
        omega
      apply hnu0not
      apply (mem_ndA5FullTube_iff hW A nu).mpr
      have htranslate := ndA5StrictAffineSweep_add_one A nu
      have hbase :
          ndA5StrictAffineSweep A nu =
            ndA5StrictAffineSweep (A + 1) nu - 1 := by
        omega
      rw [hbase, abs_lt]
      have hlower :
          -((R : ℝ)) ≤
            (ndA5StrictAffineSweep (A + 1) nu - 1 : ℤ) := by
        exact_mod_cast hminusBounds.1
      have hupper :
          ((ndA5StrictAffineSweep (A + 1) nu - 1 : ℤ) : ℝ) ≤ R := by
        exact_mod_cast hminusBounds.2
      constructor <;> linarith
    exact ⟨hnu1, hlevel⟩
  · rintro ⟨hnu1, hlevel⟩
    refine ⟨hnu1, ?_⟩
    intro hnu0
    have htube := (mem_ndA5FullTube_iff hW A nu).mp hnu0
    have htranslate := ndA5StrictAffineSweep_add_one A nu
    rw [hlevel] at htranslate
    have hbase : ndA5StrictAffineSweep A nu = -(R : ℤ) - 1 := by
      omega
    rw [hbase] at htube
    have hnonpos :
        (((-(R : ℤ) - 1 : ℤ) : ℝ)) ≤ 0 := by
      push_cast
      have hRnonneg : (0 : ℝ) ≤ R := by positivity
      linarith
    rw [abs_of_nonpos hnonpos] at htube
    push_cast at htube
    linarith

private theorem ndA5PhaseDelta_inv_lt_three_of_guards
    {B : ℕ} {C : ℝ} (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B) :
    1 / ndA5PhaseDelta < (3 : ℝ) := by
  let W := ndA5TubeWidth B C
  have hWlower : (71 : ℝ) ≤ W := by
    simpa [W] using ndA5TubeWidth_ge_seventy_one hC hlogB
  have hWpos : 0 < W := by linarith
  have hmargin := ndA5InteriorContainmentMargin hC hlogB
  have hfirstNonneg :
      0 ≤ ((4 / 25 : ℝ) * W) / ndA5LogFourThirds :=
    div_nonneg (mul_nonneg (by norm_num) hWpos.le)
      ndA5LogFourThirds_pos.le
  have hwide : (W + 1) / ndA5PhaseDelta ≤ 3 * W := by
    simpa [W] using (show
      (W + 1) / ndA5PhaseDelta ≤ 3 * W by
        have : ((4 / 25 : ℝ) * W) / ndA5LogFourThirds +
            (W + 1) / ndA5PhaseDelta ≤ 3 * W := by
          simpa [W] using hmargin
        linarith)
  have hscaled : W / ndA5PhaseDelta < (W + 1) / ndA5PhaseDelta :=
    (div_lt_div_iff_of_pos_right ndA5PhaseDelta_mem_Ioo.1).2 (by linarith)
  have hmul : (1 / ndA5PhaseDelta) * W < 3 * W := by
    calc
      (1 / ndA5PhaseDelta) * W = W / ndA5PhaseDelta := by ring
      _ < (W + 1) / ndA5PhaseDelta := hscaled
      _ ≤ 3 * W := hwide
  exact lt_of_mul_lt_mul_right hmul hWpos.le

private theorem ndA6StrictLevelMultiplicity_le_three_shiftedComparison
    {A W : ℝ} (hW : 0 < W) (hlo : 0 < ndA5TubeLo A W)
    (hinv : 1 / ndA5PhaseDelta < (3 : ℝ)) {d : ℤ}
    (hd : d ∈ Finset.Icc (-(ndA5TubeRadius W : ℤ))
      (ndA5TubeRadius W : ℤ)) :
    ndA6StrictLevelMultiplicity A W d ≤ 3 := by
  let lower : ℝ := (A - (d : ℝ)) / ndA5PhaseDelta
  let upper : ℝ := (A - (d : ℝ) + 1) / ndA5PhaseDelta
  have hmult :=
    ndA6StrictLevelMultiplicity_eq_floor_sub_floor hW hlo hd
  have hspan : upper - lower = 1 / ndA5PhaseDelta := by
    dsimp [upper, lower]
    ring
  have hupperFloor := Int.floor_le upper
  have hlowerCeil := Int.lt_floor_add_one lower
  push_cast at hupperFloor hlowerCeil
  have hdiffReal :
      (Int.floor upper : ℝ) - (Int.floor lower : ℝ) < 4 := by
    linarith
  have hdiffInt : Int.floor upper - Int.floor lower < (4 : ℤ) := by
    exact_mod_cast hdiffReal
  change ndA6StrictLevelMultiplicity A W d ≤ 3
  dsimp [upper, lower] at hdiffInt
  omega

/-- At most three base-tube indices are lost under the first phase shift. -/
theorem card_ndA5FullTube_sdiff_add_one_le_three_of_analytic
    {B : ℕ} {C A : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube0 : NDA5AnalyticTubeFacts B C A) :
    (ndA5FullTube A (ndA5TubeWidth B C) \
      ndA5FullTube (A + 1) (ndA5TubeWidth B C)).card ≤ 3 := by
  let W := ndA5TubeWidth B C
  have hinv := ndA5PhaseDelta_inv_lt_three_of_guards
    hTube0.one_half_le_C hlogB
  rw [ndA5FullTube_sdiff_add_one_eq_topFiber hTube0.width_pos]
  apply ndA6StrictLevelMultiplicity_le_three_shiftedComparison
    hTube0.width_pos hTube0.lo_pos hinv
  simp

/-- At most three shifted-tube indices are gained under the first phase
shift. -/
theorem card_ndA5FullTube_add_one_sdiff_le_three_of_analytic
    {B : ℕ} {C A : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube1 : NDA5AnalyticTubeFacts B C (A + 1)) :
    (ndA5FullTube (A + 1) (ndA5TubeWidth B C) \
      ndA5FullTube A (ndA5TubeWidth B C)).card ≤ 3 := by
  let W := ndA5TubeWidth B C
  have hinv := ndA5PhaseDelta_inv_lt_three_of_guards
    hTube1.one_half_le_C hlogB
  rw [ndA5FullTube_add_one_sdiff_eq_bottomFiber hTube1.width_pos]
  apply ndA6StrictLevelMultiplicity_le_three_shiftedComparison
    hTube1.width_pos hTube1.lo_pos hinv
  simp

/-- Every raw atom in an analytic tube is at most four inverse square roots
of the common Section 5 scale.  The safe constant four follows from the
checked ratio `N0 / nu ≤ 42.44 < 49`. -/
theorem ndA5RawQ_le_four_div_sqrt_taoSection5N0_of_analytic
    {B nu : ℕ} {C A : ℝ}
    (hTube : NDA5AnalyticTubeFacts B C A)
    (hnu : nu ∈ ndA5FullTube A (ndA5TubeWidth B C)) :
    ndA5RawQ A (ndA5TubeWidth B C) nu ≤
      4 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  let W := ndA5TubeWidth B C
  let N : ℝ := Tao.taoSection5N0 B
  have hcell : NDA5AnalyticCellFacts B nu C A :=
    hTube.pointwise nu (by simpa [W] using hnu)
  have hnuPos : 0 < nu := by simpa using hcell.t2.nu_pos
  have hnuReal : (0 : ℝ) < nu := by exact_mod_cast hnuPos
  have hraw : ndA5RawQ A W nu ≤
      1 / (2 * Real.sqrt (nu : ℝ)) := by
    rw [ndA5RawQ_of_mem (by simpa [W] using hnu)]
    exact ndGeom2EndpointMass_le_one_div_two_mul_sqrt
      hnuPos hcell.level.nu_le_nat
  have hsub :
      nu + Tao.taoSection5M0 B - Tao.taoSection5M0 B = nu := by
    omega
  have hratioUpper := hcell.t2.n0_div_nu_upper
  have hratioLower := hcell.t2.n0_div_nu_lower
  rw [hsub] at hratioUpper hratioLower
  have hNle : N ≤ 49 * (nu : ℝ) := by
    apply (div_le_iff₀ hnuReal).mp
    calc
      N / (nu : ℝ) ≤ (4244 / 100 : ℝ) := by
        simpa [N] using hratioUpper
      _ ≤ 49 := by norm_num
  have hNlower : (1374 / 100 : ℝ) * (nu : ℝ) ≤ N := by
    apply (le_div_iff₀ hnuReal).mp
    simpa [N] using hratioLower
  have hNpos : 0 < N := by nlinarith
  have hsqrtLe : Real.sqrt N ≤ 7 * Real.sqrt (nu : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hnuReal.le]
  have hfrac :
      1 / (2 * Real.sqrt (nu : ℝ)) ≤ 4 / Real.sqrt N := by
    apply (div_le_div_iff₀ (by positivity :
      (0 : ℝ) < 2 * Real.sqrt (nu : ℝ))
      (Real.sqrt_pos.2 hNpos)).2
    nlinarith [Real.sqrt_nonneg (nu : ℝ)]
  exact hraw.trans (by simpa [W, N] using hfrac)

/-- The two zero-extended raw profiles at phases `A` and `A + 1` are close in
full L1.  The common support is paid by the base raw mass, while the two
three-point endpoint fibers contribute the explicit `24 / sqrt N0` edge
term. -/
theorem sum_abs_ndA5RawQ_add_one_sub_le_of_analytic
    {B : ℕ} {C A : ℝ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube0 : NDA5AnalyticTubeFacts B C A)
    (hTube1 : NDA5AnalyticTubeFacts B C (A + 1)) :
    (∑ nu ∈
        ndA5FullTube A (ndA5TubeWidth B C) ∪
          ndA5FullTube (A + 1) (ndA5TubeWidth B C),
      |ndA5RawQ (A + 1) (ndA5TubeWidth B C) nu -
        ndA5RawQ A (ndA5TubeWidth B C) nu|) ≤
      2 * (ndA5TubeWidth B C /
          (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) *
        ndA5TubeRawMass A (ndA5TubeWidth B C) +
      24 / Real.sqrt (Tao.taoSection5N0 B : ℝ) := by
  classical
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let I1 := ndA5FullTube (A + 1) W
  let common := I0 ∩ I1
  let left := I0 \ I1
  let right := I1 \ I0
  let lo := ndA5TubeLo A W
  let Z0 := ndA5TubeRawMass A W
  let N : ℝ := Tao.taoSection5N0 B
  let f : ℕ → ℝ := fun nu =>
    |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu|
  have hWpos : 0 < W := by simpa [W] using hTube0.width_pos
  have hWnonneg : 0 ≤ W := hWpos.le
  have hloPos : 0 < lo := by simpa [lo, W] using hTube0.lo_pos
  have hloReal : (0 : ℝ) < lo := by exact_mod_cast hloPos
  have hI0eq : I0 = Finset.Icc lo (ndA5TubeHi A W) := by
    simpa [I0, lo, W] using
      ndA5FullTube_eq_Icc hTube0.width_pos hTube0.nonempty
  have hpartition :
      I0 ∪ I1 = (common ∪ left) ∪ right := by
    ext nu
    simp only [I0, I1, common, left, right, Finset.mem_union,
      Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisjCommonLeft : Disjoint common left := by
    apply Finset.disjoint_left.mpr
    intro nu hcommon hleft
    have hc := Finset.mem_inter.mp hcommon
    have hl := Finset.mem_sdiff.mp hleft
    exact hl.2 hc.2
  have hdisjRight : Disjoint (common ∪ left) right := by
    apply Finset.disjoint_left.mpr
    intro nu hcl hright
    have hr := Finset.mem_sdiff.mp hright
    rcases Finset.mem_union.mp hcl with hc | hl
    · exact hr.2 (Finset.mem_inter.mp hc).1
    · exact hr.2 (Finset.mem_sdiff.mp hl).1
  have hcommonPoint : ∀ nu ∈ common,
      f nu ≤ 2 * (W / (lo : ℝ)) * ndA5RawQ A W nu := by
    intro nu hnu
    have hmem := Finset.mem_inter.mp hnu
    have hpoint :=
      abs_ndA5RawQ_add_one_sub_le_two_mul_width_div_of_analytic
        hTube0 (by simpa [I0, W] using hmem.1)
        (by simpa [I1, W] using hmem.2)
    have hloNu : lo ≤ nu := by
      rw [hI0eq] at hmem
      exact (Finset.mem_Icc.mp hmem.1).1
    have hloNuReal : (lo : ℝ) ≤ nu := by exact_mod_cast hloNu
    have hfrac : W / (nu : ℝ) ≤ W / (lo : ℝ) :=
      div_le_div_of_nonneg_left hWnonneg hloReal hloNuReal
    change |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| ≤
      2 * (W / (lo : ℝ)) * ndA5RawQ A W nu
    exact hpoint.trans (by
      have hq := ndA5RawQ_nonneg A W nu
      nlinarith [mul_nonneg (sub_nonneg.mpr hfrac) hq])
  have hcommonSum :
      (∑ nu ∈ common, f nu) ≤
        2 * (W / (lo : ℝ)) * Z0 := by
    calc
      (∑ nu ∈ common, f nu) ≤
          ∑ nu ∈ common,
            2 * (W / (lo : ℝ)) * ndA5RawQ A W nu :=
        Finset.sum_le_sum hcommonPoint
      _ = 2 * (W / (lo : ℝ)) *
          (∑ nu ∈ common, ndA5RawQ A W nu) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * (W / (lo : ℝ)) *
          (∑ nu ∈ I0, ndA5RawQ A W nu) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            Finset.inter_subset_left (by
              intro nu _hnuI0 _hnuCommon
              exact ndA5RawQ_nonneg A W nu)
        · positivity
      _ = 2 * (W / (lo : ℝ)) * Z0 := by
        rfl
  have hleftPoint : ∀ nu ∈ left, f nu ≤ 4 / Real.sqrt N := by
    intro nu hnu
    have hmem := Finset.mem_sdiff.mp hnu
    have hzero : ndA5RawQ (A + 1) W nu = 0 :=
      ndA5RawQ_of_not_mem (by simpa [I1] using hmem.2)
    have hatom := ndA5RawQ_le_four_div_sqrt_taoSection5N0_of_analytic
      hTube0 (by simpa [I0, W] using hmem.1)
    change |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| ≤
      4 / Real.sqrt N
    rw [hzero, zero_sub, abs_neg, abs_of_nonneg
      (ndA5RawQ_nonneg A W nu)]
    simpa [N, W] using hatom
  have hleftCard : left.card ≤ 3 := by
    simpa [left, I0, I1, W] using
      card_ndA5FullTube_sdiff_add_one_le_three_of_analytic
        hlogB hTube0
  have hleftSum :
      (∑ nu ∈ left, f nu) ≤ 12 / Real.sqrt N := by
    calc
      (∑ nu ∈ left, f nu) ≤
          ∑ _nu ∈ left, 4 / Real.sqrt N :=
        Finset.sum_le_sum hleftPoint
      _ = (left.card : ℝ) * (4 / Real.sqrt N) := by
        simp [nsmul_eq_mul]
      _ ≤ 3 * (4 / Real.sqrt N) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hleftCard
        · positivity
      _ = 12 / Real.sqrt N := by ring
  have hrightPoint : ∀ nu ∈ right, f nu ≤ 4 / Real.sqrt N := by
    intro nu hnu
    have hmem := Finset.mem_sdiff.mp hnu
    have hzero : ndA5RawQ A W nu = 0 :=
      ndA5RawQ_of_not_mem (by simpa [I0] using hmem.2)
    have hatom := ndA5RawQ_le_four_div_sqrt_taoSection5N0_of_analytic
      hTube1 (by simpa [I1, W] using hmem.1)
    change |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| ≤
      4 / Real.sqrt N
    rw [hzero, sub_zero, abs_of_nonneg
      (ndA5RawQ_nonneg (A + 1) W nu)]
    simpa [N, W] using hatom
  have hrightCard : right.card ≤ 3 := by
    simpa [right, I0, I1, W] using
      card_ndA5FullTube_add_one_sdiff_le_three_of_analytic
        hlogB hTube1
  have hrightSum :
      (∑ nu ∈ right, f nu) ≤ 12 / Real.sqrt N := by
    calc
      (∑ nu ∈ right, f nu) ≤
          ∑ _nu ∈ right, 4 / Real.sqrt N :=
        Finset.sum_le_sum hrightPoint
      _ = (right.card : ℝ) * (4 / Real.sqrt N) := by
        simp [nsmul_eq_mul]
      _ ≤ 3 * (4 / Real.sqrt N) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hrightCard
        · positivity
      _ = 12 / Real.sqrt N := by ring
  change (∑ nu ∈ I0 ∪ I1, f nu) ≤
    2 * (W / (lo : ℝ)) * Z0 + 24 / Real.sqrt N
  calc
    (∑ nu ∈ I0 ∪ I1, f nu) =
        ((∑ nu ∈ common, f nu) + (∑ nu ∈ left, f nu)) +
          ∑ nu ∈ right, f nu := by
      rw [hpartition, Finset.sum_union hdisjRight,
        Finset.sum_union hdisjCommonLeft]
    _ ≤ (2 * (W / (lo : ℝ)) * Z0 + 12 / Real.sqrt N) +
          12 / Real.sqrt N :=
      add_le_add (add_le_add hcommonSum hleftSum) hrightSum
    _ = 2 * (W / (lo : ℝ)) * Z0 + 24 / Real.sqrt N := by ring

end

end ND
end Erdos1135
