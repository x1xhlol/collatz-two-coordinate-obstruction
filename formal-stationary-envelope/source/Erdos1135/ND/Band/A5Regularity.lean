import Erdos1135.ND.Band.A5NormalizerFloor
import Erdos1135.ND.Fourier.FiberEndpointCeiling
import Erdos1135.ND.Fourier.FiberEndpointRecurrence

/-!
# A5 Normalized Regularity

This leaf starts frozen A5 X.4.  It defines the intrinsic normalized tube
weight only after the raw carrier and X.3 floor are checked, records its
finite normalization and inverse-square-root ceiling, and connects the two
neutral cross-length endpoint recurrences to consecutive physical levels.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Intrinsic normalized A5 tube weight `w_nu=q_nu/Z`.  The denominator is
the intrinsic tube mass, never the exterior physical carrier. -/
noncomputable def ndA5NormalizedQ (A W : ℝ) (nu : ℕ) : ℝ :=
  ndA5RawQ A W nu / ndA5TubeRawMass A W

theorem ndA5NormalizedQ_nonneg (A W : ℝ) (nu : ℕ) :
    0 ≤ ndA5NormalizedQ A W nu := by
  unfold ndA5NormalizedQ
  exact div_nonneg (ndA5RawQ_nonneg A W nu) (by
    unfold ndA5TubeRawMass
    exact Finset.sum_nonneg fun _ _ => ndA5RawQ_nonneg A W _)

@[simp] theorem ndA5NormalizedQ_of_not_mem
    {A W : ℝ} {nu : ℕ} (hnu : nu ∉ ndA5FullTube A W) :
    ndA5NormalizedQ A W nu = 0 := by
  simp [ndA5NormalizedQ, ndA5RawQ_of_not_mem hnu]

/-- Positive intrinsic mass normalizes the finite tube weights to one. -/
theorem sum_ndA5NormalizedQ_eq_one
    {A W : ℝ} (hZ : 0 < ndA5TubeRawMass A W) :
    (∑ nu ∈ ndA5FullTube A W, ndA5NormalizedQ A W nu) = 1 := by
  unfold ndA5NormalizedQ
  rw [← Finset.sum_div, show
    (∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu) =
      ndA5TubeRawMass A W by rfl]
  exact div_self hZ.ne'

/-- An arbitrary analytic tube makes the intrinsic normalized carrier a
genuine finite probability weight. -/
theorem sum_ndA5NormalizedQ_eq_one_of_analytic
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    (∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
      ndA5NormalizedQ A (ndA5TubeWidth B C) nu) = 1 := by
  apply sum_ndA5NormalizedQ_eq_one
  exact (by
    have hfloor := one_div_thirty_two_le_ndA5TubeRawMass_of_analytic hTube
    norm_num at hfloor ⊢
    linarith)

/-- Physical interior specialization of analytic normalization. -/
theorem sum_ndA5NormalizedQ_eq_one_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (∑ nu ∈ ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C),
      ndA5NormalizedQ
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) nu) = 1 := by
  simpa using
    sum_ndA5NormalizedQ_eq_one_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube)

/-- The X.3 floor and raw endpoint ceiling give the source-facing normalized
maximum `w_nu <= 16/sqrt(nu)` at every analytic tube point. -/
theorem ndA5NormalizedQ_le_sixteen_div_sqrt_of_analytic
    {B nu : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A)
    (hnu : nu ∈ ndA5FullTube A (ndA5TubeWidth B C)) :
    ndA5NormalizedQ A (ndA5TubeWidth B C) nu ≤
      16 / Real.sqrt (nu : ℝ) := by
  let W := ndA5TubeWidth B C
  have hcell : NDA5AnalyticCellFacts B nu C A :=
    hTube.pointwise nu hnu
  have hnuPos : 0 < nu := by simpa using hcell.t2.nu_pos
  have hrawCeiling :
      ndA5RawQ A W nu ≤ 1 / (2 * Real.sqrt (nu : ℝ)) := by
    rw [ndA5RawQ_of_mem (by simpa [W] using hnu)]
    exact ndGeom2EndpointMass_le_one_div_two_mul_sqrt
      hnuPos hcell.level.nu_le_nat
  have hfloor : (1 / 32 : ℝ) ≤ ndA5TubeRawMass A W := by
    simpa [W] using one_div_thirty_two_le_ndA5TubeRawMass_of_analytic hTube
  have hqNonneg := ndA5RawQ_nonneg A W nu
  unfold ndA5NormalizedQ
  calc
    ndA5RawQ A W nu / ndA5TubeRawMass A W ≤
        ndA5RawQ A W nu / (1 / 32 : ℝ) :=
      div_le_div_of_nonneg_left hqNonneg (by norm_num) hfloor
    _ = 32 * ndA5RawQ A W nu := by ring
    _ ≤ 32 * (1 / (2 * Real.sqrt (nu : ℝ))) :=
      mul_le_mul_of_nonneg_left hrawCeiling (by norm_num)
    _ = 16 / Real.sqrt (nu : ℝ) := by ring

/-- Physical interior specialization of the analytic normalized ceiling. -/
theorem ndA5NormalizedQ_le_sixteen_div_sqrt_of_interior
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)) :
    ndA5NormalizedQ
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) nu ≤
      16 / Real.sqrt (nu : ℝ) := by
  simpa using
    ndA5NormalizedQ_le_sixteen_div_sqrt_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube) hnu

/-- Lossless consecutive physical levels rise by exactly one or two.  A
stationary signed displacement corresponds to a level rise of two, while a
unit displacement drop corresponds to a level rise of one. -/
theorem ndA5PhysicalLevel_succ_eq_add_one_or_two
    {A : ℝ} {nu : ℕ}
    (h0 : NDA5PhysicalLevelFacts A nu)
    (h1 : NDA5PhysicalLevelFacts A (nu + 1)) :
    ndA5PhysicalLevel A (nu + 1) = ndA5PhysicalLevel A nu + 1 ∨
      ndA5PhysicalLevel A (nu + 1) = ndA5PhysicalLevel A nu + 2 := by
  have hd0 :
      (ndA5PhysicalLevel A nu : ℤ) - 2 * (nu : ℤ) =
        ndA5StrictAffineSweep A nu := by
    rw [h0.nat_cast_eq]
    exact ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A nu
  have hd1 :
      (ndA5PhysicalLevel A (nu + 1) : ℤ) - 2 * ((nu + 1 : ℕ) : ℤ) =
        ndA5StrictAffineSweep A (nu + 1) := by
    rw [h1.nat_cast_eq]
    exact ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A (nu + 1)
  rcases ndA5StrictAffineSweep_succ A nu with hstay | hdrop
  · right
    exact_mod_cast (show
      (ndA5PhysicalLevel A (nu + 1) : ℤ) =
        (ndA5PhysicalLevel A nu : ℤ) + 2 by omega)
  · left
    exact_mod_cast (show
      (ndA5PhysicalLevel A (nu + 1) : ℤ) =
        (ndA5PhysicalLevel A nu : ℤ) + 1 by omega)

/-- Consecutive supported raw weights obey the first exact X.4 recurrence
when the physical endpoint rises by one. -/
theorem ndA5RawQ_succ_eq_of_level_add_one_of_analytic
    {B nu : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A)
    (hnu : nu ∈ ndA5FullTube A (ndA5TubeWidth B C))
    (hnext : nu + 1 ∈ ndA5FullTube A (ndA5TubeWidth B C))
    (hlevel : ndA5PhysicalLevel A (nu + 1) =
      ndA5PhysicalLevel A nu + 1) :
    ndA5RawQ A (ndA5TubeWidth B C) (nu + 1) =
      ndA5RawQ A (ndA5TubeWidth B C) nu *
        (ndA5PhysicalLevel A nu : ℝ) / (2 * (nu : ℝ)) := by
  let W := ndA5TubeWidth B C
  have hcell := hTube.pointwise nu hnu
  have hnuPos : 0 < nu := by simpa using hcell.t2.nu_pos
  rw [ndA5RawQ_of_mem (by simpa [W] using hnext),
    ndA5RawQ_of_mem (by simpa [W] using hnu)]
  simpa [hlevel] using
    ndGeom2EndpointMass_succ_length_one hnuPos hcell.level.nu_le_nat

/-- Physical interior specialization of the first analytic recurrence. -/
theorem ndA5RawQ_succ_eq_of_level_add_one
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C))
    (hnext : nu + 1 ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C))
    (hlevel : ndA5PhysicalLevel
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M) (nu + 1) =
      ndA5PhysicalLevel
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu + 1) :
    ndA5RawQ
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) (nu + 1) =
      ndA5RawQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) nu *
        (ndA5PhysicalLevel
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) /
          (2 * (nu : ℝ)) := by
  simpa using
    ndA5RawQ_succ_eq_of_level_add_one_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube) hnu hnext hlevel

/-- Consecutive supported raw weights obey the second exact X.4 recurrence
when the physical endpoint rises by two. -/
theorem ndA5RawQ_succ_eq_of_level_add_two_of_analytic
    {B nu : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A)
    (hnu : nu ∈ ndA5FullTube A (ndA5TubeWidth B C))
    (hnext : nu + 1 ∈ ndA5FullTube A (ndA5TubeWidth B C))
    (hlevel : ndA5PhysicalLevel A (nu + 1) =
      ndA5PhysicalLevel A nu + 2) :
    ndA5RawQ A (ndA5TubeWidth B C) (nu + 1) =
      ndA5RawQ A (ndA5TubeWidth B C) nu *
        (((ndA5PhysicalLevel A nu : ℝ) *
            ((ndA5PhysicalLevel A nu + 1 : ℕ) : ℝ)) /
          (4 * (nu : ℝ) *
            ((ndA5PhysicalLevel A nu + 1 - nu : ℕ) : ℝ))) := by
  let W := ndA5TubeWidth B C
  have hcell := hTube.pointwise nu hnu
  have hnuPos : 0 < nu := by simpa using hcell.t2.nu_pos
  rw [ndA5RawQ_of_mem (by simpa [W] using hnext),
    ndA5RawQ_of_mem (by simpa [W] using hnu)]
  simpa [hlevel] using
    ndGeom2EndpointMass_succ_length_two hnuPos hcell.level.nu_le_nat

/-- Physical interior specialization of the second analytic recurrence. -/
theorem ndA5RawQ_succ_eq_of_level_add_two
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C))
    (hnext : nu + 1 ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C))
    (hlevel : ndA5PhysicalLevel
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M) (nu + 1) =
      ndA5PhysicalLevel
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu + 2) :
    ndA5RawQ
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) (nu + 1) =
      ndA5RawQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) nu *
        (((ndA5PhysicalLevel
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu : ℝ) *
            ((ndA5PhysicalLevel
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu + 1 : ℕ) : ℝ)) /
          (4 * (nu : ℝ) *
            ((ndA5PhysicalLevel
              (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu + 1 - nu : ℕ) : ℝ))) := by
  simpa using
    ndA5RawQ_succ_eq_of_level_add_two_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube) hnu hnext hlevel

/-- Analytic adjacent raw weights have a mass-proportional relative defect.
The factor two is uniform across both exact level increments. -/
theorem abs_ndA5RawQ_succ_sub_le_two_mul_width_div_of_analytic
    {B nu : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A)
    (hnu : nu ∈ ndA5FullTube A (ndA5TubeWidth B C))
    (hnext : nu + 1 ∈ ndA5FullTube A (ndA5TubeWidth B C)) :
    |ndA5RawQ A (ndA5TubeWidth B C) (nu + 1) -
        ndA5RawQ A (ndA5TubeWidth B C) nu| ≤
      2 * (ndA5TubeWidth B C / (nu : ℝ)) *
        ndA5RawQ A (ndA5TubeWidth B C) nu := by
  let W := ndA5TubeWidth B C
  let L := ndA5PhysicalLevel A nu
  let q := ndA5RawQ A W nu
  have hcell : NDA5AnalyticCellFacts B nu C A :=
    hTube.pointwise nu (by simpa [W] using hnu)
  have hnextCell : NDA5AnalyticCellFacts B (nu + 1) C A :=
    hTube.pointwise (nu + 1) (by simpa [W] using hnext)
  have hnuPos : 0 < nu := by simpa using hcell.t2.nu_pos
  have hnuReal : (0 : ℝ) < nu := by exact_mod_cast hnuPos
  have hqNonneg : 0 ≤ q := by
    exact ndA5RawQ_nonneg A W nu
  have hWone : (1 : ℝ) < W := by
    simpa [W] using one_lt_ndA5TubeWidth_of_analytic hTube
  have hWNonneg : (0 : ℝ) ≤ W := by linarith
  have hWle : W ≤ (nu : ℝ) / 8 := by
    simpa [W] using hcell.t2.width_le_nu_div_eight
  have hdInt :
      (L : ℤ) - 2 * (nu : ℤ) = ndA5StrictAffineSweep A nu := by
    dsimp [L]
    rw [hcell.level.nat_cast_eq]
    exact ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A nu
  have hdReal := congrArg (fun z : ℤ => (z : ℝ)) hdInt
  push_cast at hdReal
  have htube : |(ndA5StrictAffineSweep A nu : ℝ)| < W :=
    (Finset.mem_filter.mp hnu).2
  have hdev : |(L : ℝ) - 2 * (nu : ℝ)| < W := by
    rw [hdReal]
    exact htube
  rcases ndA5PhysicalLevel_succ_eq_add_one_or_two
      hcell.level hnextCell.level with hone | htwo
  · have hrec := ndA5RawQ_succ_eq_of_level_add_one_of_analytic
      hTube hnu hnext hone
    have hratio :
        |((L : ℝ) - 2 * (nu : ℝ)) / (2 * (nu : ℝ))| ≤
          2 * (W / (nu : ℝ)) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * nu)]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * nu)).2
      have hdevLe := hdev.le
      field_simp [hnuReal.ne']
      nlinarith
    have hfactor :
        q * (L : ℝ) / (2 * (nu : ℝ)) - q =
          q * (((L : ℝ) - 2 * (nu : ℝ)) / (2 * (nu : ℝ))) := by
      field_simp [hnuReal.ne']
    change |ndA5RawQ A W (nu + 1) - q| ≤
      2 * (W / (nu : ℝ)) * q
    rw [hrec, hfactor, abs_mul, abs_of_nonneg hqNonneg]
    calc
      q * |((L : ℝ) - 2 * (nu : ℝ)) / (2 * (nu : ℝ))| ≤
          q * (2 * (W / (nu : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio hqNonneg
      _ = 2 * (W / (nu : ℝ)) * q := by ring
  · have hrec := ndA5RawQ_succ_eq_of_level_add_two_of_analytic
      hTube hnu hnext htwo
    let x : ℝ := (L : ℝ) - 2 * (nu : ℝ)
    let g : ℝ := (L : ℝ) + 1 - (nu : ℝ)
    have hx : |x| < W := by simpa [x] using hdev
    have hxBounds := abs_lt.mp hx
    have hLnu : nu ≤ L := by simpa [L] using hcell.level.nu_le_nat
    have hgCast : ((L + 1 - nu : ℕ) : ℝ) = g := by
      rw [Nat.cast_sub (by omega : nu ≤ L + 1)]
      push_cast
      rfl
    have hgPos : 0 < g := by
      dsimp [g]
      have hLnuReal : (nu : ℝ) ≤ L := by exact_mod_cast hLnu
      linarith
    have hgLower : (nu : ℝ) / 2 ≤ g := by
      dsimp [x, g] at hxBounds ⊢
      nlinarith
    have hxSq : x ^ 2 ≤ W ^ 2 := by
      have hsquare := (sq_lt_sq₀ (abs_nonneg x) hWNonneg).2 hx
      simpa only [sq_abs] using hsquare.le
    have hWsq : W ^ 2 ≤ W * (nu : ℝ) / 8 := by
      nlinarith [mul_nonneg hWNonneg (sub_nonneg.mpr hWle)]
    have hnuEight : (8 : ℝ) ≤ nu := by nlinarith
    have hWsmall : W ≤ W * (nu : ℝ) / 8 := by
      nlinarith [mul_nonneg hWNonneg (sub_nonneg.mpr
        (show (1 : ℝ) ≤ (nu : ℝ) / 8 by nlinarith))]
    have hnum :
        |x ^ 2 + x - 2 * (nu : ℝ)| ≤ 8 * W * g := by
      calc
        |x ^ 2 + x - 2 * (nu : ℝ)| ≤
            |x ^ 2| + |x| + |2 * (nu : ℝ)| := by
          calc
            |x ^ 2 + x - 2 * (nu : ℝ)| ≤
                |x ^ 2 + x| + |2 * (nu : ℝ)| := by
              simpa [sub_eq_add_neg] using
                (abs_add_le (x ^ 2 + x) (-(2 * (nu : ℝ))))
            _ ≤ |x ^ 2| + |x| + |2 * (nu : ℝ)| := by
              linarith [abs_add_le (x ^ 2) x]
        _ = x ^ 2 + |x| + 2 * (nu : ℝ) := by
          rw [abs_of_nonneg (sq_nonneg x),
            abs_of_nonneg (mul_nonneg (by norm_num) hnuReal.le)]
        _ ≤ 4 * W * (nu : ℝ) := by
          nlinarith [hx.le]
        _ ≤ 8 * W * g := by
          nlinarith [mul_nonneg hWNonneg (sub_nonneg.mpr hgLower)]
    have hdefect :
        (L : ℝ) * ((L + 1 : ℕ) : ℝ) /
              (4 * (nu : ℝ) * ((L + 1 - nu : ℕ) : ℝ)) - 1 =
          (x ^ 2 + x - 2 * (nu : ℝ)) /
            (4 * (nu : ℝ) * g) := by
      rw [hgCast]
      field_simp [hnuReal.ne', hgPos.ne']
      dsimp [x, g]
      push_cast
      ring
    have hratio :
        |(L : ℝ) * ((L + 1 : ℕ) : ℝ) /
              (4 * (nu : ℝ) * ((L + 1 - nu : ℕ) : ℝ)) - 1| ≤
          2 * (W / (nu : ℝ)) := by
      rw [hdefect, abs_div, abs_of_pos (mul_pos (by positivity) hgPos)]
      apply (div_le_iff₀ (mul_pos (by positivity) hgPos)).2
      calc
        |x ^ 2 + x - 2 * (nu : ℝ)| ≤ 8 * W * g := hnum
        _ = 2 * (W / (nu : ℝ)) * (4 * (nu : ℝ) * g) := by
          field_simp [hnuReal.ne']
          ring
    have hfactor :
        q * ((L : ℝ) * ((L + 1 : ℕ) : ℝ) /
              (4 * (nu : ℝ) * ((L + 1 - nu : ℕ) : ℝ))) - q =
          q * ((L : ℝ) * ((L + 1 : ℕ) : ℝ) /
              (4 * (nu : ℝ) * ((L + 1 - nu : ℕ) : ℝ)) - 1) := by
      ring
    change |ndA5RawQ A W (nu + 1) - q| ≤
      2 * (W / (nu : ℝ)) * q
    rw [hrec, hfactor, abs_mul, abs_of_nonneg hqNonneg]
    calc
      q * |(L : ℝ) * ((L + 1 : ℕ) : ℝ) /
            (4 * (nu : ℝ) * ((L + 1 - nu : ℕ) : ℝ)) - 1| ≤
          q * (2 * (W / (nu : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio hqNonneg
      _ = 2 * (W / (nu : ℝ)) * q := by ring

/-- Physical interior specialization of the analytic adjacent defect. -/
theorem abs_ndA5RawQ_succ_sub_le_two_mul_width_div_of_interior
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C))
    (hnext : nu + 1 ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)) :
    |ndA5RawQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) (nu + 1) -
        ndA5RawQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) nu| ≤
      2 * (ndA5TubeWidth B C / (nu : ℝ)) *
        ndA5RawQ
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) nu := by
  simpa using
    abs_ndA5RawQ_succ_sub_le_two_mul_width_div_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube) hnu hnext

/-- Full zero-extension variation of the intrinsic normalized tube weights.
Both endpoint jumps are counted, including twice the unique weight of a
singleton tube. -/
noncomputable def ndA5NormalizedQExtendedVariation (A W : ℝ) : ℝ :=
  let lo := ndA5TubeLo A W
  let hi := ndA5TubeHi A W
  |ndA5NormalizedQ A W lo| +
    (∑ nu ∈ Finset.Ico lo hi,
      |ndA5NormalizedQ A W (nu + 1) - ndA5NormalizedQ A W nu|) +
    |ndA5NormalizedQ A W hi|

/-- Exact source X.4 regularity with an explicit absolute constant.  The
interior variation is bounded proportionally to the raw normalizer before it
is cancelled; no cardinality-times-maximum estimate is used. -/
theorem ndA5NormalizedQExtendedVariation_le_twenty_mul_width_div_lo_of_analytic
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    ndA5NormalizedQExtendedVariation A (ndA5TubeWidth B C) ≤
      20 * ndA5TubeWidth B C /
        (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) := by
  classical
  let W := ndA5TubeWidth B C
  let lo := ndA5TubeLo A W
  let hi := ndA5TubeHi A W
  let Z := ndA5TubeRawMass A W
  have hne : (ndA5FullTube A W).Nonempty := by simpa [W] using hTube.nonempty
  have hWpos : 0 < W := by simpa [W] using hTube.width_pos
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : lo ≤ hi := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hloMem : lo ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr hlohi
  have hhiMem : hi ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.right_mem_Icc.mpr hlohi
  have hloPos : 0 < lo := by simpa [W, lo] using hTube.lo_pos
  have hloReal : (0 : ℝ) < lo := by exact_mod_cast hloPos
  have hZfloor : (1 / 32 : ℝ) ≤ Z := by
    simpa [W, Z] using one_div_thirty_two_le_ndA5TubeRawMass_of_analytic hTube
  have hZpos : 0 < Z := by norm_num at hZfloor ⊢; linarith
  have hscaled :
      (37 / 20 : ℝ) * Real.sqrt (lo : ℝ) < W := by
    simpa [W, lo] using ndA5AnalyticTube_scaled_sqrt_lo_lt_width hTube
  have hsqrtPos : 0 < Real.sqrt (lo : ℝ) := Real.sqrt_pos.2 hloReal
  have hsqrtSq : (Real.sqrt (lo : ℝ)) ^ 2 = (lo : ℝ) :=
    Real.sq_sqrt hloReal.le
  have hloWeight : ndA5NormalizedQ A W lo ≤
      16 / Real.sqrt (lo : ℝ) := by
    simpa [W, lo] using
      ndA5NormalizedQ_le_sixteen_div_sqrt_of_analytic hTube
        (by simpa [W] using hloMem)
  have hhiWeightAtHi : ndA5NormalizedQ A W hi ≤
      16 / Real.sqrt (hi : ℝ) := by
    simpa [W, hi] using
      ndA5NormalizedQ_le_sixteen_div_sqrt_of_analytic hTube
        (by simpa [W] using hhiMem)
  have hsqrtOrder : Real.sqrt (lo : ℝ) ≤ Real.sqrt (hi : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hlohi)
  have hhiWeight : ndA5NormalizedQ A W hi ≤
      16 / Real.sqrt (lo : ℝ) := by
    exact hhiWeightAtHi.trans
      (div_le_div_of_nonneg_left (by norm_num) hsqrtPos hsqrtOrder)
  have hboundary :
      |ndA5NormalizedQ A W lo| + |ndA5NormalizedQ A W hi| ≤
        18 * W / (lo : ℝ) := by
    have hsum :
        |ndA5NormalizedQ A W lo| + |ndA5NormalizedQ A W hi| ≤
          32 / Real.sqrt (lo : ℝ) := by
      rw [abs_of_nonneg (ndA5NormalizedQ_nonneg A W lo),
        abs_of_nonneg (ndA5NormalizedQ_nonneg A W hi)]
      calc
        ndA5NormalizedQ A W lo + ndA5NormalizedQ A W hi ≤
            16 / Real.sqrt (lo : ℝ) +
              16 / Real.sqrt (lo : ℝ) := add_le_add hloWeight hhiWeight
        _ = 32 / Real.sqrt (lo : ℝ) := by ring
    have hnum :
        32 * Real.sqrt (lo : ℝ) ≤ 18 * W := by
      nlinarith [Real.sqrt_nonneg (lo : ℝ)]
    have hid :
        32 / Real.sqrt (lo : ℝ) =
          (32 * Real.sqrt (lo : ℝ)) / (lo : ℝ) := by
      field_simp [(Real.sqrt_pos.2 hloReal).ne']
      nlinarith
    exact hsum.trans (by
      rw [hid]
      exact div_le_div_of_nonneg_right hnum hloReal.le)
  have hEdgeSubset : Finset.Ico lo hi ⊆ ndA5FullTube A W := by
    intro nu hnu
    rw [hEq]
    have hbounds := Finset.mem_Ico.mp hnu
    exact Finset.mem_Icc.mpr ⟨hbounds.1, hbounds.2.le⟩
  have hEdgeNext : ∀ nu ∈ Finset.Ico lo hi,
      nu + 1 ∈ ndA5FullTube A W := by
    intro nu hnu
    rw [hEq]
    have hbounds := Finset.mem_Ico.mp hnu
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hRawEdge : ∀ nu ∈ Finset.Ico lo hi,
      |ndA5RawQ A W (nu + 1) - ndA5RawQ A W nu| ≤
        2 * (W / (lo : ℝ)) * ndA5RawQ A W nu := by
    intro nu hnu
    have hbounds := Finset.mem_Ico.mp hnu
    have hnuTube := hEdgeSubset hnu
    have hnextTube := hEdgeNext nu hnu
    have hedge :=
      abs_ndA5RawQ_succ_sub_le_two_mul_width_div_of_analytic
        hTube (by simpa [W] using hnuTube)
        (by simpa [W] using hnextTube)
    have hnuReal : (lo : ℝ) ≤ nu := by exact_mod_cast hbounds.1
    have hfrac : W / (nu : ℝ) ≤ W / (lo : ℝ) :=
      div_le_div_of_nonneg_left hWpos.le hloReal hnuReal
    exact hedge.trans (by
      have hq := ndA5RawQ_nonneg A W nu
      nlinarith [mul_nonneg (sub_nonneg.mpr hfrac) hq])
  have hRawSum :
      (∑ nu ∈ Finset.Ico lo hi,
          |ndA5RawQ A W (nu + 1) - ndA5RawQ A W nu|) ≤
        2 * (W / (lo : ℝ)) * Z := by
    calc
      (∑ nu ∈ Finset.Ico lo hi,
          |ndA5RawQ A W (nu + 1) - ndA5RawQ A W nu|) ≤
          ∑ nu ∈ Finset.Ico lo hi,
            2 * (W / (lo : ℝ)) * ndA5RawQ A W nu :=
        Finset.sum_le_sum hRawEdge
      _ = 2 * (W / (lo : ℝ)) *
          (∑ nu ∈ Finset.Ico lo hi, ndA5RawQ A W nu) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * (W / (lo : ℝ)) *
          (∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg hEdgeSubset (by
            intro nu _hnuTube _hnuEdge
            exact ndA5RawQ_nonneg A W nu)
        · positivity
      _ = 2 * (W / (lo : ℝ)) * Z := by
        rfl
  have hNormSumEq :
      (∑ nu ∈ Finset.Ico lo hi,
          |ndA5NormalizedQ A W (nu + 1) - ndA5NormalizedQ A W nu|) =
        (∑ nu ∈ Finset.Ico lo hi,
          |ndA5RawQ A W (nu + 1) - ndA5RawQ A W nu|) / Z := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro nu hnu
    unfold ndA5NormalizedQ
    rw [← sub_div, abs_div, abs_of_pos hZpos]
  have hInterior :
      (∑ nu ∈ Finset.Ico lo hi,
          |ndA5NormalizedQ A W (nu + 1) - ndA5NormalizedQ A W nu|) ≤
        2 * W / (lo : ℝ) := by
    rw [hNormSumEq]
    calc
      (∑ nu ∈ Finset.Ico lo hi,
          |ndA5RawQ A W (nu + 1) - ndA5RawQ A W nu|) / Z ≤
          (2 * (W / (lo : ℝ)) * Z) / Z :=
        div_le_div_of_nonneg_right hRawSum hZpos.le
      _ = 2 * W / (lo : ℝ) := by
        field_simp [hZpos.ne']
  unfold ndA5NormalizedQExtendedVariation
  dsimp only
  change |ndA5NormalizedQ A W lo| +
      (∑ nu ∈ Finset.Ico lo hi,
        |ndA5NormalizedQ A W (nu + 1) - ndA5NormalizedQ A W nu|) +
      |ndA5NormalizedQ A W hi| ≤ 20 * W / (lo : ℝ)
  calc
    |ndA5NormalizedQ A W lo| +
          (∑ nu ∈ Finset.Ico lo hi,
            |ndA5NormalizedQ A W (nu + 1) - ndA5NormalizedQ A W nu|) +
          |ndA5NormalizedQ A W hi| =
        (|ndA5NormalizedQ A W lo| + |ndA5NormalizedQ A W hi|) +
          (∑ nu ∈ Finset.Ico lo hi,
            |ndA5NormalizedQ A W (nu + 1) - ndA5NormalizedQ A W nu|) := by
      ring
    _ ≤ 18 * W / (lo : ℝ) + 2 * W / (lo : ℝ) :=
      add_le_add hboundary hInterior
    _ = 20 * W / (lo : ℝ) := by ring

/-- Physical interior specialization of the analytic constant-20 variation. -/
theorem ndA5NormalizedQExtendedVariation_le_twenty_mul_width_div_lo_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    ndA5NormalizedQExtendedVariation
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) ≤
      20 * ndA5TubeWidth B C /
        (ndA5TubeLo
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) : ℝ) := by
  simpa using
    ndA5NormalizedQExtendedVariation_le_twenty_mul_width_div_lo_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube)

/-- Convenient looser X.4 constant for downstream padding and Abel
consumers. -/
theorem ndA5NormalizedQExtendedVariation_le_thirty_two_mul_width_div_lo_of_analytic
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    ndA5NormalizedQExtendedVariation A (ndA5TubeWidth B C) ≤
      32 * ndA5TubeWidth B C /
        (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) := by
  have htwenty :=
    ndA5NormalizedQExtendedVariation_le_twenty_mul_width_div_lo_of_analytic
      hTube
  have hWnonneg : 0 ≤ ndA5TubeWidth B C := by
    linarith [one_lt_ndA5TubeWidth_of_analytic hTube]
  have hloPos : 0 < ndA5TubeLo A (ndA5TubeWidth B C) := hTube.lo_pos
  have hnonneg : 0 ≤ ndA5TubeWidth B C /
      (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) := by
    exact div_nonneg hWnonneg (by positivity)
  calc
    ndA5NormalizedQExtendedVariation A (ndA5TubeWidth B C) ≤
        20 * (ndA5TubeWidth B C /
          (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) := by
      simpa only [mul_div_assoc] using htwenty
    _ ≤ 32 * (ndA5TubeWidth B C /
          (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hnonneg
    _ = 32 * ndA5TubeWidth B C /
          (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) := by ring

/-- Physical interior specialization of the analytic constant-32 variation. -/
theorem ndA5NormalizedQExtendedVariation_le_thirty_two_mul_width_div_lo_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    ndA5NormalizedQExtendedVariation
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) ≤
      32 * ndA5TubeWidth B C /
        (ndA5TubeLo
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) : ℝ) := by
  simpa using
    ndA5NormalizedQExtendedVariation_le_thirty_two_mul_width_div_lo_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube)

end

end ND
end Erdos1135
