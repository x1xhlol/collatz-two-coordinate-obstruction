import Erdos1135.ND.Band.A5RawMass
import Erdos1135.ND.Band.A5AnalyticTube
import Erdos1135.ND.Fourier.FiberEndpointFloor

/-!
# A5 Normalizer Floor

This leaf begins the X.3 branch after the raw `q/G/Z` fork.  Its first
interface is the lower tube-width estimate used both by the central-hit floor
and later by the X.4 boundary-jump estimate.  No normalized weight is defined
here.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The checked `(t2)` ratio and visible `C >= 1/2` imply the source lower
width constant `1.85`.  This is the missing lower-width direction; it is
independent of the already checked upper bound `W <= nu/8`. -/
theorem ndA5T2Scale_width_lower
    {B n : ℕ} {C : ℝ} (hC : (1 / 2 : ℝ) ≤ C)
    (hscale : NDA5T2ScaleFacts B n C) :
    (37 / 20 : ℝ) * Real.sqrt
        (((n - Tao.taoSection5M0 B : ℕ) : ℝ) *
          Real.log (Tao.taoSection5N0 B : ℝ)) ≤
      ndA5TubeWidth B C := by
  let nu := n - Tao.taoSection5M0 B
  let n0 := Tao.taoSection5N0 B
  have hnuPos : (0 : ℝ) < nu := by
    exact_mod_cast hscale.nu_pos
  have hnuOne : (1 : ℝ) ≤ nu := by
    exact_mod_cast hscale.nu_pos
  have hratio :
      (1374 / 100 : ℝ) ≤ (n0 : ℝ) / (nu : ℝ) := by
    simpa [nu, n0] using hscale.n0_div_nu_lower
  have hn0Lower :
      (1374 / 100 : ℝ) * (nu : ℝ) ≤ (n0 : ℝ) :=
    (le_div_iff₀ hnuPos).mp hratio
  have hn0One : (1 : ℝ) ≤ n0 := by
    nlinarith
  have hlogN0 : 0 ≤ Real.log (n0 : ℝ) :=
    Real.log_nonneg hn0One
  have hnuLog :
      0 ≤ (nu : ℝ) * Real.log (n0 : ℝ) :=
    mul_nonneg hnuPos.le hlogN0
  have hn0Log :
      0 ≤ (n0 : ℝ) * Real.log (n0 : ℝ) :=
    mul_nonneg (by positivity) hlogN0
  have hratioScaled :
      (1374 / 100 : ℝ) * (nu : ℝ) * Real.log (n0 : ℝ) ≤
        (n0 : ℝ) * Real.log (n0 : ℝ) := by
    exact mul_le_mul_of_nonneg_right hn0Lower hlogN0
  have hCsq : (1 / 2 : ℝ) ^ 2 ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - 1 / 2)]
  have hCsqScaled :
      (1 / 2 : ℝ) ^ 2 *
          ((n0 : ℝ) * Real.log (n0 : ℝ)) ≤
        C ^ 2 * ((n0 : ℝ) * Real.log (n0 : ℝ)) :=
    mul_le_mul_of_nonneg_right hCsq hn0Log
  have hsquareCore :
      (37 / 20 : ℝ) ^ 2 *
          ((nu : ℝ) * Real.log (n0 : ℝ)) ≤
        C ^ 2 * ((n0 : ℝ) * Real.log (n0 : ℝ)) := by
    norm_num at hratioScaled hCsqScaled ⊢
    nlinarith
  have hsquare :
      ((37 / 20 : ℝ) * Real.sqrt
          ((nu : ℝ) * Real.log (n0 : ℝ))) ^ 2 ≤
        (C * Real.sqrt
          ((n0 : ℝ) * Real.log (n0 : ℝ))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnuLog,
      Real.sq_sqrt hn0Log]
    exact hsquareCore
  have hleftNonneg :
      0 ≤ (37 / 20 : ℝ) * Real.sqrt
        ((nu : ℝ) * Real.log (n0 : ℝ)) := by positivity
  have hrightNonneg :
      0 ≤ C * Real.sqrt
        ((n0 : ℝ) * Real.log (n0 : ℝ)) := by
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  unfold ndA5TubeWidth
  simpa [nu, n0] using
    (sq_le_sq₀ hleftNonneg hrightNonneg).mp hsquare

/-- Specialize the reusable lower-width estimate at the actual left endpoint
of an arbitrary analytic tube.  This is the central-room input used by X.3. -/
theorem ndA5AnalyticTube_width_lower_at_lo
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    (37 / 20 : ℝ) * Real.sqrt
        ((ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) *
          Real.log (Tao.taoSection5N0 B : ℝ)) ≤
      ndA5TubeWidth B C := by
  let W := ndA5TubeWidth B C
  have hne : (ndA5FullTube A W).Nonempty := by simpa [W] using hTube.nonempty
  have hWpos : 0 < W := by simpa [W] using hTube.width_pos
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : ndA5TubeLo A W ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hloMem : ndA5TubeLo A W ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr hlohi
  have hcell : NDA5AnalyticCellFacts B (ndA5TubeLo A W) C A :=
    hTube.pointwise (ndA5TubeLo A W) (by simpa [W] using hloMem)
  have hshift :
      ndA5TubeLo A W + Tao.taoSection5M0 B - Tao.taoSection5M0 B =
        ndA5TubeLo A W := by omega
  have hwidth := ndA5T2Scale_width_lower hTube.one_half_le_C hcell.t2
  rw [hshift] at hwidth
  simpa [W] using hwidth

/-- Physical interior specialization of the analytic lower-width estimate. -/
theorem ndA5InteriorTube_width_lower_at_lo
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (37 / 20 : ℝ) * Real.sqrt
        ((ndA5TubeLo
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C) : ℝ) *
          Real.log (Tao.taoSection5N0 B : ℝ)) ≤
      ndA5TubeWidth B C := by
  simpa using
    ndA5AnalyticTube_width_lower_at_lo
      (NDA5InteriorTubeFacts.toAnalytic hTube)

/-- The endpoint displacement used by the negative-binomial floor is exactly
the natural absolute value of the checked signed physical sweep. -/
theorem ndA5PhysicalLevel_centralDisplacement_eq
    {A : ℝ} {nu : ℕ} (hlevel : NDA5PhysicalLevelFacts A nu) :
    ndGeom2CentralDisplacement nu (ndA5PhysicalLevel A nu) =
      Int.natAbs (ndA5StrictAffineSweep A nu) := by
  unfold ndGeom2CentralDisplacement
  congr 1
  calc
    (ndA5PhysicalLevel A nu : ℤ) - ((2 * nu : ℕ) : ℤ) =
        ndA5PhysicalLevelInt A nu - 2 * (nu : ℤ) := by
      rw [hlevel.nat_cast_eq]
      push_cast
      rfl
    _ = ndA5StrictAffineSweep A nu :=
      ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A nu

/-- The endpoint `(t2)` ratios give a cheap span bound sufficient for X.3.
This deliberately does not claim the sharper manuscript intermediate
`tubeHi <= 2*tubeLo`. -/
private theorem ndA5AnalyticTube_hi_le_four_mul_lo
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    ndA5TubeHi A (ndA5TubeWidth B C) ≤
      4 * ndA5TubeLo A (ndA5TubeWidth B C) := by
  let W := ndA5TubeWidth B C
  let lo := ndA5TubeLo A W
  let hi := ndA5TubeHi A W
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
  have hloCell : NDA5AnalyticCellFacts B lo C A :=
    hTube.pointwise lo (by simpa [W] using hloMem)
  have hhiCell : NDA5AnalyticCellFacts B hi C A :=
    hTube.pointwise hi (by simpa [W] using hhiMem)
  have hloPos : 0 < lo := by simpa [W, lo] using hTube.lo_pos
  have hhiPos : 0 < hi := hloPos.trans_le hlohi
  have hloPosReal : (0 : ℝ) < lo := by exact_mod_cast hloPos
  have hhiPosReal : (0 : ℝ) < hi := by exact_mod_cast hhiPos
  have hloRatio :
      (Tao.taoSection5N0 B : ℝ) / (lo : ℝ) ≤ 4244 / 100 := by
    simpa [lo] using hloCell.t2.n0_div_nu_upper
  have hhiRatio :
      (1374 / 100 : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) / (hi : ℝ) := by
    simpa [hi] using hhiCell.t2.n0_div_nu_lower
  have hloMul :
      (Tao.taoSection5N0 B : ℝ) ≤
        (4244 / 100 : ℝ) * (lo : ℝ) :=
    (div_le_iff₀ hloPosReal).mp hloRatio
  have hhiMul :
      (1374 / 100 : ℝ) * (hi : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) :=
    (le_div_iff₀ hhiPosReal).mp hhiRatio
  have hspanReal : (hi : ℝ) ≤ 4 * (lo : ℝ) := by
    nlinarith
  simpa [W, lo, hi] using (show hi ≤ 4 * lo by exact_mod_cast hspanReal)

/-- The left-endpoint `(t2)` ratio makes the logarithm large enough for the
checked lower-width estimate to dominate `sqrt tubeLo`.  Combining this with
the checked upper-width estimate forces the small absolute cutoff used below.
No ambient lower bound on `log B` is needed at this interface. -/
private theorem ndA5AnalyticTube_scaled_sqrt_lo_lt_width_and_sixty_four_lt_lo
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    (37 / 20 : ℝ) * Real.sqrt
        (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) <
        ndA5TubeWidth B C ∧
      64 < ndA5TubeLo A (ndA5TubeWidth B C) := by
  let W := ndA5TubeWidth B C
  let lo := ndA5TubeLo A W
  have hne : (ndA5FullTube A W).Nonempty := by simpa [W] using hTube.nonempty
  have hWpos : 0 < W := by simpa [W] using hTube.width_pos
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : lo ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hloMem : lo ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr hlohi
  have hloCell : NDA5AnalyticCellFacts B lo C A :=
    hTube.pointwise lo (by simpa [W] using hloMem)
  have hloPos : 0 < lo := by simpa [W, lo] using hTube.lo_pos
  have hloPosReal : (0 : ℝ) < lo := by exact_mod_cast hloPos
  have hloRatio :
      (1374 / 100 : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) / (lo : ℝ) := by
    simpa [lo] using hloCell.t2.n0_div_nu_lower
  have hn0Lower :
      (1374 / 100 : ℝ) * (lo : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) :=
    (le_div_iff₀ hloPosReal).mp hloRatio
  have hloOne : (1 : ℝ) ≤ lo := by exact_mod_cast hloPos
  have hn0Three :
      (3 : ℝ) < Tao.taoSection5N0 B := by
    nlinarith
  have hn0Pos :
      (0 : ℝ) < Tao.taoSection5N0 B := by linarith
  have hlogOne :
      (1 : ℝ) < Real.log (Tao.taoSection5N0 B : ℝ) :=
    (Real.lt_log_iff_exp_lt hn0Pos).2
      (Real.exp_one_lt_three.trans hn0Three)
  have hprod :
      (lo : ℝ) <
        (lo : ℝ) * Real.log (Tao.taoSection5N0 B : ℝ) := by
    simpa using (mul_lt_mul_of_pos_left hlogOne hloPosReal)
  have hsqrt :
      Real.sqrt (lo : ℝ) <
        Real.sqrt
          ((lo : ℝ) * Real.log (Tao.taoSection5N0 B : ℝ)) :=
    Real.sqrt_lt_sqrt hloPosReal.le hprod
  have hwidth := ndA5AnalyticTube_width_lower_at_lo hTube
  have hscaledSqrtWidth :
      (37 / 20 : ℝ) * Real.sqrt (lo : ℝ) < W := by
    have hscaledSqrt :
        (37 / 20 : ℝ) * Real.sqrt (lo : ℝ) <
          (37 / 20 : ℝ) * Real.sqrt
            ((lo : ℝ) * Real.log (Tao.taoSection5N0 B : ℝ)) :=
      mul_lt_mul_of_pos_left hsqrt (by norm_num)
    simpa [W, lo] using hscaledSqrt.trans_le hwidth
  have hsqrtWidth : Real.sqrt (lo : ℝ) < W := by
    nlinarith [Real.sqrt_nonneg (lo : ℝ)]
  have hWle : W ≤ (lo : ℝ) / 8 := by
    simpa [W, lo] using hloCell.t2.width_le_nu_div_eight
  have hsqrtSq : (Real.sqrt (lo : ℝ)) ^ 2 = (lo : ℝ) :=
    Real.sq_sqrt hloPosReal.le
  have hloSixtyFour : 64 < lo := by
    have hloSixtyFourReal : (64 : ℝ) < lo := by
      nlinarith [Real.sqrt_pos.2 hloPosReal]
    exact_mod_cast hloSixtyFourReal
  simpa [W, lo] using And.intro hscaledSqrtWidth hloSixtyFour

/-- Public analytic X.4 boundary-room adapter.  The source `1.85` lower-width
constant already dominates the square root of the actual tube start. -/
theorem ndA5AnalyticTube_scaled_sqrt_lo_lt_width
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    (37 / 20 : ℝ) * Real.sqrt
        (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) <
      ndA5TubeWidth B C :=
  (ndA5AnalyticTube_scaled_sqrt_lo_lt_width_and_sixty_four_lt_lo hTube).1

/-- Physical interior specialization of the analytic boundary-room adapter. -/
theorem ndA5InteriorTube_scaled_sqrt_lo_lt_width
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (37 / 20 : ℝ) * Real.sqrt
        (ndA5TubeLo
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C) : ℝ) <
      ndA5TubeWidth B C := by
  simpa using
    ndA5AnalyticTube_scaled_sqrt_lo_lt_width
      (NDA5InteriorTubeFacts.toAnalytic hTube)

/-- Every checked analytic tube has width strictly larger than one. -/
theorem one_lt_ndA5TubeWidth_of_analytic
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    (1 : ℝ) < ndA5TubeWidth B C := by
  have hscaled := ndA5AnalyticTube_scaled_sqrt_lo_lt_width hTube
  have hlo :=
    (ndA5AnalyticTube_scaled_sqrt_lo_lt_width_and_sixty_four_lt_lo hTube).2
  let lo := ndA5TubeLo A (ndA5TubeWidth B C)
  have hlo' : 64 < lo := by simpa [lo] using hlo
  have honeLoReal : (1 : ℝ) < lo := by
    exact_mod_cast (show 1 < lo by omega)
  have hsqrtOne : (1 : ℝ) < Real.sqrt (lo : ℝ) := by
    have hsqrt := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) honeLoReal
    norm_num at hsqrt ⊢
    exact hsqrt
  simpa [lo] using (show (1 : ℝ) < ndA5TubeWidth B C by
    nlinarith)

/-- Physical interior specialization of the analytic width lower bound. -/
theorem one_lt_ndA5TubeWidth_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (1 : ℝ) < ndA5TubeWidth B C :=
  one_lt_ndA5TubeWidth_of_analytic
    (NDA5InteriorTubeFacts.toAnalytic hTube)

/-- A central endpoint whose displacement is at most the square root of a
smaller positive time has a uniform `1/(16*sqrt nu)` mass floor.  The
constant is intentionally modest: the `5/4` exponential budget is enough for
the X.3 sum and avoids any asymptotic estimate. -/
private theorem one_div_sixteen_mul_sqrt_le_endpointMass_of_displacement
    {nuMin nu L : ℕ} (hmin : 16 ≤ nuMin) (hnuLower : nuMin ≤ nu)
    (hd : ndGeom2CentralDisplacement nu L ≤ Nat.sqrt nuMin) :
    1 / (16 * Real.sqrt (nu : ℝ)) ≤ ndGeom2EndpointMass nu L := by
  let d := ndGeom2CentralDisplacement nu L
  change d ≤ Nat.sqrt nuMin at hd
  have hs4 : 4 ≤ Nat.sqrt nuMin :=
    (Nat.le_sqrt).2 (by omega)
  have hss := Nat.sqrt_le nuMin
  have h4d : 4 * d ≤ nu := by
    calc
      4 * d ≤ 4 * Nat.sqrt nuMin := Nat.mul_le_mul_left 4 hd
      _ ≤ Nat.sqrt nuMin * Nat.sqrt nuMin :=
        Nat.mul_le_mul_right (Nat.sqrt nuMin) hs4
      _ ≤ nuMin := hss
      _ ≤ nu := hnuLower
  have hdd : d * d ≤ nu := by
    exact (Nat.mul_le_mul hd hd).trans (hss.trans hnuLower)
  have hn : 0 < nu := by omega
  have hhalf : 2 * d ≤ nu := by omega
  have hnReal : (0 : ℝ) < nu := by exact_mod_cast hn
  have h4dReal : (4 : ℝ) * (d : ℝ) ≤ nu := by exact_mod_cast h4d
  have hddReal : (d : ℝ) * (d : ℝ) ≤ nu := by exact_mod_cast hdd
  have hbudget :
      (d : ℝ) * ((d : ℝ) + 1) / (nu : ℝ) ≤ 5 / 4 := by
    apply (div_le_iff₀ hnReal).2
    nlinarith
  have hnegOne : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    have hdecimal := Real.exp_neg_one_gt_d9
    norm_num at hdecimal ⊢
    linarith
  have hnegQuarter : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4)) := by
    have h := Real.one_sub_le_exp_neg (1 / 4 : ℝ)
    norm_num at h ⊢
    exact h
  have hnegFiveFour : (1 / 4 : ℝ) ≤ Real.exp (-(5 / 4)) := by
    calc
      (1 / 4 : ℝ) = (1 / 3) * (3 / 4) := by norm_num
      _ ≤ Real.exp (-1) * Real.exp (-(1 / 4)) :=
        mul_le_mul hnegOne hnegQuarter (by positivity) (by positivity)
      _ = Real.exp (-(5 / 4)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hexp :
      (1 / 4 : ℝ) ≤
        Real.exp (-((d : ℝ) * ((d : ℝ) + 1) / (nu : ℝ))) := by
    exact hnegFiveFour.trans
      (Real.exp_monotone (by linarith))
  have hbase :=
    one_div_four_mul_sqrt_mul_exp_displacement_le_endpointMass
      (n := nu) (L := L) hn (by simpa [d] using hhalf)
  change
    1 / (4 * Real.sqrt (nu : ℝ)) *
        Real.exp (-((d : ℝ) * ((d : ℝ) + 1) / (nu : ℝ))) ≤
      ndGeom2EndpointMass nu L at hbase
  calc
    1 / (16 * Real.sqrt (nu : ℝ)) =
        1 / (4 * Real.sqrt (nu : ℝ)) * (1 / 4) := by ring
    _ ≤ 1 / (4 * Real.sqrt (nu : ℝ)) *
        Real.exp (-((d : ℝ) * ((d : ℝ) + 1) / (nu : ℝ))) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ ndGeom2EndpointMass nu L := hbase

/-- The source X.3 normalizer floor.  Exact endpoint crossings supply a full
central block of indices; the checked endpoint-mass estimate then gives total
raw tube mass at least `1/32`.  The sharper printed intermediate span estimate
is not asserted: the endpoint `(t2)` ratios directly provide the weaker
factor-four comparison actually consumed here. -/
theorem one_div_thirty_two_le_ndA5TubeRawMass_of_analytic
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    (1 / 32 : ℝ) ≤ ndA5TubeRawMass A (ndA5TubeWidth B C) := by
  classical
  let W := ndA5TubeWidth B C
  let lo := ndA5TubeLo A W
  let hi := ndA5TubeHi A W
  let s := Nat.sqrt lo
  let H := (Finset.Icc lo hi).filter
    (fun nu => Int.natAbs (ndA5StrictAffineSweep A nu) ≤ s)
  have hne : (ndA5FullTube A W).Nonempty := by simpa [W] using hTube.nonempty
  have hWpos : 0 < W := by simpa [W] using hTube.width_pos
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : lo ≤ hi := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hroom :=
    ndA5AnalyticTube_scaled_sqrt_lo_lt_width_and_sixty_four_lt_lo hTube
  have hsqrtWidth : Real.sqrt (lo : ℝ) < W := by
    have hscaled : (37 / 20 : ℝ) * Real.sqrt (lo : ℝ) < W := by
      simpa [W, lo] using hroom.1
    nlinarith [Real.sqrt_nonneg (lo : ℝ)]
  have hloSixtyFour : 64 < lo := by
    simpa [W, lo] using hroom.2
  have hsRealLe : (s : ℝ) ≤ Real.sqrt (lo : ℝ) := by
    simpa [s] using (Real.nat_sqrt_le_real_sqrt (a := lo))
  have hsLtCeil : s < Nat.ceil W := by
    exact Nat.lt_ceil.mpr (hsRealLe.trans_lt hsqrtWidth)
  have hsRadius : s ≤ ndA5TubeRadius W := by
    unfold ndA5TubeRadius
    omega
  have hupper : (s : ℤ) ≤ ndA5StrictAffineSweep A lo := by
    have hsRadiusInt : (s : ℤ) ≤ ndA5TubeRadius W := by
      exact_mod_cast hsRadius
    simpa [W, lo] using hsRadiusInt.trans_eq hTube.endpoint_crossings.1.symm
  have hlower : ndA5StrictAffineSweep A hi ≤ -(s : ℤ) := by
    have hsRadiusInt : (s : ℤ) ≤ ndA5TubeRadius W := by
      exact_mod_cast hsRadius
    simpa [W, hi] using
      hTube.endpoint_crossings.2.le.trans (neg_le_neg hsRadiusInt)
  have hcardNat : 2 * s + 1 ≤ H.card := by
    simpa [H] using
      two_mul_add_one_le_card_centralHits_of_unit_down_sweep
        (d := ndA5StrictAffineSweep A) hlohi
        (fun nu _hlo _hhi => ndA5StrictAffineSweep_succ A nu)
        hupper hlower
  have hcardReal : Real.sqrt (lo : ℝ) ≤ (H.card : ℝ) := by
    have hsqrtSucc :
        Real.sqrt (lo : ℝ) < (s : ℝ) + 1 := by
      simpa [s] using (Real.real_sqrt_lt_nat_sqrt_succ (a := lo))
    have hcardCast : ((2 * s + 1 : ℕ) : ℝ) ≤ H.card := by
      exact_mod_cast hcardNat
    push_cast at hcardCast
    have hsNonneg : (0 : ℝ) ≤ s := by positivity
    nlinarith
  have hspan : hi ≤ 4 * lo := by
    simpa [W, lo, hi] using ndA5AnalyticTube_hi_le_four_mul_lo hTube
  have hsubset : H ⊆ ndA5FullTube A W := by
    intro nu hnu
    rw [hEq]
    exact (Finset.mem_filter.mp hnu).1
  have hpoint : ∀ nu ∈ H,
      1 / (32 * Real.sqrt (lo : ℝ)) ≤ ndA5RawQ A W nu := by
    intro nu hnu
    have hnuFilter := Finset.mem_filter.mp hnu
    have hnuBounds := Finset.mem_Icc.mp hnuFilter.1
    have hnuTube : nu ∈ ndA5FullTube A W := hsubset hnu
    have hcell : NDA5AnalyticCellFacts B nu C A :=
      hTube.pointwise nu (by simpa [W] using hnuTube)
    have hdisplacement :
        ndGeom2CentralDisplacement nu (ndA5PhysicalLevel A nu) ≤ s := by
      rw [ndA5PhysicalLevel_centralDisplacement_eq hcell.level]
      exact hnuFilter.2
    have hmass :=
      one_div_sixteen_mul_sqrt_le_endpointMass_of_displacement
        (nuMin := lo) (nu := nu) (L := ndA5PhysicalLevel A nu)
        (by omega) hnuBounds.1 (by simpa [s] using hdisplacement)
    have hnuFour : nu ≤ 4 * lo := hnuBounds.2.trans hspan
    have hnuFourReal : (nu : ℝ) ≤ 4 * (lo : ℝ) := by
      exact_mod_cast hnuFour
    have hsqrtNu :
        Real.sqrt (nu : ℝ) ≤ 2 * Real.sqrt (lo : ℝ) := by
      calc
        Real.sqrt (nu : ℝ) ≤ Real.sqrt (4 * (lo : ℝ)) :=
          Real.sqrt_le_sqrt hnuFourReal
        _ = 2 * Real.sqrt (lo : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
    have hnuPos : 0 < nu := by
      simpa using hcell.t2.nu_pos
    have hden :
        16 * Real.sqrt (nu : ℝ) ≤ 32 * Real.sqrt (lo : ℝ) := by
      nlinarith
    have hreciprocal :
        1 / (32 * Real.sqrt (lo : ℝ)) ≤
          1 / (16 * Real.sqrt (nu : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hden
    rw [ndA5RawQ_of_mem hnuTube]
    exact hreciprocal.trans hmass
  have hsumCentral :
      (∑ _nu ∈ H, 1 / (32 * Real.sqrt (lo : ℝ))) ≤
        ∑ nu ∈ H, ndA5RawQ A W nu := by
    exact Finset.sum_le_sum fun nu hnu => hpoint nu hnu
  have hsumFull :
      (∑ nu ∈ H, ndA5RawQ A W nu) ≤
        ∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro nu _hnuFull _hnuCentral
      exact ndA5RawQ_nonneg A W nu)
  have hloPosReal : (0 : ℝ) < lo := by
    exact_mod_cast (show 0 < lo by omega)
  have hsqrtPos : 0 < Real.sqrt (lo : ℝ) := Real.sqrt_pos.2 hloPosReal
  have hcardMass :
      (1 / 32 : ℝ) ≤
        (H.card : ℝ) * (1 / (32 * Real.sqrt (lo : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_right hcardReal
      (show 0 ≤ (1 / (32 * Real.sqrt (lo : ℝ)) : ℝ) by positivity)
    calc
      (1 / 32 : ℝ) =
          Real.sqrt (lo : ℝ) *
            (1 / (32 * Real.sqrt (lo : ℝ))) := by
        field_simp
      _ ≤ (H.card : ℝ) *
          (1 / (32 * Real.sqrt (lo : ℝ))) := hmul
  calc
    (1 / 32 : ℝ) ≤
        (H.card : ℝ) * (1 / (32 * Real.sqrt (lo : ℝ))) := hcardMass
    _ = ∑ _nu ∈ H, 1 / (32 * Real.sqrt (lo : ℝ)) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ nu ∈ H, ndA5RawQ A W nu := hsumCentral
    _ ≤ ∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu := hsumFull
    _ = ndA5TubeRawMass A (ndA5TubeWidth B C) := by
      simp [ndA5TubeRawMass, W]

/-- Physical interior specialization of the arbitrary-phase X.3 floor. -/
theorem one_div_thirty_two_le_ndA5TubeRawMass_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (1 / 32 : ℝ) ≤
      ndA5TubeRawMass
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) := by
  simpa using
    one_div_thirty_two_le_ndA5TubeRawMass_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube)

/-- Source-facing X.3 in terms of the physical band mass `G(M,j)`.  The
interior carrier identity is used only here, after the intrinsic `Z` floor has
been proved. -/
theorem one_div_thirty_two_le_ndA5BandRawMass_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (1 / 32 : ℝ) ≤ ndA5BandRawMass B branch C j M := by
  rw [ndA5BandRawMass_eq_tubeRawMass_of_interior hTube]
  exact one_div_thirty_two_le_ndA5TubeRawMass_of_interior hTube

end

end ND
end Erdos1135
