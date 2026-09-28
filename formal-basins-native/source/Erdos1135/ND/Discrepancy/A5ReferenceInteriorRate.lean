import Erdos1135.ND.Discrepancy.A5ReferenceInteriorAggregate
import Erdos1135.ND.Band.A5ReferenceTerminalAggregateEventual
import Erdos1135.Tao.Section5.FixedTimeMixing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A5 uniform interior reference rate

This leaf converts the literal endpoint-dependent normalized A6 errors into
one source-scale power rate.  The exponent remains a parameter under the
strict frozen condition `d < 1 / (2 * kappa)`.  The subsequent CommonZ
consumer is additive and does not import the separate exterior estimate.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The endpoint-free scalar majorant for the two normalized interior A6
rows.  Its first summand is the PhaseGap contribution, its second summand
contains the physical A6 and local-shift contributions, and its final
summand is the band-normalizer residue. -/
def ndA5ReferenceInteriorScalarMajorant
    (B : ℕ) (C c kappa : ℝ) : ℝ :=
  (39927552 / 25 : ℝ) * (6 + 2 / (Real.pi * c)) * C ^ 2 *
      Real.log (Tao.taoSection5N0 B : ℝ) *
      Real.rpow (ndA5TubeWidth B C) (-1 / kappa) +
    ((101856 / 25 : ℝ) * C + 288 + 54750000 * (C + C ^ 3)) *
      ndA6PhysicalRate B +
    12 / ((B : ℝ) * ndA5LogFourThirds)

/-- The strict logarithmic rate used by the interior common-profile row. -/
def ndA5ReferenceInteriorScalarRate (B : ℕ) (d : ℝ) : ℝ :=
  Real.rpow (Real.log B) (-d)

/-- The full physical tube has cardinality comparable with its real width,
uniformly over every source-admissible interior endpoint. -/
theorem ndA5ReferenceInteriorTube_card_bounds
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
    let W := ndA5TubeWidth B C
    W ≤ ((ndA5FullTube A W).card : ℝ) ∧
      ((ndA5FullTube A W).card : ℝ) ≤ 7 * W := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let card : ℝ := (ndA5FullTube A W).card
  have hW142 : (142 : ℝ) ≤ W := by
    simpa only [W] using
      ndA5TubeWidth_ge_one_hundred_forty_two hC hlogB
  have hWpos : 0 < W := by linarith
  have hdeltaPos : 0 < ndA5PhaseDelta := ndA5PhaseDelta_mem_Ioo.1
  have hdeltaLeOne : ndA5PhaseDelta ≤ 1 := ndA5PhaseDelta_mem_Ioo.2.le
  have hInvOne : (1 : ℝ) ≤ 1 / ndA5PhaseDelta := by
    apply (le_div_iff₀ hdeltaPos).2
    simpa using hdeltaLeOne
  have hpadding :=
    (ndA5FirstPassagePaddingMargin (W := W) (by linarith)).1
  have hInvThree : (1 : ℝ) / ndA5PhaseDelta ≤ 3 := by
    have hmul : W * ((1 : ℝ) / ndA5PhaseDelta) ≤ W * 3 := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hpadding
    nlinarith
  have hcardError :
      |card - 2 * W / ndA5PhaseDelta| ≤
        2 + 1 / ndA5PhaseDelta := by
    simpa only [A, W, card] using hTube.card_error
  rw [abs_le] at hcardError
  have hcardLower :
      2 * W / ndA5PhaseDelta - (2 + 1 / ndA5PhaseDelta) ≤ card := by
    linarith [hcardError.1]
  have hcardUpper :
      card ≤ 2 * W / ndA5PhaseDelta + (2 + 1 / ndA5PhaseDelta) := by
    linarith [hcardError.2]
  have hTwoW : 2 * W ≤ 2 * W / ndA5PhaseDelta := by
    rw [show 2 * W / ndA5PhaseDelta =
      (2 * W) * (1 / ndA5PhaseDelta) by ring]
    nlinarith
  have hSixW : 2 * W / ndA5PhaseDelta ≤ 6 * W := by
    rw [show 2 * W / ndA5PhaseDelta =
      (2 * W) * (1 / ndA5PhaseDelta) by ring]
    nlinarith
  dsimp only
  change W ≤ card ∧ card ≤ 7 * W
  constructor <;> nlinarith

/-- The localized Koksma geometry factor has one endpoint-independent
majorant.  The constant is exactly `64 * 7 * (4244/100)`. -/
theorem ndA5ReferenceInteriorGeometryFactor_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
    let W := ndA5TubeWidth B C
    64 * ((ndA5FullTube A W).card : ℝ) * W /
        (ndA5TubeLo A W : ℝ) ≤
      (475328 / 25 : ℝ) * C ^ 2 *
        Real.log (Tao.taoSection5N0 B : ℝ) := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let card : ℝ := (ndA5FullTube A W).card
  let lo : ℝ := ndA5TubeLo A W
  let N : ℝ := Tao.taoSection5N0 B
  let L : ℝ := Real.log N
  have hloPos : 0 < lo := by
    dsimp only [lo]
    exact_mod_cast hTube.lo_pos
  have hratio := (ndA6PhysicalN0_div_tubeLo_mem_Icc hTube).2
  have hratio' : N / lo ≤ (4244 / 100 : ℝ) := by
    simpa only [N, lo, A, W] using hratio
  have hratioLower := (ndA6PhysicalN0_div_tubeLo_mem_Icc hTube).1
  have hNlower : (1374 / 100 : ℝ) * lo ≤ N :=
    (le_div_iff₀ hloPos).mp (by
      simpa only [N, lo, A, W] using hratioLower)
  have hNpos : 0 < N := by nlinarith
  have hNone : (1 : ℝ) ≤ N := by
    have hloOne : (1 : ℝ) ≤ lo := by
      dsimp only [lo]
      exact_mod_cast hTube.lo_pos
    have hNlower : (1374 / 100 : ℝ) * lo ≤ N :=
      (le_div_iff₀ hloPos).mp (by
        simpa only [N, lo, A, W] using hratioLower)
    nlinarith
  have hLnonneg : 0 ≤ L := by
    simpa only [L] using Real.log_nonneg hNone
  have hbase : 0 ≤ N * L := mul_nonneg hNpos.le hLnonneg
  have hWnonneg : 0 ≤ W := by
    dsimp only [W, ndA5TubeWidth]
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hWsq : W ^ 2 = C ^ 2 * N * L := by
    dsimp only [W, ndA5TubeWidth]
    rw [mul_pow, Real.sq_sqrt hbase]
    ring
  have hcardUpper :=
    (ndA5ReferenceInteriorTube_card_bounds hC hlogB hTube).2
  have hcardUpper' : card ≤ 7 * W := by
    simpa only [A, W, card] using hcardUpper
  have hcardNonneg : 0 ≤ card := by positivity
  have hfirst : 64 * card * W / N ≤ 448 * C ^ 2 * L := by
    have hmul : card * W ≤ 7 * W ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hcardUpper' hWnonneg]
    apply (div_le_iff₀ hNpos).2
    nlinarith [hWsq]
  have hfirstNonneg : 0 ≤ 64 * card * W / N := by positivity
  have hfirstUpperNonneg : 0 ≤ 448 * C ^ 2 * L := by positivity
  have hratioNonneg : 0 ≤ N / lo := by positivity
  have hfactor :
      64 * card * W / lo = (64 * card * W / N) * (N / lo) := by
    field_simp [hNpos.ne', hloPos.ne']
  dsimp only
  change 64 * card * W / lo ≤ (475328 / 25 : ℝ) * C ^ 2 * L
  rw [hfactor]
  calc
    (64 * card * W / N) * (N / lo) ≤
        (448 * C ^ 2 * L) * (4244 / 100 : ℝ) :=
      mul_le_mul hfirst hratio' hratioNonneg hfirstUpperNonneg
    _ = (475328 / 25 : ℝ) * C ^ 2 * L := by ring

/-- The capped discrepancy is always below its decaying branch. -/
theorem ndEndpointDbar_le_uncapped
    (c kappa : ℝ) (N : ℕ) :
    ndEndpointDbar c kappa N ≤
      (6 + 2 / (Real.pi * c)) *
        Real.rpow (N : ℝ) (-1 / kappa) := by
  unfold ndEndpointDbar
  exact min_le_right _ _

/-- On an interior tube, the uncapped discrepancy branch can be weakened
from the tube cardinality to the real tube width. -/
theorem ndA5ReferenceInteriorDbar_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C M c kappa : ℝ}
    (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hPhase : PhaseGap c kappa)
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
    let W := ndA5TubeWidth B C
    ndEndpointDbar c kappa (ndA5FullTube A W).card ≤
      (6 + 2 / (Real.pi * c)) * Real.rpow W (-1 / kappa) := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let card : ℝ := (ndA5FullTube A W).card
  have hWcard :=
    (ndA5ReferenceInteriorTube_card_bounds hC hlogB hTube).1
  have hWcard' : W ≤ card := by
    simpa only [A, W, card] using hWcard
  have hW142 : (142 : ℝ) ≤ W := by
    simpa only [W] using
      ndA5TubeWidth_ge_one_hundred_forty_two hC hlogB
  have hWpos : 0 < W := by linarith
  have hexp : -1 / kappa ≤ 0 := by
    have hkappa : 0 < kappa := by linarith [hPhase.two_lt_kappa]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hkappa.le
  have hrpow : Real.rpow card (-1 / kappa) ≤
      Real.rpow W (-1 / kappa) :=
    Real.rpow_le_rpow_of_nonpos hWpos hWcard' hexp
  have hconst : 0 ≤ 6 + 2 / (Real.pi * c) := by
    have hden : 0 < Real.pi * c := mul_pos Real.pi_pos hPhase.c_pos
    have : 0 < 2 / (Real.pi * c) := div_pos (by norm_num) hden
    linarith
  dsimp only
  calc
    ndEndpointDbar c kappa (ndA5FullTube A W).card ≤
        (6 + 2 / (Real.pi * c)) * Real.rpow card (-1 / kappa) := by
      simpa only [card] using
        ndEndpointDbar_le_uncapped c kappa (ndA5FullTube A W).card
    _ ≤ (6 + 2 / (Real.pi * c)) * Real.rpow W (-1 / kappa) :=
      mul_le_mul_of_nonneg_left hrpow hconst

/-- Intrinsic raw tube mass is nonnegative before any A6 estimate. -/
theorem ndA5TubeRawMass_nonneg (A W : ℝ) :
    0 ≤ ndA5TubeRawMass A W := by
  unfold ndA5TubeRawMass
  exact Finset.sum_nonneg fun nu _hnu => ndA5RawQ_nonneg A W nu

/-- The physical A6 estimate gives the exact endpoint-local raw-mass
ceiling used in both normalized rows. -/
theorem ndA5ReferenceInteriorRawMass_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M EA6 : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hA6 :
      |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤ EA6) :
    let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
    let W := ndA5TubeWidth B C
    0 ≤ ndA5TubeRawMass A W ∧
      ndA5TubeRawMass A W ≤ 1 / ndA5PhaseDelta + EA6 := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  have hA6' := hA6
  rw [ndA5BandRawMass_eq_tubeRawMass_of_interior hTube] at hA6'
  have hupper : ndA5TubeRawMass A W ≤ 1 / ndA5PhaseDelta + EA6 := by
    have := (abs_le.mp (by simpa only [A, W] using hA6')).2
    linarith
  exact ⟨ndA5TubeRawMass_nonneg A W, hupper⟩

/-- Once the physical A6 error is at most one, the intrinsic raw mass is at
most four.  This is the only scalar weakening of the exact A6 mass row used
by the common interior majorant. -/
theorem ndA5ReferenceInteriorRawMass_le_four
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M EA6 : ℝ}
    (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube : NDA5InteriorTubeFacts B j branch C M)
    (hA6 :
      |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤ EA6)
    (hEA6 : EA6 ≤ 1) :
    let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
    let W := ndA5TubeWidth B C
    0 ≤ ndA5TubeRawMass A W ∧ ndA5TubeRawMass A W ≤ 4 := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  have hW142 : (142 : ℝ) ≤ W := by
    simpa only [W] using
      ndA5TubeWidth_ge_one_hundred_forty_two hC hlogB
  have hWpos : 0 < W := by linarith
  have hpadding :=
    (ndA5FirstPassagePaddingMargin (W := W) (by linarith)).1
  have hInvThree : (1 : ℝ) / ndA5PhaseDelta ≤ 3 := by
    have hmul : W * ((1 : ℝ) / ndA5PhaseDelta) ≤ W * 3 := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hpadding
    nlinarith
  have hmass := ndA5ReferenceInteriorRawMass_le hTube hA6
  have hmass' :
      0 ≤ ndA5TubeRawMass A W ∧
        ndA5TubeRawMass A W ≤ 1 / ndA5PhaseDelta + EA6 := by
    simpa only [A, W] using hmass
  exact ⟨hmass'.1, by linarith⟩

set_option maxHeartbeats 800000 in
/-- Both literal endpoint-dependent normalized A6 errors are bounded by the
same endpoint-free scalar majorant.  The hypothesis `EA6 ≤ 1` is explicit:
it is exactly what permits the finite replacement of the raw mass by `4`. -/
theorem ndA5ReferenceInteriorA6Errors_le_scalarMajorant
    {B j M : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C c kappa : ℝ}
    (hPhase : PhaseGap c kappa)
    (hB : 1 ≤ B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C)
    (hTube : NDA5InteriorTubeFacts B j branch C (M : ℝ))
    (hmass :
      |ndA5BandRawMass B branch C j (M : ℝ) -
          1 / ndA5PhaseDelta| ≤
        3650000 * (C + C ^ 3) * ndA6PhysicalRate B)
    (hEA6One :
      3650000 * (C + C ^ 3) * ndA6PhysicalRate B ≤ 1) :
    ndA5HarmonicReferenceInteriorA6Error
          B branch C j M c kappa ≤
        ndA5ReferenceInteriorScalarMajorant B C c kappa ∧
      ndA5FlatReferenceInteriorA6Error
          B branch C j M c kappa ≤
        ndA5ReferenceInteriorScalarMajorant B C c kappa := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) (M : ℝ)
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let lo : ℝ := ndA5TubeLo A W
  let N : ℝ := Tao.taoSection5N0 B
  let rho := ndA6PhysicalRate B
  let EA6 := 3650000 * (C + C ^ 3) * rho
  let Z0 := ndA5TubeRawMass A W
  let beta := ndA5BandBeta B branch
  let geom := 64 * (I0.card : ℝ) * W / lo
  let phase :=
    (6 + 2 / (Real.pi * c)) * Real.rpow W (-1 / kappa) *
      ((475328 / 25 : ℝ) * C ^ 2 * Real.log N)
  let shift :=
    (2 * (4244 / 100 : ℝ) * C * 4 + 24) * rho
  let common :=
    84 * phase + 12 * shift + 15 * EA6 +
      12 / ((B : ℝ) * ndA5LogFourThirds)
  have hW142 : (142 : ℝ) ≤ W := by
    simpa only [W] using
      ndA5TubeWidth_ge_one_hundred_forty_two hC hlogB
  have hWpos : 0 < W := by linarith
  have hloPos : 0 < lo := by
    dsimp only [lo]
    exact_mod_cast hTube.lo_pos
  have hloOne : (1 : ℝ) ≤ lo := by
    dsimp only [lo]
    exact_mod_cast hTube.lo_pos
  have hratioAll := ndA6PhysicalN0_div_tubeLo_mem_Icc hTube
  have hNlower : (1374 / 100 : ℝ) * lo ≤ N :=
    (le_div_iff₀ hloPos).mp (by
      simpa only [N, lo, A, W] using hratioAll.1)
  have hNpos : 0 < N := by nlinarith
  have hsqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hinvSqrt : 1 / Real.sqrt N ≤ rho := by
    simpa only [N, rho] using
      one_div_sqrt_taoSection5N0_le_ndA6PhysicalRate_of_interior hTube
  have hrhoPos : 0 < rho :=
    (div_pos (by norm_num) hsqrtNpos).trans_le hinvSqrt
  have hrho0 : 0 ≤ rho := hrhoPos.le
  have hC0 : 0 ≤ C := by linarith
  have hEA60 : 0 ≤ EA6 := by
    dsimp only [EA6]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by nlinarith [sq_nonneg C])) hrho0
  have hEA6One' : EA6 ≤ 1 := by
    simpa only [EA6, rho] using hEA6One
  have hZ :=
    ndA5ReferenceInteriorRawMass_le_four
      hC hlogB hTube (by simpa only [EA6, rho] using hmass) hEA6One'
  have hZ' : 0 ≤ Z0 ∧ Z0 ≤ 4 := by
    simpa only [A, W, Z0] using hZ
  have hZ0 := hZ'.1
  have hZ4 := hZ'.2
  have hDbar :
      ndEndpointDbar c kappa I0.card ≤
        (6 + 2 / (Real.pi * c)) * Real.rpow W (-1 / kappa) := by
    simpa only [A, W, I0] using
      ndA5ReferenceInteriorDbar_le hC hlogB hPhase hTube
  have hgeom :
      geom ≤ (475328 / 25 : ℝ) * C ^ 2 * Real.log N := by
    simpa only [A, W, I0, lo, N, geom] using
      ndA5ReferenceInteriorGeometryFactor_le hC hlogB hTube
  have hDbar0 : 0 ≤ ndEndpointDbar c kappa I0.card :=
    ndEndpointDbar_nonneg hPhase I0.card
  have hgeom0 : 0 ≤ geom := by
    dsimp only [geom]
    positivity
  have hphaseUpper0 :
      0 ≤ (6 + 2 / (Real.pi * c)) * Real.rpow W (-1 / kappa) := by
    have hden : 0 < Real.pi * c := mul_pos Real.pi_pos hPhase.c_pos
    have hcst : 0 ≤ 6 + 2 / (Real.pi * c) := by
      have : 0 < 2 / (Real.pi * c) := div_pos (by norm_num) hden
      linarith
    exact mul_nonneg hcst (Real.rpow_nonneg hWpos.le _)
  have hgeomUpper0 :
      0 ≤ (475328 / 25 : ℝ) * C ^ 2 * Real.log N := by
    have hNone : (1 : ℝ) ≤ N := by nlinarith
    positivity
  have hphaseRaw :
      ndEndpointDbar c kappa I0.card * geom ≤ phase := by
    dsimp only [phase]
    exact mul_le_mul hDbar hgeom hgeom0 hphaseUpper0
  have hphaseRaw0 :
      0 ≤ ndEndpointDbar c kappa I0.card * geom :=
    mul_nonneg hDbar0 hgeom0
  have hphase0 : 0 ≤ phase := by
    dsimp only [phase]
    exact mul_nonneg hphaseUpper0 hgeomUpper0
  have hratio : W / lo ≤ (4244 / 100 : ℝ) * C * rho := by
    simpa only [ndA6PhysicalLinearRatio, A, W, lo, rho] using
      ndA6PhysicalLinearRatio_le_rate hTube
  have hratio0 : 0 ≤ W / lo := div_nonneg hWpos.le hloPos.le
  have hratioUpper0 : 0 ≤ (4244 / 100 : ℝ) * C * rho := by positivity
  have hratioZ :
      (W / lo) * Z0 ≤ ((4244 / 100 : ℝ) * C * rho) * 4 :=
    mul_le_mul hratio hZ4 hZ0 hratioUpper0
  have hshiftRaw :
      2 * (W / lo) * Z0 + 24 / Real.sqrt N ≤ shift := by
    dsimp only [shift]
    calc
      2 * (W / lo) * Z0 + 24 / Real.sqrt N =
          2 * ((W / lo) * Z0) + 24 * (1 / Real.sqrt N) := by ring
      _ ≤ 2 * (((4244 / 100 : ℝ) * C * rho) * 4) + 24 * rho :=
        add_le_add
          (mul_le_mul_of_nonneg_left hratioZ (by norm_num))
          (mul_le_mul_of_nonneg_left hinvSqrt (by norm_num))
      _ = (2 * (4244 / 100 : ℝ) * C * 4 + 24) * rho := by ring
  have hshiftRaw0 :
      0 ≤ 2 * (W / lo) * Z0 + 24 / Real.sqrt N := by positivity
  have hshift0 : 0 ≤ shift := by
    dsimp only [shift]
    positivity
  have hbeta0 : 0 ≤ beta := by
    simpa only [beta] using ndA5BandBeta_nonneg hB branch
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbetaRatio : beta / Real.log 2 ≤ 2 := by
    apply (div_le_iff₀ hlogTwoPos).2
    simpa only [beta] using
      (ndA5BandBeta_lt_two_mul_logTwo
        (branch := branch) hB hlogB).le
  have hexpFour : Real.exp beta ≤ 4 := by
    simpa only [beta] using
      (exp_ndA5BandBeta_lt_four
        (branch := branch) hB hlogB).le
  have hflatFactor0 : 0 ≤ 2 * Real.exp beta - 1 := by
    nlinarith [Real.one_le_exp hbeta0]
  have hflatFactorSeven : 2 * Real.exp beta - 1 ≤ 7 := by
    linarith
  have hflatMean0 : 0 ≤ ndA5FlatPhaseMean beta := by
    unfold ndA5FlatPhaseMean
    exact div_nonneg (by nlinarith [Real.one_le_exp hbeta0]) hlogTwoPos.le
  have hflatMeanFive : ndA5FlatPhaseMean beta ≤ 5 := by
    unfold ndA5FlatPhaseMean
    apply (div_le_iff₀ hlogTwoPos).2
    have hlogTwoLower : (69 / 100 : ℝ) < Real.log 2 := by
      have h := Real.log_two_gt_d9
      norm_num at h ⊢
      linarith
    nlinarith
  have hP : Z0 *
        (ndEndpointDbar c kappa I0.card * geom) ≤ 4 * phase := by
    calc
      Z0 * (ndEndpointDbar c kappa I0.card * geom) ≤
          4 * (ndEndpointDbar c kappa I0.card * geom) :=
        mul_le_mul_of_nonneg_right hZ4 hphaseRaw0
      _ ≤ 4 * phase :=
        mul_le_mul_of_nonneg_left hphaseRaw (by norm_num)
  have hP0 :
      0 ≤ Z0 * (ndEndpointDbar c kappa I0.card * geom) :=
    mul_nonneg hZ0 hphaseRaw0
  have hRawH :
      ndA5ReciprocalTwoProfileA6Error
          B branch C j (M : ℝ) EA6 c kappa ≤
        4 * phase + shift + 2 * EA6 := by
    change Z0 * (ndEndpointDbar c kappa I0.card * geom) +
        (2 * (W / lo) * Z0 + 24 / Real.sqrt N) +
        (beta / Real.log 2) * EA6 ≤
      4 * phase + shift + 2 * EA6
    exact add_le_add
      (add_le_add hP hshiftRaw)
      (mul_le_mul_of_nonneg_right hbetaRatio hEA60)
  have hRawF :
      ndA5FlatTwoProfileA6Error
          B branch C j (M : ℝ) EA6 c kappa ≤
        28 * phase + 4 * shift + 5 * EA6 := by
    change Z0 * ((2 * Real.exp beta - 1) *
          ndEndpointDbar c kappa I0.card * geom) +
        Real.exp beta *
          (2 * (W / lo) * Z0 + 24 / Real.sqrt N) +
        ndA5FlatPhaseMean beta * EA6 ≤
      28 * phase + 4 * shift + 5 * EA6
    have hflatPhase :
        Z0 * ((2 * Real.exp beta - 1) *
            ndEndpointDbar c kappa I0.card * geom) ≤ 28 * phase := by
      calc
        Z0 * ((2 * Real.exp beta - 1) *
            ndEndpointDbar c kappa I0.card * geom) =
            (2 * Real.exp beta - 1) *
              (Z0 * (ndEndpointDbar c kappa I0.card * geom)) := by ring
        _ ≤ 7 * (Z0 *
            (ndEndpointDbar c kappa I0.card * geom)) :=
          mul_le_mul_of_nonneg_right hflatFactorSeven hP0
        _ ≤ 7 * (4 * phase) :=
          mul_le_mul_of_nonneg_left hP (by norm_num)
        _ = 28 * phase := by ring
    have hflatShift : Real.exp beta *
        (2 * (W / lo) * Z0 + 24 / Real.sqrt N) ≤ 4 * shift := by
      calc
        Real.exp beta *
            (2 * (W / lo) * Z0 + 24 / Real.sqrt N) ≤
            4 * (2 * (W / lo) * Z0 + 24 / Real.sqrt N) :=
          mul_le_mul_of_nonneg_right hexpFour hshiftRaw0
        _ ≤ 4 * shift :=
          mul_le_mul_of_nonneg_left hshiftRaw (by norm_num)
    exact add_le_add (add_le_add hflatPhase hflatShift)
      (mul_le_mul_of_nonneg_right hflatMeanFive hEA60)
  have hz : (B : ℝ) ≤ ndA5BandLower B branch j :=
    cast_le_ndA5BandLower hB branch j
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hden : (B : ℝ) * ndA5LogFourThirds ≤
      ndA5BandLower B branch j * ndA5LogFourThirds :=
    mul_le_mul_of_nonneg_right hz ndA5LogFourThirds_pos.le
  have hres12 :
      12 / (ndA5BandLower B branch j * ndA5LogFourThirds) ≤
        12 / ((B : ℝ) * ndA5LogFourThirds) :=
    div_le_div_of_nonneg_left (by norm_num)
      (mul_pos hBpos ndA5LogFourThirds_pos) hden
  have hres6 :
      6 / (ndA5BandLower B branch j * ndA5LogFourThirds) ≤
        12 / ((B : ℝ) * ndA5LogFourThirds) := by
    calc
      6 / (ndA5BandLower B branch j * ndA5LogFourThirds) ≤
          6 / ((B : ℝ) * ndA5LogFourThirds) :=
        div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hBpos ndA5LogFourThirds_pos) hden
      _ ≤ 12 / ((B : ℝ) * ndA5LogFourThirds) :=
        div_le_div_of_nonneg_right (by norm_num)
          (mul_pos hBpos ndA5LogFourThirds_pos).le
  have hH : ndA5HarmonicReferenceInteriorA6Error
      B branch C j M c kappa ≤ common := by
    change 4 * ndA5ReciprocalTwoProfileA6Error
          B branch C j (M : ℝ) EA6 c kappa +
        12 / (ndA5BandLower B branch j * ndA5LogFourThirds) ≤ common
    calc
      _ ≤ 4 * (4 * phase + shift + 2 * EA6) +
            12 / ((B : ℝ) * ndA5LogFourThirds) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hRawH (by norm_num)) hres12
      _ ≤ common := by
        dsimp only [common]
        nlinarith
  have hF : ndA5FlatReferenceInteriorA6Error
      B branch C j M c kappa ≤ common := by
    change 3 * ndA5FlatTwoProfileA6Error
          B branch C j (M : ℝ) EA6 c kappa +
        6 / (ndA5BandLower B branch j * ndA5LogFourThirds) ≤ common
    calc
      _ ≤ 3 * (28 * phase + 4 * shift + 5 * EA6) +
            12 / ((B : ℝ) * ndA5LogFourThirds) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hRawF (by norm_num)) hres6
      _ = common := by
        dsimp only [common]
        ring
  have hcommon :
      common = ndA5ReferenceInteriorScalarMajorant B C c kappa := by
    dsimp only [common, phase, shift, EA6, rho, W, N]
    unfold ndA5ReferenceInteriorScalarMajorant
    ring
  exact ⟨hH.trans_eq hcommon, hF.trans_eq hcommon⟩

/-- A fixed linear combination of the three real-scale rows occurring in
the scalar majorant is little-o of every strictly weaker power. -/
private theorem eventually_ndA5ReferenceInterior_real_envelope
    {K1 K2 K3 q d ε : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3)
    (hdq : d < q) (hdhalf : d < 1 / 2) (hdone : d < 1)
    (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      K1 * Real.log x * Real.rpow x (-q) +
          K2 * Real.rpow (Real.log x) (3 / 2 : ℝ) *
            Real.rpow x (-(1 / 2 : ℝ)) +
          K3 * Real.rpow x (-1 : ℝ) ≤
        ε * Real.rpow x (-d) := by
  let ε1 := ε / (3 * K1)
  let ε2 := ε / (3 * K2)
  let ε3 := ε / (3 * K3)
  have hε1 : 0 < ε1 := by dsimp only [ε1]; positivity
  have hε2 : 0 < ε2 := by dsimp only [ε2]; positivity
  have hε3 : 0 < ε3 := by dsimp only [ε3]; positivity
  have hsmall1 :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (sub_pos.mpr hdq)).bound hε1
  have hsmall2 :=
    (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
      (sub_pos.mpr hdhalf)).bound hε2
  have hsmall3 :=
    (isLittleO_log_rpow_rpow_atTop (0 : ℝ)
      (sub_pos.mpr hdone)).bound hε3
  filter_upwards [hsmall1, hsmall2, hsmall3,
      eventually_gt_atTop (1 : ℝ)] with x hx1 hx2 hx3 hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hpow1pos : 0 < Real.rpow x (q - d) := Real.rpow_pos_of_pos hxpos _
  have hpow2pos : 0 < Real.rpow x (1 / 2 - d) :=
    Real.rpow_pos_of_pos hxpos _
  have hpow3pos : 0 < Real.rpow x (1 - d) := Real.rpow_pos_of_pos hxpos _
  have hnormLog1 : ‖Real.rpow (Real.log x) (1 : ℝ)‖ = Real.log x := by
    rw [Real.rpow_eq_pow, Real.rpow_one, Real.norm_eq_abs,
      abs_of_pos hlogpos]
  have hnormLog2 : ‖Real.rpow (Real.log x) (3 / 2 : ℝ)‖ =
      Real.rpow (Real.log x) (3 / 2 : ℝ) := by
    rw [Real.rpow_eq_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlogpos.le _)]
  have hnormLog3 : ‖Real.rpow (Real.log x) (0 : ℝ)‖ = 1 := by
    rw [Real.rpow_eq_pow, Real.rpow_zero, norm_one]
  have hnormPow1 : ‖Real.rpow x (q - d)‖ = Real.rpow x (q - d) := by
    rw [Real.rpow_eq_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  have hnormPow2 : ‖Real.rpow x (1 / 2 - d)‖ =
      Real.rpow x (1 / 2 - d) := by
    rw [Real.rpow_eq_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  have hnormPow3 : ‖Real.rpow x (1 - d)‖ = Real.rpow x (1 - d) := by
    rw [Real.rpow_eq_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  simp only [← Real.rpow_eq_pow] at hx1 hx2 hx3
  have hs1 : Real.log x ≤ ε1 * Real.rpow x (q - d) := by
    simpa only [hnormLog1, hnormPow1] using hx1
  have hs2 : Real.rpow (Real.log x) (3 / 2 : ℝ) ≤
      ε2 * Real.rpow x (1 / 2 - d) := by
    simpa only [hnormLog2, hnormPow2] using hx2
  have hs3 : (1 : ℝ) ≤ ε3 * Real.rpow x (1 - d) := by
    simpa only [hnormLog3, hnormPow3] using hx3
  have hprod1 : Real.rpow x (q - d) * Real.rpow x (-q) =
      Real.rpow x (-d) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hprod2 : Real.rpow x (1 / 2 - d) *
      Real.rpow x (-(1 / 2 : ℝ)) = Real.rpow x (-d) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hprod3 : Real.rpow x (1 - d) * Real.rpow x (-1 : ℝ) =
      Real.rpow x (-d) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hp1 :
      K1 * Real.log x * Real.rpow x (-q) ≤
        (ε / 3) * Real.rpow x (-d) := by
    calc
      K1 * Real.log x * Real.rpow x (-q) ≤
          K1 * (ε1 * Real.rpow x (q - d)) * Real.rpow x (-q) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs1 hK1.le)
          (Real.rpow_nonneg hxpos.le _)
      _ = (K1 * ε1) *
          (Real.rpow x (q - d) * Real.rpow x (-q)) := by ring
      _ = (ε / 3) * Real.rpow x (-d) := by
        rw [hprod1]
        dsimp only [ε1]
        field_simp [hK1.ne']
  have hp2 :
      K2 * Real.rpow (Real.log x) (3 / 2 : ℝ) *
          Real.rpow x (-(1 / 2 : ℝ)) ≤
        (ε / 3) * Real.rpow x (-d) := by
    calc
      K2 * Real.rpow (Real.log x) (3 / 2 : ℝ) *
          Real.rpow x (-(1 / 2 : ℝ)) ≤
          K2 * (ε2 * Real.rpow x (1 / 2 - d)) *
            Real.rpow x (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs2 hK2.le)
          (Real.rpow_nonneg hxpos.le _)
      _ = (K2 * ε2) *
          (Real.rpow x (1 / 2 - d) *
            Real.rpow x (-(1 / 2 : ℝ))) := by ring
      _ = (ε / 3) * Real.rpow x (-d) := by
        rw [hprod2]
        dsimp only [ε2]
        field_simp [hK2.ne']
  have hp3 :
      K3 * Real.rpow x (-1 : ℝ) ≤
        (ε / 3) * Real.rpow x (-d) := by
    calc
      K3 * Real.rpow x (-1 : ℝ) ≤
          K3 * (ε3 * Real.rpow x (1 - d)) *
            Real.rpow x (-1 : ℝ) := by
        rw [show K3 * Real.rpow x (-1 : ℝ) =
          K3 * 1 * Real.rpow x (-1 : ℝ) by ring]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs3 hK3.le)
          (Real.rpow_nonneg hxpos.le _)
      _ = (K3 * ε3) *
          (Real.rpow x (1 - d) * Real.rpow x (-1 : ℝ)) := by ring
      _ = (ε / 3) * Real.rpow x (-d) := by
        rw [hprod3]
        dsimp only [ε3]
        field_simp [hK3.ne']
  linarith

/-- The Section-5 floor schedule eventually retains at least one twentieth
of the real source logarithm. -/
theorem eventually_log_div_twenty_le_taoSection5N0 :
    ∀ᶠ B : ℕ in atTop,
      Real.log B / 20 ≤ (Tao.taoSection5N0 B : ℝ) := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (20 : ℝ)] with B hlarge
  let L : ℝ := Real.log B
  let N : ℝ := Tao.taoSection5N0 B
  let ell : ℝ := Real.log 2
  have hL20 : (20 : ℝ) ≤ L := by simpa only [L] using hlarge
  have hL0 : 0 ≤ L := by linarith
  have hell : 0 < ell := Real.log_pos (by norm_num)
  have hellOne : ell < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hnLower : L / (10 * ell) - 1 < N := by
    simpa only [L, N, ell] using
      Tao.log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hratio : L / 10 ≤ L / (10 * ell) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hell)).2
    calc
      L / 10 * (10 * ell) = L * ell := by ring
      _ ≤ L * 1 := mul_le_mul_of_nonneg_left hellOne.le hL0
      _ = L := mul_one L
  simpa only [L, N] using (show L / 20 ≤ N by linarith)

/-- The endpoint-free finite majorant is eventually smaller than every
strictly admissible source-logarithmic rate. -/
theorem eventually_ndA5ReferenceInteriorScalarMajorant_le
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa d ε : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hdk : d < 1 / (2 * kappa))
    (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop,
      ndA5ReferenceInteriorScalarMajorant B C c kappa ≤
        ε * ndA5ReferenceInteriorScalarRate B d := by
  let q : ℝ := 1 / (2 * kappa)
  let K1 : ℝ :=
    (39927552 / 25 : ℝ) * (6 + 2 / (Real.pi * c)) * C ^ 2
  let K2 : ℝ :=
    (101856 / 25 : ℝ) * C + 288 + 54750000 * (C + C ^ 3)
  let K3 : ℝ := 12 / ndA5LogFourThirds
  let εN : ℝ := ε * Real.rpow 20 (-d)
  have hkappa : 0 < kappa := by linarith [hPhase.two_lt_kappa]
  have hqhalf : q < 1 / 2 := by
    dsimp only [q]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hkappa)).2
    nlinarith [hPhase.two_lt_kappa]
  have hdq : d < q := by simpa only [q] using hdk
  have hdhalf : d < 1 / 2 := hdq.trans hqhalf
  have hdone : d < 1 := hdhalf.trans (by norm_num)
  have hK1 : 0 < K1 := by
    dsimp only [K1]
    have hden : 0 < Real.pi * c := mul_pos Real.pi_pos hPhase.c_pos
    have hcst : 0 < 6 + 2 / (Real.pi * c) := by
      have : 0 < 2 / (Real.pi * c) := div_pos (by norm_num) hden
      linarith
    positivity
  have hK2 : 0 < K2 := by
    dsimp only [K2]
    have hCpos : 0 < C := by linarith
    have hsum : 0 < C + C ^ 3 := by nlinarith [sq_nonneg C]
    positivity
  have hK3 : 0 < K3 := by
    dsimp only [K3]
    exact div_pos (by norm_num) ndA5LogFourThirds_pos
  have hεN : 0 < εN := by
    dsimp only [εN]
    exact mul_pos hε (by
      rw [Real.rpow_eq_pow]
      positivity)
  have hreal := eventually_ndA5ReferenceInterior_real_envelope
    hK1 hK2 hK3 hdq hdhalf hdone hεN
  have hschedule : Tendsto
      (fun B : ℕ => (Tao.taoSection5N0 B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ndTendsto_taoSection5N0_atTop
  have hrealB := hschedule.eventually hreal
  filter_upwards
      [hrealB,
        hschedule.eventually_ge_atTop (Real.exp 4),
        eventually_log_div_twenty_le_taoSection5N0,
        Filter.eventually_ge_atTop (3 : ℕ)]
      with B henvelope hNlarge hlogTwenty hBthree
  let N : ℝ := Tao.taoSection5N0 B
  let L : ℝ := Real.log N
  let W : ℝ := ndA5TubeWidth B C
  have hNpos : 0 < N := (Real.exp_pos 4).trans_le
    (by simpa only [N] using hNlarge)
  have hLfour : (4 : ℝ) ≤ L := by
    dsimp only [L]
    exact (Real.le_log_iff_exp_le hNpos).2 (by simpa only [N] using hNlarge)
  have hL0 : 0 ≤ L := by linarith
  have hsqrtL : (2 : ℝ) ≤ Real.sqrt L := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hWform : W = C * (Real.sqrt N * Real.sqrt L) := by
    dsimp only [W, N, L, ndA5TubeWidth]
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  have hsqrtNW : Real.sqrt N ≤ W := by
    rw [hWform]
    calc
      Real.sqrt N = (1 / 2 : ℝ) * (Real.sqrt N * 2) := by ring
      _ ≤ (1 / 2 : ℝ) * (Real.sqrt N * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsqrtL (Real.sqrt_nonneg N))
          (by norm_num)
      _ ≤ C * (Real.sqrt N * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
  have hexp : -1 / kappa ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hkappa.le
  have hwidthPow : Real.rpow W (-1 / kappa) ≤ Real.rpow N (-q) := by
    have hWpos : 0 < W := hsqrtNpos.trans_le hsqrtNW
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
    calc
      W ^ (-1 / kappa) ≤ (Real.sqrt N) ^ (-1 / kappa) :=
        Real.rpow_le_rpow_of_nonpos hsqrtNpos hsqrtNW hexp
      _ = N ^ (-q) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
        congr 1
        dsimp only [q]
        ring
  have hK1L0 : 0 ≤ K1 * L := mul_nonneg hK1.le hL0
  have hphase :
      K1 * L * Real.rpow W (-1 / kappa) ≤
        K1 * L * Real.rpow N (-q) :=
    mul_le_mul_of_nonneg_left hwidthPow hK1L0
  have hrho : ndA6PhysicalRate B =
      Real.rpow L (3 / 2 : ℝ) * Real.rpow N (-(1 / 2 : ℝ)) := by
    dsimp only [ndA6PhysicalRate, N, L]
    rw [div_eq_mul_inv, Real.sqrt_eq_rpow]
    rw [← Real.rpow_neg hNpos.le]
    simp only [← Real.rpow_eq_pow]
    rfl
  have hphys : K2 * ndA6PhysicalRate B =
      K2 * Real.rpow L (3 / 2 : ℝ) *
        Real.rpow N (-(1 / 2 : ℝ)) := by rw [hrho]; ring
  have hNBnat : Tao.taoSection5N0 B ≤ B := by
    unfold Tao.taoSection5N0
    exact (Nat.div_le_self (Nat.log 2 B) 10).trans (Nat.log_le_self 2 B)
  have hNB : N ≤ (B : ℝ) := by
    dsimp only [N]
    exact_mod_cast hNBnat
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlast :
      12 / ((B : ℝ) * ndA5LogFourThirds) ≤
        K3 * Real.rpow N (-1 : ℝ) := by
    calc
      12 / ((B : ℝ) * ndA5LogFourThirds) ≤
          12 / (N * ndA5LogFourThirds) := by
        apply (div_le_div_iff₀
          (mul_pos hBpos ndA5LogFourThirds_pos)
          (mul_pos hNpos ndA5LogFourThirds_pos)).2
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hNB ndA5LogFourThirds_pos.le)
          (by norm_num)
      _ = K3 * Real.rpow N (-1 : ℝ) := by
        dsimp only [K3]
        rw [Real.rpow_eq_pow, Real.rpow_neg_one]
        field_simp [hNpos.ne', ndA5LogFourThirds_pos.ne']
  have hmajorant :
      ndA5ReferenceInteriorScalarMajorant B C c kappa ≤
        K1 * L * Real.rpow N (-q) +
          K2 * Real.rpow L (3 / 2 : ℝ) *
            Real.rpow N (-(1 / 2 : ℝ)) +
          K3 * Real.rpow N (-1 : ℝ) := by
    unfold ndA5ReferenceInteriorScalarMajorant
    change K1 * L * Real.rpow W (-1 / kappa) +
        K2 * ndA6PhysicalRate B +
        12 / ((B : ℝ) * ndA5LogFourThirds) ≤ _
    exact add_le_add (add_le_add hphase hphys.le) hlast
  have henvelope' :
      K1 * L * Real.rpow N (-q) +
          K2 * Real.rpow L (3 / 2 : ℝ) *
            Real.rpow N (-(1 / 2 : ℝ)) +
          K3 * Real.rpow N (-1 : ℝ) ≤
        εN * Real.rpow N (-d) := by
    simpa only [N, L] using henvelope
  have hlogBpos : 0 < Real.log B := by
    apply Real.log_pos
    exact_mod_cast (show 1 < B by omega)
  have hlogLe : Real.log B ≤ 20 * N := by
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 20)).mp hlogTwenty
    simpa only [N, mul_comm] using h
  have hscalePow : Real.rpow (20 * N) (-d) ≤
      Real.rpow (Real.log B) (-d) := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
    exact Real.rpow_le_rpow_of_nonpos hlogBpos hlogLe (by linarith)
  have hsplit :
      Real.rpow 20 (-d) * Real.rpow N (-d) =
        Real.rpow (20 * N) (-d) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 20) hNpos.le]
  calc
    ndA5ReferenceInteriorScalarMajorant B C c kappa ≤
        K1 * L * Real.rpow N (-q) +
          K2 * Real.rpow L (3 / 2 : ℝ) *
            Real.rpow N (-(1 / 2 : ℝ)) +
          K3 * Real.rpow N (-1 : ℝ) := hmajorant
    _ ≤ εN * Real.rpow N (-d) := henvelope'
    _ = ε * Real.rpow (20 * N) (-d) := by
      dsimp only [εN]
      rw [mul_assoc, hsplit]
    _ ≤ ε * Real.rpow (Real.log B) (-d) :=
      mul_le_mul_of_nonneg_left hscalePow hε.le
    _ = ε * ndA5ReferenceInteriorScalarRate B d := by rfl

/-- Uniform pointwise interior A6 decay, retaining exactly the original
natural endpoint and its closed interior guard. -/
theorem eventually_ndA5ReferenceInteriorA6Errors_le
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa d ε : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hdk : d < 1 / (2 * kappa))
    (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ),
        j < ndA5BandCount B branch →
          ∀ M : ℕ, 0 < M →
            |ndA5InteriorShift B (M : ℝ)| ≤
                (4 / 25 : ℝ) * ndA5TubeWidth B C →
              ndA5HarmonicReferenceInteriorA6Error
                    B branch C j M c kappa ≤
                  ε * ndA5ReferenceInteriorScalarRate B d ∧
                ndA5FlatReferenceInteriorA6Error
                    B branch C j M c kappa ≤
                  ε * ndA5ReferenceInteriorScalarRate B d := by
  let K : ℝ := 3650000 * (C + C ^ 3)
  have hCpos : 0 < C := by linarith
  have hK : 0 < K := by
    dsimp only [K]
    have hsum : 0 < C + C ^ 3 := by nlinarith [sq_nonneg C]
    positivity
  have hsmallRate :
      ∀ᶠ B : ℕ in atTop, ndA6PhysicalRate B < 1 / K :=
    tendsto_ndA6PhysicalRate_zero.eventually_lt_const (by positivity)
  have hEA6One :
      ∀ᶠ B : ℕ in atTop,
        3650000 * (C + C ^ 3) * ndA6PhysicalRate B ≤ 1 := by
    filter_upwards [hsmallRate] with B hsmall
    dsimp only [K] at hsmall hK
    simpa only [mul_comm] using ((lt_div_iff₀ hK).mp hsmall).le
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [Filter.eventually_ge_atTop (1 : ℕ),
        hlog.eventually_ge_atTop (300000 : ℝ),
        eventually_three_mul_ndA5TubeWidth_le_log C hCpos,
        eventually_a6PhysicalInterior C hC,
        hEA6One,
        eventually_ndA5ReferenceInteriorScalarMajorant_le
          C hC hPhase hd hdk hε]
      with B hB hlogB hpadding hmass hsmall hscalar
  intro branch j hj M hM hshift
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hTube : NDA5InteriorTubeFacts B j branch C (M : ℝ) :=
    ndA5InteriorTubeFacts_of_guards
      hB hlogB hC hMreal hpadding hshift hj
  have hfinite := ndA5ReferenceInteriorA6Errors_le_scalarMajorant
    hPhase hB hlogB hC hTube (hmass branch j hj (M : ℝ) hMreal hshift)
      hsmall
  exact ⟨hfinite.1.trans hscalar, hfinite.2.trans hscalar⟩

/-- A uniform scalar pointwise bound passes through the nonnegative reference
kernel with no cardinality loss. -/
theorem sum_ndA5ReferenceEndpointKernel_mul_le_commonZ
    {m : ℕ} {S : Finset ℕ} {e : ℕ → ℝ} {r : ℝ}
    (hpoint : ∀ M ∈ S, e M ≤ r) :
    (∑ M ∈ S, ndA5ReferenceEndpointKernel m M * e M) ≤
      r * Tao.taoSection5PayloadFreeCommonZ m S := by
  calc
    (∑ M ∈ S, ndA5ReferenceEndpointKernel m M * e M) ≤
        ∑ M ∈ S, ndA5ReferenceEndpointKernel m M * r := by
      apply Finset.sum_le_sum
      intro M hM
      exact mul_le_mul_of_nonneg_left
        (hpoint M hM) (ndA5ReferenceEndpointKernel_nonneg m M)
    _ = r * (∑ M ∈ S, ndA5ReferenceEndpointKernel m M) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _hM
      ring
    _ = r * Tao.taoSection5PayloadFreeCommonZ m S := by
      rw [sum_ndA5ReferenceEndpointKernel_eq_commonZ]

/-- Reusable mass-relative two-law decay on the closed original-endpoint
interior carrier. -/
def NDA5ReferenceInteriorDecayAt
    (B : ℕ) (C d : ℝ) : Prop :=
  ∀ (m : ℕ) (branch : Tao.TaoSection5SourceBranch)
      (j : ℕ) (E : Set ℕ),
    j < ndA5BandCount B branch →
      let Int := ndA5ReferenceInteriorEndpoints B C E
      (|ndA5HarmonicReferencePhysicalProfileOn B m branch C j Int -
            (2 / ndA5LogFourThirds) *
              Tao.taoSection5PayloadFreeCommonZ m Int| ≤
          ndA5ReferenceInteriorScalarRate B d *
            Tao.taoSection5PayloadFreeCommonZ m Int) ∧
        (|ndA5FlatReferencePhysicalProfileOn B m branch C j Int -
            (2 / ndA5LogFourThirds) *
              Tao.taoSection5PayloadFreeCommonZ m Int| ≤
          ndA5ReferenceInteriorScalarRate B d *
            Tao.taoSection5PayloadFreeCommonZ m Int)

/-- Eventual arbitrary-reference-level interior decay.  The CommonZ factor
remains visible here; the fixed scheduler supplies its cap in the next
consumer. -/
theorem eventually_ndA5ReferenceInteriorDecay
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      NDA5ReferenceInteriorDecayAt B C d := by
  filter_upwards
      [eventually_ndA5ReferenceInteriorAggregate C hC hPhase,
        eventually_ndA5ReferenceInteriorA6Errors_le
          C hC hPhase hd hdk (by norm_num : (0 : ℝ) < 1)]
      with B haggregate hpoint
  rw [NDA5ReferenceInteriorDecayAt]
  intro m branch j E hj
  let Int := ndA5ReferenceInteriorEndpoints B C E
  have hagg := haggregate m branch j E hj
  have hHsum :
      (∑ M ∈ Int, ndA5ReferenceEndpointKernel m M *
          ndA5HarmonicReferenceInteriorA6Error
            B branch C j M c kappa) ≤
        ndA5ReferenceInteriorScalarRate B d *
          Tao.taoSection5PayloadFreeCommonZ m Int := by
    apply sum_ndA5ReferenceEndpointKernel_mul_le_commonZ
    intro M hM
    have hdata := mem_ndA5ReferenceInteriorEndpoints_iff.mp hM
    have hMpos : 0 < M :=
      Odd.pos (Tao.mem_taoSection5EPrime_iff.mp hdata.1).2.2.1
    simpa only [one_mul] using
      (hpoint branch j hj M hMpos hdata.2).1
  have hFsum :
      (∑ M ∈ Int, ndA5ReferenceEndpointKernel m M *
          ndA5FlatReferenceInteriorA6Error
            B branch C j M c kappa) ≤
        ndA5ReferenceInteriorScalarRate B d *
          Tao.taoSection5PayloadFreeCommonZ m Int := by
    apply sum_ndA5ReferenceEndpointKernel_mul_le_commonZ
    intro M hM
    have hdata := mem_ndA5ReferenceInteriorEndpoints_iff.mp hM
    have hMpos : 0 < M :=
      Odd.pos (Tao.mem_taoSection5EPrime_iff.mp hdata.1).2.2.1
    simpa only [one_mul] using
      (hpoint branch j hj M hMpos hdata.2).2
  simpa only [Int] using ⟨hagg.1.trans hHsum, hagg.2.trans hFsum⟩

/-- The scheduled reference level supplies the route-facing absolute
interior estimate.  The factor five comes only from the checked whole-EPrime
CommonZ cap under the visible lost-window and integer-index facts. -/
theorem eventually_ndA5ReferenceInteriorDecay_referenceLevel_le_five
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ),
        j < ndA5BandCount B branch →
          let Int := ndA5ReferenceInteriorEndpoints B C E
          (|ndA5HarmonicReferencePhysicalProfileOn B
                (ndA5ReferenceLevel B) branch C j Int -
              (2 / ndA5LogFourThirds) *
                Tao.taoSection5PayloadFreeCommonZ
                  (ndA5ReferenceLevel B) Int| ≤
            5 * ndA5ReferenceInteriorScalarRate B d) ∧
          (|ndA5FlatReferencePhysicalProfileOn B
                (ndA5ReferenceLevel B) branch C j Int -
              (2 / ndA5LogFourThirds) *
                Tao.taoSection5PayloadFreeCommonZ
                  (ndA5ReferenceLevel B) Int| ≤
            5 * ndA5ReferenceInteriorScalarRate B d) := by
  filter_upwards
      [eventually_ndA5ReferenceInteriorDecay C hC hPhase hd hdk,
        Tao.eventually_taoSection5PassLostWindowFacts,
        Tao.eventually_taoSection5PassScheduleFacts,
        eventually_ndA5ReferenceLevel_integer_room]
      with B hdecay lost schedule hroom
  intro branch j E hj
  let Int := ndA5ReferenceInteriorEndpoints B C E
  have hindex : Tao.taoSection5M0 B + ndA5ReferenceLevel B ≤
      Tao.taoSection5N0 B := by
    obtain ⟨n, hn⟩ := schedule.nonempty Tao.TaoSection5SourceBranch.alpha
    have hrange := schedule.range Tao.TaoSection5SourceBranch.alpha n hn
    have htwo : 2 * Tao.taoSection5M0 B ≤ Tao.taoSection5N0 B :=
      hrange.1.trans hrange.2
    omega
  have hsubset : Int ⊆ Tao.taoSection5EPrime B E := by
    intro M hM
    exact (mem_ndA5ReferenceInteriorEndpoints_iff.mp hM).1
  have hcapFull :=
    Tao.taoSection5PayloadFreeCommonZ_ePrime_mem_Icc_five
      lost (E := E) hindex
  have hcap : Tao.taoSection5PayloadFreeCommonZ
      (ndA5ReferenceLevel B) Int ≤ 5 :=
    (ndA5ReferenceCommonZ_mono hsubset).trans hcapFull.2
  have hrate0 : 0 ≤ ndA5ReferenceInteriorScalarRate B d := by
    unfold ndA5ReferenceInteriorScalarRate
    rw [Real.rpow_eq_pow]
    exact Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast schedule.one_le_B)) _
  have hscaled :
      ndA5ReferenceInteriorScalarRate B d *
          Tao.taoSection5PayloadFreeCommonZ
            (ndA5ReferenceLevel B) Int ≤
        5 * ndA5ReferenceInteriorScalarRate B d := by
    calc
      ndA5ReferenceInteriorScalarRate B d *
          Tao.taoSection5PayloadFreeCommonZ
            (ndA5ReferenceLevel B) Int ≤
          ndA5ReferenceInteriorScalarRate B d * 5 :=
        mul_le_mul_of_nonneg_left hcap hrate0
      _ = 5 * ndA5ReferenceInteriorScalarRate B d := by ring
  have hpair := hdecay (ndA5ReferenceLevel B) branch j E hj
  simpa only [Int] using
    ⟨hpair.1.trans hscaled, hpair.2.trans hscaled⟩

end
end ND
end Erdos1135
