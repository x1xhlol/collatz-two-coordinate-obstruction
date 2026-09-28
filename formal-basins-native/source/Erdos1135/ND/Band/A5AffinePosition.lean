import Erdos1135.ND.Band.A5ExactAffineCorrection
import Erdos1135.ND.Band.A5BandNormalizer
import Erdos1135.ND.Band.A5StrictBandLevels
import Erdos1135.Tao.Syracuse.AffineReciprocal

/-!
# A5 Exact and Nominal Affine Positions

This leaf freezes the sign and endpoint behavior of the once-only affine
correction.  For an exact affine source, the physical band position is the
nominal lattice position minus

`delta = -log (1 - F / M)`.

The physical band is half-open, whereas the nominal profile deliberately
uses strict endpoints.  The mismatch lemmas below therefore retain the sole
zero-length lower-endpoint case instead of hiding it in a generic boundary
estimate.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Exact logarithmic position of a positive source relative to a band lower
endpoint. -/
noncomputable def ndA5ExactAffinePosition (z : ℝ) (N : ℕ) : ℝ :=
  Real.log ((N : ℝ) / z)

/-- Nominal affine position obtained by dropping the offset `F` from the
exact denominator `M - F`.  This is definitionally the position expression
used by `ndA5NominalStrictBandLevel`. -/
noncomputable def ndA5NominalAffinePosition
    (z M : ℝ) (q L : ℕ) : ℝ :=
  ((L : ℝ) - (ndA5PhysicalPhase z M + (q : ℝ) * logTwoThree)) *
    Real.log 2

/-- Positive-direction correction from nominal to exact affine position. -/
noncomputable def ndA5AffinePositionCorrection
    (as : List ℕ+) (M : ℝ) : ℝ :=
  -Real.log (1 - (Tao.taoOffsetList as : ℝ) / M)

/-- Strict nominal membership used by the frozen phase profile. -/
def ndA5StrictPosition (beta u : ℝ) : Prop :=
  0 < u ∧ u < beta

/-- Half-open physical membership used by the actual A5 bands. -/
def ndA5HalfOpenPosition (beta u : ℝ) : Prop :=
  0 ≤ u ∧ u < beta

/-- The nominal position predicate is exactly the already checked strict
signed-level predicate after specializing its physical phase. -/
theorem ndA5NominalStrictBandLevel_iff_nominalPosition
    (beta z M : ℝ) (q L : ℕ) :
    ndA5NominalStrictBandLevel beta (ndA5PhysicalPhase z M) q (L : ℤ) ↔
      ndA5StrictPosition beta (ndA5NominalAffinePosition z M q L) := by
  simp only [ndA5NominalStrictBandLevel, ndA5StrictPosition,
    ndA5NominalAffinePosition, Int.cast_natCast]

/-- A logarithmic position is in the physical half-open interval exactly
when its source lies between the corresponding multiplicative endpoints. -/
theorem ndA5HalfOpenPosition_exact_iff
    {beta z : ℝ} {N : ℕ} (hz : 0 < z) (hN : 0 < N) :
    ndA5HalfOpenPosition beta (ndA5ExactAffinePosition z N) ↔
      z ≤ (N : ℝ) ∧ (N : ℝ) < z * Real.exp beta := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiv : 0 < (N : ℝ) / z := div_pos hNR hz
  unfold ndA5HalfOpenPosition ndA5ExactAffinePosition
  constructor
  · rintro ⟨hlower, hupper⟩
    have hone : (1 : ℝ) ≤ (N : ℝ) / z :=
      (Real.log_nonneg_iff hdiv).mp hlower
    have hupp : (N : ℝ) / z < Real.exp beta :=
      (Real.log_lt_iff_lt_exp hdiv).mp hupper
    constructor
    · have := (le_div_iff₀ hz).mp hone
      simpa only [one_mul] using this
    · have := (div_lt_iff₀ hz).mp hupp
      simpa only [mul_comm] using this
  · rintro ⟨hlower, hupper⟩
    constructor
    · apply (Real.log_nonneg_iff hdiv).mpr
      exact (le_div_iff₀ hz).mpr (by simpa only [one_mul] using hlower)
    · apply (Real.log_lt_iff_lt_exp hdiv).mpr
      exact (div_lt_iff₀ hz).mpr (by simpa only [mul_comm] using hupper)

/-- Actual A5 band membership, with oddness supplied by the source atom, is
exactly half-open membership of the exact logarithmic position. -/
theorem mem_ndA5OddBand_iff_halfOpen_exactPosition
    {B N j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hodd : N % 2 = 1) :
    N ∈ ndA5OddBand B branch j ↔
      ndA5HalfOpenPosition (ndA5BandBeta B branch)
        (ndA5ExactAffinePosition (ndA5BandLower B branch j) N) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hz : 0 < ndA5BandLower B branch j := by
    unfold ndA5BandLower
    exact mul_pos hYpos (Real.exp_pos _)
  have hN : 0 < N := by omega
  rw [mem_ndA5OddBand_exp_iff]
  constructor
  · rintro ⟨hlower, hupper, _⟩
    exact (ndA5HalfOpenPosition_exact_iff hz hN).2 ⟨hlower, hupper⟩
  · intro hposition
    rcases (ndA5HalfOpenPosition_exact_iff hz hN).1 hposition with
      ⟨hlower, hupper⟩
    exact ⟨hlower, hupper, hodd⟩

/-- A zero-length valuation tuple has zero affine offset. -/
theorem ndA5_taoOffsetList_eq_zero_of_length_eq_zero
    (as : List ℕ+) (hzero : as.length = 0) :
    Tao.taoOffsetList as = 0 := by
  have has : as = [] := List.length_eq_zero_iff.mp hzero
  subst as
  rfl

/-- Every nonempty valuation tuple has strictly positive affine offset. -/
theorem ndA5_taoOffsetList_pos_of_length_pos
    (as : List ℕ+) (hpos : 0 < as.length) :
    0 < Tao.taoOffsetList as := by
  have hne : as ≠ [] := List.length_pos_iff_ne_nil.mp hpos
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold Tao.taoOffsetList
  exact add_pos_of_pos_of_nonneg
    (div_pos (pow_pos (by norm_num) _)
      (pow_pos (by norm_num) _))
    (Tao.taoOffsetList_nonneg rest)

/-- Exact sign identity between physical and nominal affine positions.

The plus sign in the intermediate formula is load-bearing:
`uExact = uNominal + log (1 - F/M)`, hence the named nonnegative correction
is subtracted. -/
theorem ndA5_exactAffinePosition_eq_nominal_sub_correction
    {z : ℝ} {q M : ℕ} {as : List ℕ+} {N : Tao.TaoOddNat}
    (hz : 0 < z) (hlen : as.length = q)
    (hAff : Tao.taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    ndA5ExactAffinePosition z N.1 =
      ndA5NominalAffinePosition z M q (Tao.taoTupleWeight as) -
        ndA5AffinePositionCorrection as M := by
  have hNpos : (0 : ℝ) < N.1 := by
    exact_mod_cast Odd.pos N.2
  have hdenPos :
      0 < (M : ℝ) - (Tao.taoOffsetList as : ℝ) :=
    Tao.taoAffList_denominator_pos hlen hAff
  have hoffset0 : 0 ≤ (Tao.taoOffsetList as : ℝ) :=
    Rat.cast_nonneg.mpr (Tao.taoOffsetList_nonneg as)
  have hMpos : (0 : ℝ) < M := by linarith
  have hclosedQ :
      (M : ℚ) =
        (3 : ℚ) ^ as.length /
            (2 : ℚ) ^ Tao.taoTupleWeight as * (N.1 : ℚ) +
          Tao.taoOffsetList as :=
    hAff.symm.trans (Tao.taoAffList_closed as (N.1 : ℚ))
  have hclosedR := congrArg (fun x : ℚ => (x : ℝ)) hclosedQ
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat] at hclosedR
  have hdenEq :
      (M : ℝ) - (Tao.taoOffsetList as : ℝ) =
        (3 : ℝ) ^ q / (2 : ℝ) ^ Tao.taoTupleWeight as * (N.1 : ℝ) := by
    rw [hlen] at hclosedR
    linarith
  have hratioEq :
      1 - (Tao.taoOffsetList as : ℝ) / (M : ℝ) =
        ((M : ℝ) - (Tao.taoOffsetList as : ℝ)) / (M : ℝ) := by
    field_simp [hMpos.ne']
  have hlogExact :
      Real.log ((N.1 : ℝ) / z) = Real.log (N.1 : ℝ) - Real.log z := by
    rw [Real.log_div hNpos.ne' hz.ne']
  have hlogPhase :
      Real.log (z / (M : ℝ)) = Real.log z - Real.log (M : ℝ) := by
    rw [Real.log_div hz.ne' hMpos.ne']
  have hlogCorrection :
      Real.log (1 - (Tao.taoOffsetList as : ℝ) / (M : ℝ)) =
        Real.log ((M : ℝ) - (Tao.taoOffsetList as : ℝ)) -
          Real.log (M : ℝ) := by
    rw [hratioEq, Real.log_div hdenPos.ne' hMpos.ne']
  have hlogDenominator :
      Real.log ((M : ℝ) - (Tao.taoOffsetList as : ℝ)) =
        (q : ℝ) * Real.log 3 -
          (Tao.taoTupleWeight as : ℝ) * Real.log 2 +
          Real.log (N.1 : ℝ) := by
    rw [hdenEq,
      Real.log_mul
        (div_ne_zero (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ (by norm_num))) hNpos.ne',
      Real.log_div (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)),
      Real.log_pow, Real.log_pow]
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  unfold ndA5ExactAffinePosition ndA5NominalAffinePosition
    ndA5AffinePositionCorrection ndA5PhysicalPhase logTwoThree
  rw [hlogExact, hlogPhase, hlogCorrection, hlogDenominator]
  field_simp [hlogTwo]
  ring

/-- Equivalent plus-log form of the exact position identity.  This exposes
the sign directly at the public interface used by strip consumers. -/
theorem ndA5_exactAffinePosition_eq_nominal_add_log_ratio
    {z : ℝ} {q M : ℕ} {as : List ℕ+} {N : Tao.TaoOddNat}
    (hz : 0 < z) (hlen : as.length = q)
    (hAff : Tao.taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    ndA5ExactAffinePosition z N.1 =
      ndA5NominalAffinePosition z M q (Tao.taoTupleWeight as) +
        Real.log (1 - (Tao.taoOffsetList as : ℝ) / (M : ℝ)) := by
  rw [ndA5_exactAffinePosition_eq_nominal_sub_correction hz hlen hAff]
  unfold ndA5AffinePositionCorrection
  ring

/-- The correction vanishes on the zero-length tuple route. -/
@[simp]
theorem ndA5AffinePositionCorrection_eq_zero_of_length_eq_zero
    (as : List ℕ+) (M : ℝ) (hzero : as.length = 0) :
    ndA5AffinePositionCorrection as M = 0 := by
  rw [ndA5AffinePositionCorrection,
    ndA5_taoOffsetList_eq_zero_of_length_eq_zero as hzero]
  norm_num

/-- A tuple whose declared length is zero has no affine correction. -/
theorem ndA5AffinePositionCorrection_eq_zero_of_length_eq
    {q : ℕ} (as : List ℕ+) (M : ℝ)
    (hlen : as.length = q) (hq : q = 0) :
    ndA5AffinePositionCorrection as M = 0 := by
  apply ndA5AffinePositionCorrection_eq_zero_of_length_eq_zero
  omega

/-- Every exact affine source has a nonnegative position correction. -/
theorem ndA5AffinePositionCorrection_nonneg
    {q M : ℕ} {as : List ℕ+} {N : Tao.TaoOddNat}
    (hlen : as.length = q)
    (hAff : Tao.taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    0 ≤ ndA5AffinePositionCorrection as M := by
  have hdenPos :
      0 < (M : ℝ) - (Tao.taoOffsetList as : ℝ) :=
    Tao.taoAffList_denominator_pos hlen hAff
  have hoffset0 : 0 ≤ (Tao.taoOffsetList as : ℝ) :=
    Rat.cast_nonneg.mpr (Tao.taoOffsetList_nonneg as)
  have hMpos : (0 : ℝ) < M := by linarith
  have hratio0 :
      0 ≤ (Tao.taoOffsetList as : ℝ) / (M : ℝ) :=
    div_nonneg hoffset0 hMpos.le
  have hratioLt :
      (Tao.taoOffsetList as : ℝ) / (M : ℝ) < 1 :=
    (div_lt_one hMpos).2 (by linarith)
  unfold ndA5AffinePositionCorrection
  have hlog := Real.log_nonpos (by linarith :
      0 ≤ 1 - (Tao.taoOffsetList as : ℝ) / (M : ℝ)) (by linarith)
  linarith

/-- A positive-length exact affine source has a strictly positive correction. -/
theorem ndA5AffinePositionCorrection_pos
    {q M : ℕ} {as : List ℕ+} {N : Tao.TaoOddNat}
    (hq : 0 < q) (hlen : as.length = q)
    (hAff : Tao.taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    0 < ndA5AffinePositionCorrection as M := by
  have hdenPos :
      0 < (M : ℝ) - (Tao.taoOffsetList as : ℝ) :=
    Tao.taoAffList_denominator_pos hlen hAff
  have hoffsetQ : 0 < Tao.taoOffsetList as :=
    ndA5_taoOffsetList_pos_of_length_pos as (by omega)
  have hoffset : 0 < (Tao.taoOffsetList as : ℝ) :=
    Rat.cast_pos.mpr hoffsetQ
  have hMpos : (0 : ℝ) < M := by linarith
  have hratioPos :
      0 < (Tao.taoOffsetList as : ℝ) / (M : ℝ) :=
    div_pos hoffset hMpos
  have hratioLt :
      (Tao.taoOffsetList as : ℝ) / (M : ℝ) < 1 :=
    (div_lt_one hMpos).2 (by linarith)
  unfold ndA5AffinePositionCorrection
  exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

/-- The source-facing scalar packet, rewritten in the named position unit.
The positive lower bound uses the checked local `t2.nu_pos`, so the integral
phase endpoint is decided on the strict side required by frozen v10. -/
theorem ndA5AffinePositionCorrection_ePrime_pos_le
    {B n M : ℕ} {C : ℝ} {E : Set ℕ} {as : List ℕ+}
    (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hM : M ∈ Tao.taoSection5EPrime B E)
    (ht2 : NDA5T2ScaleFacts B n C)
    (hlen : as.length = n - Tao.taoSection5M0 B) :
    0 < ndA5AffinePositionCorrection as M ∧
      ndA5AffinePositionCorrection as M ≤
        (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  let r : ℝ := (Tao.taoOffsetList as : ℝ) / (M : ℝ)
  have hpacket := ndA5_exactAffineCorrection_ePrime_packet
    facts hlogB hM ht2 hlen
  have hasLengthPos : 0 < as.length := by
    rw [hlen]
    exact ht2.nu_pos
  have hoffsetQ : 0 < Tao.taoOffsetList as :=
    ndA5_taoOffsetList_pos_of_length_pos as hasLengthPos
  have hoffset : 0 < (Tao.taoOffsetList as : ℝ) :=
    Rat.cast_pos.mpr hoffsetQ
  have hMposNat : 0 < M :=
    Odd.pos (Tao.mem_taoSection5EPrime_iff.mp hM).2.2.1
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposNat
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos hoffset hMpos
  have hrlt : r < 1 := by
    have := hpacket.2.2.1
    simpa only [r] using (sub_pos.mp this)
  unfold ndA5AffinePositionCorrection
  constructor
  · exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
  · simpa only [r] using hpacket.2.2.2.2

/-- With strict membership on both sides, a nominal-only point lies in the
closed-at-correction lower mismatch strip. -/
theorem ndA5_strict_nominal_not_strict_exact_mem_lowerStrip
    {beta uExact uNominal delta : ℝ}
    (heq : uExact = uNominal - delta) (hdelta : 0 ≤ delta)
    (hnominal : ndA5StrictPosition beta uNominal)
    (hexact : ¬ ndA5StrictPosition beta uExact) :
    uNominal ∈ Set.Ioc (0 : ℝ) delta := by
  rcases hnominal with ⟨hnominal0, hnominalBeta⟩
  constructor
  · exact hnominal0
  · by_contra hnot
    have hdeltaLt : delta < uNominal := lt_of_not_ge hnot
    apply hexact
    constructor <;> unfold ndA5StrictPosition at * <;> linarith

/-- With strict membership on both sides, an exact-only point lies in the
half-open upper mismatch strip. -/
theorem ndA5_strict_exact_not_strict_nominal_mem_upperStrip
    {beta uExact uNominal delta : ℝ}
    (heq : uExact = uNominal - delta) (hdelta : 0 ≤ delta)
    (hexact : ndA5StrictPosition beta uExact)
    (hnominal : ¬ ndA5StrictPosition beta uNominal) :
    uNominal ∈ Set.Ico beta (beta + delta) := by
  rcases hexact with ⟨hexact0, hexactBeta⟩
  constructor
  · by_contra hnot
    apply hnominal
    constructor <;> unfold ndA5StrictPosition at * <;> linarith
  · linarith

/-- A nominal strict point excluded from the actual half-open band lies in
the genuinely open lower strip.  Equality `uNominal = delta` gives
`uExact = 0`, which is physically included and is therefore absent here. -/
theorem ndA5_strict_nominal_not_halfOpen_exact_mem_lowerStrip
    {beta uExact uNominal delta : ℝ}
    (heq : uExact = uNominal - delta) (hdelta : 0 ≤ delta)
    (hnominal : ndA5StrictPosition beta uNominal)
    (hexact : ¬ ndA5HalfOpenPosition beta uExact) :
    uNominal ∈ Set.Ioo (0 : ℝ) delta := by
  rcases hnominal with ⟨hnominal0, hnominalBeta⟩
  constructor
  · exact hnominal0
  · by_contra hnot
    have hdeltaLe : delta ≤ uNominal := le_of_not_gt hnot
    apply hexact
    constructor <;> unfold ndA5HalfOpenPosition at * <;> linarith

/-- Exact half-open membership but failed nominal strict membership is either
the sole zero-correction lower endpoint or lies in the upper mismatch strip. -/
theorem ndA5_halfOpen_exact_not_strict_nominal_boundary_or_upperStrip
    {beta uExact uNominal delta : ℝ}
    (heq : uExact = uNominal - delta) (hdelta : 0 ≤ delta)
    (hexact : ndA5HalfOpenPosition beta uExact)
    (hnominal : ¬ ndA5StrictPosition beta uNominal) :
    (uNominal = 0 ∧ uExact = 0 ∧ delta = 0) ∨
      uNominal ∈ Set.Ico beta (beta + delta) := by
  rcases hexact with ⟨hexact0, hexactBeta⟩
  have hnominal0 : 0 ≤ uNominal := by linarith
  by_cases hzero : uNominal = 0
  · left
    have hdeltaZero : delta = 0 := by linarith
    exact ⟨hzero, by linarith, hdeltaZero⟩
  · right
    have hnominalPos : 0 < uNominal := lt_of_le_of_ne hnominal0 (Ne.symm hzero)
    constructor
    · by_contra hnot
      apply hnominal
      constructor <;> unfold ndA5StrictPosition at * <;> linarith
    · linarith

/-- With a genuinely positive affine correction, the zero endpoint branch is
impossible, so every physical-only point lies in the upper mismatch strip. -/
theorem ndA5_halfOpen_exact_not_strict_nominal_mem_upperStrip_of_delta_pos
    {beta uExact uNominal delta : ℝ}
    (heq : uExact = uNominal - delta) (hdelta : 0 < delta)
    (hexact : ndA5HalfOpenPosition beta uExact)
    (hnominal : ¬ ndA5StrictPosition beta uNominal) :
    uNominal ∈ Set.Ico beta (beta + delta) := by
  rcases ndA5_halfOpen_exact_not_strict_nominal_boundary_or_upperStrip
      heq hdelta.le hexact hnominal with hboundary | hupper
  · exfalso
    linarith [hboundary.2.2]
  · exact hupper

/-- Endpoint-shaped once-only strip packet for an exact affine source in an
actual A5 band.  This is the direct `ℓ7` interface: actual membership is read
from the half-open finite carrier, nominal membership is strict, and every
mismatch is confined to a strip of width at most `B^-0.9`. -/
theorem ndA5_affineBandMismatch_mem_strips_ePrime
    {B n M j : ℕ} {C : ℝ} {E : Set ℕ}
    {branch : Tao.TaoSection5SourceBranch}
    {as : List ℕ+} {N : Tao.TaoOddNat}
    (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hM : M ∈ Tao.taoSection5EPrime B E)
    (ht2 : NDA5T2ScaleFacts B n C)
    (hlen : as.length = n - Tao.taoSection5M0 B)
    (hAff : Tao.taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    let beta := ndA5BandBeta B branch
    let z := ndA5BandLower B branch j
    let uNominal := ndA5NominalAffinePosition z M
      (n - Tao.taoSection5M0 B) (Tao.taoTupleWeight as)
    let delta := ndA5AffinePositionCorrection as M
    0 < delta ∧
      delta ≤ (B : ℝ) ^ (-(9 / 10 : ℝ)) ∧
      (ndA5StrictPosition beta uNominal ∧
          N.1 ∉ ndA5OddBand B branch j →
        uNominal ∈ Set.Ioo (0 : ℝ) delta) ∧
      (N.1 ∈ ndA5OddBand B branch j ∧
          ¬ ndA5StrictPosition beta uNominal →
        uNominal ∈ Set.Ico beta (beta + delta)) := by
  dsimp only
  have hB := facts.schedule.one_le_B
  have hz : 0 < ndA5BandLower B branch j := by
    have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
    have hYpos : 0 < Tao.taoSection5SourceY B branch := by
      rw [Tao.taoSection5SourceY_eq_branch_rpow]
      exact Real.rpow_pos_of_pos hBpos _
    unfold ndA5BandLower
    exact mul_pos hYpos (Real.exp_pos _)
  have heq := ndA5_exactAffinePosition_eq_nominal_sub_correction
    hz hlen hAff
  have hdelta := ndA5AffinePositionCorrection_ePrime_pos_le
    facts hlogB hM ht2 hlen
  have hcarrier := mem_ndA5OddBand_iff_halfOpen_exactPosition
    (branch := branch) (j := j) hB (Nat.odd_iff.mp N.2)
  refine ⟨hdelta.1, hdelta.2, ?_, ?_⟩
  · rintro ⟨hnominal, hnotMem⟩
    apply ndA5_strict_nominal_not_halfOpen_exact_mem_lowerStrip
      heq hdelta.1.le hnominal
    intro hhalfOpen
    exact hnotMem (hcarrier.2 hhalfOpen)
  · rintro ⟨hmem, hnotNominal⟩
    apply ndA5_halfOpen_exact_not_strict_nominal_mem_upperStrip_of_delta_pos
      heq hdelta.1 (hcarrier.1 hmem) hnotNominal

end

end ND
end Erdos1135
