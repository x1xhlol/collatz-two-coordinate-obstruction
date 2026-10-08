import Erdos1135.ND.Band.A5BandNormalizerRatios
import Erdos1135.ND.Discrepancy.A5TwoProfilePhysicalA6

/-!
# A5 normalized two-profile A6

This leaf divides the reciprocal physical profile by its exact logarithmic
band mass and scales the flat profile by the exact lower-endpoint/cardinality
factor.  Both normalized laws are compared with the same deterministic center
`2 / log(4/3)`.  The two error rows remain separate for the later common-kernel
interior-endpoint sum.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Reciprocal physical value after exact harmonic band normalization. -/
def ndA5HarmonicTwoProfileNormalizedPhysicalValue
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (M : ℝ) : ℝ :=
  ndA5ReciprocalTwoProfilePhysicalSum B branch C j M /
    Tao.logFinsetMass (ndA5OddBand B branch j)

/-- Flat physical value after exact counting normalization. -/
def ndA5FlatTwoProfileNormalizedPhysicalValue
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (M : ℝ) : ℝ :=
  ndA5BandLower B branch j /
      ((ndA5OddBand B branch j).card : ℝ) *
    ndA5FlatTwoProfilePhysicalSum B branch C j M

/-- Convenient reciprocal normalized error from one raw A6 error. -/
def ndA5HarmonicTwoProfileNormalizedA6Error
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (j : ℕ) (E : ℝ) : ℝ :=
  4 * E +
    12 / (ndA5BandLower B branch j * ndA5LogFourThirds)

/-- Convenient flat normalized error from one raw A6 error. -/
def ndA5FlatTwoProfileNormalizedA6Error
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (j : ℕ) (E : ℝ) : ℝ :=
  3 * E +
    6 / (ndA5BandLower B branch j * ndA5LogFourThirds)

/-- A reciprocal raw physical A6 estimate becomes a normalized estimate at
the common center. -/
theorem
    abs_ndA5HarmonicTwoProfileNormalizedPhysicalValue_sub_common_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C M E : ℝ} (hB : 1 ≤ B) (hj : j < ndA5BandCount B branch)
    (hraw :
      |ndA5ReciprocalTwoProfilePhysicalSum B branch C j M -
          ndA5BandBeta B branch / ndA5LogFourThirds| ≤ E) :
    |ndA5HarmonicTwoProfileNormalizedPhysicalValue B branch C j M -
        2 / ndA5LogFourThirds| ≤
      ndA5HarmonicTwoProfileNormalizedA6Error B branch j E := by
  let S := ndA5ReciprocalTwoProfilePhysicalSum B branch C j M
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  let beta := ndA5BandBeta B branch
  let z := ndA5BandLower B branch j
  let L := ndA5LogFourThirds
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have hzPos : 0 < z := by
    have hzSix : (6 : ℝ) ≤ z := by
      simpa only [z] using six_le_ndA5BandLower hB j hcount
    linarith
  have hHpos : 0 < H := by
    simpa only [H] using logFinsetMass_ndA5OddBand_pos hB j hcount
  have hLpos : 0 < L := by
    simpa only [L] using ndA5LogFourThirds_pos
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hraw
  have hInv : 1 / H ≤ 4 := by
    simpa only [H] using
      one_div_logFinsetMass_ndA5OddBand_le_four hB j hcount
  have hnorm : |beta / H - 2| ≤ 12 / z := by
    simpa only [beta, H, z] using
      abs_ndA5BandBeta_div_logFinsetMass_sub_two_le hB j hcount
  have hdecomp :
      S / H - 2 / L =
        (S - beta / L) / H + (beta / H - 2) / L := by
    field_simp [hHpos.ne', hLpos.ne']
    ring
  have hfirst : |S - beta / L| / H ≤ 4 * E := by
    calc
      |S - beta / L| / H ≤ E / H :=
        div_le_div_of_nonneg_right
          (by simpa only [S, beta, L] using hraw) hHpos.le
      _ = E * (1 / H) := by ring
      _ ≤ E * 4 := mul_le_mul_of_nonneg_left hInv hE0
      _ = 4 * E := by ring
  have hsecond : |beta / H - 2| / L ≤ 12 / (z * L) := by
    calc
      |beta / H - 2| / L ≤ (12 / z) / L :=
        div_le_div_of_nonneg_right hnorm hLpos.le
      _ = 12 / (z * L) := by field_simp [hzPos.ne', hLpos.ne']
  rw [ndA5HarmonicTwoProfileNormalizedPhysicalValue,
    show ndA5ReciprocalTwoProfilePhysicalSum B branch C j M = S by rfl,
    show Tao.logFinsetMass (ndA5OddBand B branch j) = H by rfl,
    show ndA5LogFourThirds = L by rfl, hdecomp]
  calc
    |(S - beta / L) / H + (beta / H - 2) / L| ≤
        |(S - beta / L) / H| + |(beta / H - 2) / L| := abs_add_le _ _
    _ = |S - beta / L| / H + |beta / H - 2| / L := by
      rw [abs_div, abs_div, abs_of_pos hHpos, abs_of_pos hLpos]
    _ ≤ 4 * E + 12 / (z * L) := add_le_add hfirst hsecond
    _ = ndA5HarmonicTwoProfileNormalizedA6Error B branch j E := by
      rfl

/-- A flat raw physical A6 estimate becomes a normalized estimate at the same
common center. -/
theorem
    abs_ndA5FlatTwoProfileNormalizedPhysicalValue_sub_common_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C M E : ℝ} (hB : 1 ≤ B) (hj : j < ndA5BandCount B branch)
    (hraw :
      |ndA5FlatTwoProfilePhysicalSum B branch C j M -
          (Real.exp (ndA5BandBeta B branch) - 1) /
            ndA5LogFourThirds| ≤ E) :
    |ndA5FlatTwoProfileNormalizedPhysicalValue B branch C j M -
        2 / ndA5LogFourThirds| ≤
      ndA5FlatTwoProfileNormalizedA6Error B branch j E := by
  let S := ndA5FlatTwoProfilePhysicalSum B branch C j M
  let card := ((ndA5OddBand B branch j).card : ℝ)
  let beta := ndA5BandBeta B branch
  let z := ndA5BandLower B branch j
  let L := ndA5LogFourThirds
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have hcardNat := ndA5OddBand_card_pos hB j hcount
  have hcardPos : 0 < card := by
    dsimp only [card]
    exact_mod_cast hcardNat
  have hzPos : 0 < z := by
    have hzSix : (6 : ℝ) ≤ z := by
      simpa only [z] using six_le_ndA5BandLower hB j hcount
    linarith
  have hLpos : 0 < L := by
    simpa only [L] using ndA5LogFourThirds_pos
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hraw
  have hscale0 : 0 ≤ z / card := div_nonneg hzPos.le hcardPos.le
  have hscale : z / card < 3 := by
    simpa only [z, card] using ndA5BandLower_div_card_lt_three hB j hcount
  have hnorm :
      |z * (Real.exp beta - 1) / card - 2| < 6 / z := by
    simpa only [z, beta, card] using
      abs_ndA5BandLower_mul_exp_sub_one_div_card_sub_two_lt hB j hcount
  have hdecomp :
      z / card * S - 2 / L =
        z / card * (S - (Real.exp beta - 1) / L) +
          (z * (Real.exp beta - 1) / card - 2) / L := by
    field_simp [hcardPos.ne', hLpos.ne']
    ring
  have hfirst :
      z / card * |S - (Real.exp beta - 1) / L| ≤ 3 * E := by
    calc
      z / card * |S - (Real.exp beta - 1) / L| ≤ z / card * E :=
        mul_le_mul_of_nonneg_left
          (by simpa only [S, beta, L] using hraw) hscale0
      _ ≤ 3 * E := mul_le_mul_of_nonneg_right hscale.le hE0
  have hsecond :
      |z * (Real.exp beta - 1) / card - 2| / L ≤
        6 / (z * L) := by
    calc
      |z * (Real.exp beta - 1) / card - 2| / L ≤ (6 / z) / L :=
        div_le_div_of_nonneg_right hnorm.le hLpos.le
      _ = 6 / (z * L) := by field_simp [hzPos.ne', hLpos.ne']
  rw [ndA5FlatTwoProfileNormalizedPhysicalValue,
    show ndA5FlatTwoProfilePhysicalSum B branch C j M = S by rfl,
    show ((ndA5OddBand B branch j).card : ℝ) = card by rfl,
    show ndA5BandLower B branch j = z by rfl,
    show ndA5LogFourThirds = L by rfl, hdecomp]
  calc
    |z / card * (S - (Real.exp beta - 1) / L) +
        (z * (Real.exp beta - 1) / card - 2) / L| ≤
      |z / card * (S - (Real.exp beta - 1) / L)| +
        |(z * (Real.exp beta - 1) / card - 2) / L| := abs_add_le _ _
    _ = z / card * |S - (Real.exp beta - 1) / L| +
        |z * (Real.exp beta - 1) / card - 2| / L := by
      rw [abs_mul, abs_of_nonneg hscale0, abs_div, abs_of_pos hLpos]
    _ ≤ 3 * E + 6 / (z * L) := add_le_add hfirst hsecond
    _ = ndA5FlatTwoProfileNormalizedA6Error B branch j E := by
      rfl

/-- Named eventual normalized A6 packet at one base. -/
def NDA5TwoProfileNormalizedA6At
    (B : ℕ) (C c kappa : ℝ) : Prop :=
  ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ),
    j < ndA5BandCount B branch →
      ∀ M : ℝ, 0 < M →
        |ndA5InteriorShift B M| ≤
            (4 / 25 : ℝ) * ndA5TubeWidth B C →
          let EA6 := 3650000 * (C + C ^ 3) * ndA6PhysicalRate B
          (|ndA5HarmonicTwoProfileNormalizedPhysicalValue
                B branch C j M - 2 / ndA5LogFourThirds| ≤
              ndA5HarmonicTwoProfileNormalizedA6Error B branch j
                (ndA5ReciprocalTwoProfileA6Error
                  B branch C j M EA6 c kappa)) ∧
            (|ndA5FlatTwoProfileNormalizedPhysicalValue
                B branch C j M - 2 / ndA5LogFourThirds| ≤
              ndA5FlatTwoProfileNormalizedA6Error B branch j
                (ndA5FlatTwoProfileA6Error
                  B branch C j M EA6 c kappa))

/-- Fixed-`C` normalized A6 packet for every later original interior
endpoint, with the common center visible in both components. -/
theorem eventually_ndA5TwoProfileNormalizedA6
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa : ℝ} (hPhase : PhaseGap c kappa) :
    ∀ᶠ B : ℕ in Filter.atTop,
      NDA5TwoProfileNormalizedA6At B C c kappa := by
  filter_upwards
    [Filter.eventually_ge_atTop (1 : ℕ),
      eventually_ndA5TwoProfilePhysicalA6 C hC hPhase]
      with B hB hraw
  rw [NDA5TwoProfileNormalizedA6At]
  intro branch j hj M hM hshift
  dsimp only
  have hpair := hraw branch j hj M hM hshift
  exact
    ⟨abs_ndA5HarmonicTwoProfileNormalizedPhysicalValue_sub_common_le
        hB hj hpair.1,
      abs_ndA5FlatTwoProfileNormalizedPhysicalValue_sub_common_le
        hB hj hpair.2⟩

end
end ND
end Erdos1135
