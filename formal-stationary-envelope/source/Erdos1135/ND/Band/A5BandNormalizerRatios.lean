import Erdos1135.ND.Band.A5BandNormalizer

/-!
# A5 band normalizer ratios

This leaf converts the checked additive harmonic-mass and flat-cardinality
errors into the ratio estimates consumed after the physical-window A6 step.
Every division is discharged from the existing positive band floors.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The reciprocal of the exact odd-band logarithmic mass is at most four. -/
theorem one_div_logFinsetMass_ndA5OddBand_le_four
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    1 / Tao.logFinsetMass (ndA5OddBand B branch j) ≤ 4 := by
  have hmass := one_fourth_le_logFinsetMass_ndA5OddBand hB j hcount
  have hmassPos := logFinsetMass_ndA5OddBand_pos hB j hcount
  apply (div_le_iff₀ hmassPos).2
  nlinarith

/-- The harmonic band normalizer is within `12 / z` of two. -/
theorem abs_ndA5BandBeta_div_logFinsetMass_sub_two_le
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    |ndA5BandBeta B branch /
          Tao.logFinsetMass (ndA5OddBand B branch j) - 2| ≤
      12 / ndA5BandLower B branch j := by
  let beta := ndA5BandBeta B branch
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  let z := ndA5BandLower B branch j
  have hzSix : (6 : ℝ) ≤ z := by
    simpa only [z] using six_le_ndA5BandLower hB j hcount
  have hzPos : 0 < z := by linarith
  have hHfloor : (1 / 4 : ℝ) ≤ H := by
    simpa only [H] using one_fourth_le_logFinsetMass_ndA5OddBand hB j hcount
  have hHpos : 0 < H := by linarith
  have herr : |H - beta / 2| ≤ 3 / (2 * z) := by
    simpa only [H, beta, z] using
      abs_logFinsetMass_ndA5OddBand_sub_half_beta_le hB j hcount
  have herr' : |H - beta / 2| ≤ (3 / 2 : ℝ) * (1 / z) := by
    calc
      |H - beta / 2| ≤ 3 / (2 * z) := herr
      _ = (3 / 2 : ℝ) * (1 / z) := by field_simp [hzPos.ne']
  have hrewrite : beta / H - 2 = (-2 * (H - beta / 2)) / H := by
    field_simp [hHpos.ne']
    ring
  rw [show ndA5BandBeta B branch = beta by rfl,
    show Tao.logFinsetMass (ndA5OddBand B branch j) = H by rfl,
    show ndA5BandLower B branch j = z by rfl, hrewrite,
    abs_div, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0),
    abs_of_pos hHpos]
  norm_num only [neg_neg]
  apply (div_le_iff₀ hHpos).2
  rw [show 12 / z = 12 * (1 / z) by ring]
  have hinv : 0 ≤ 1 / z := one_div_nonneg.mpr hzPos.le
  nlinarith

private theorem ndA5BandLower_div_three_lt_card
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5BandLower B branch j / 3 <
      ((ndA5OddBand B branch j).card : ℝ) := by
  let beta := ndA5BandBeta B branch
  let z := ndA5BandLower B branch j
  let card := ((ndA5OddBand B branch j).card : ℝ)
  have hzSix : (6 : ℝ) ≤ z := by
    simpa only [z] using six_le_ndA5BandLower hB j hcount
  have hbeta : (1 : ℝ) ≤ beta := by
    simpa only [beta] using (ndA5BandBeta_mem_Ico hcount).1
  have hexp : (1 : ℝ) ≤ Real.exp beta - 1 := by
    have := Real.add_one_le_exp beta
    linarith
  have herr : |card - z * (Real.exp beta - 1) / 2| < 1 := by
    simpa only [card, z, beta] using
      abs_card_ndA5OddBand_sub_flat_center_lt_one hB j hcount
  have hlower := (abs_lt.mp herr).1
  change z / 3 < card
  nlinarith [mul_le_mul_of_nonneg_left hexp (by linarith : 0 ≤ z)]

/-- The flat band scale divided by its exact odd cardinality is below three. -/
theorem ndA5BandLower_div_card_lt_three
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5BandLower B branch j /
        ((ndA5OddBand B branch j).card : ℝ) < 3 := by
  have hcardNat := ndA5OddBand_card_pos hB j hcount
  have hcard : (0 : ℝ) < ((ndA5OddBand B branch j).card : ℝ) := by
    exact_mod_cast hcardNat
  apply (div_lt_iff₀ hcard).2
  nlinarith [ndA5BandLower_div_three_lt_card hB j hcount]

/-- The flat band normalizer is within `6 / z` of two. -/
theorem abs_ndA5BandLower_mul_exp_sub_one_div_card_sub_two_lt
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    |ndA5BandLower B branch j *
          (Real.exp (ndA5BandBeta B branch) - 1) /
          ((ndA5OddBand B branch j).card : ℝ) - 2| <
      6 / ndA5BandLower B branch j := by
  let beta := ndA5BandBeta B branch
  let z := ndA5BandLower B branch j
  let card := ((ndA5OddBand B branch j).card : ℝ)
  have hzSix : (6 : ℝ) ≤ z := by
    simpa only [z] using six_le_ndA5BandLower hB j hcount
  have hzPos : 0 < z := by linarith
  have hcardNat := ndA5OddBand_card_pos hB j hcount
  have hcardPos : 0 < card := by
    dsimp only [card]
    exact_mod_cast hcardNat
  have herr : |card - z * (Real.exp beta - 1) / 2| < 1 := by
    simpa only [card, z, beta] using
      abs_card_ndA5OddBand_sub_flat_center_lt_one hB j hcount
  have hzCard : z / 3 < card := by
    simpa only [z, card] using
      ndA5BandLower_div_three_lt_card hB j hcount
  have hrewrite :
      z * (Real.exp beta - 1) / card - 2 =
        (-2 * (card - z * (Real.exp beta - 1) / 2)) / card := by
    field_simp [hcardPos.ne']
    ring
  rw [show ndA5BandBeta B branch = beta by rfl,
    show ndA5BandLower B branch j = z by rfl,
    show ((ndA5OddBand B branch j).card : ℝ) = card by rfl,
    hrewrite, abs_div, abs_mul,
    abs_of_neg (by norm_num : (-2 : ℝ) < 0), abs_of_pos hcardPos]
  norm_num only [neg_neg]
  have hnum : 2 * |card - z * (Real.exp beta - 1) / 2| < 2 := by
    nlinarith
  have hfirst :
      2 * |card - z * (Real.exp beta - 1) / 2| / card < 2 / card :=
    div_lt_div_of_pos_right hnum hcardPos
  have hsecond : 2 / card < 6 / z := by
    apply (div_lt_div_iff₀ hcardPos hzPos).2
    nlinarith
  exact hfirst.trans hsecond

end
end ND
end Erdos1135
