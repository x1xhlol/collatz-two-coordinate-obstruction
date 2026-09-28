import Erdos1135.ND.Band.A5RawMass
import Erdos1135.Tao.Section5.PassNormalizer

/-!
# A5 Physical-Window Cardinality

This leaf bounds the number of retained physical times in one band.  Only
the nonproportional FM1 and tail rows may later pay this factor.
-/

namespace Erdos1135
namespace ND

noncomputable section

private theorem one_fourth_le_ndA5LogFourThirds_card :
    (1 / 4 : ℝ) ≤ ndA5LogFourThirds := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
  unfold ndA5LogFourThirds
  norm_num at h ⊢
  exact h

private theorem ndA5PaddedBandUpper_sub_lower_eq_card
    {B j : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) :
    ndA5PaddedBandUpper B branch C j -
        ndA5PaddedBandLower B branch C j =
      ndA5BandBeta B branch / ndA5LogFourThirds +
        6 * ndA5TubeWidth B C := by
  unfold ndA5PaddedBandUpper ndA5PaddedBandLower
  rw [ndA5_log_bandUpper_div hB branch,
    ndA5_log_bandLower_div hB branch]
  ring

/-- The retained physical-time carrier has at most seven tube widths.  The
bound is pointwise under the same visible guards that make every padded time
strictly later than `m0`; no eventual quantifier is hidden here. -/
theorem ndA5PhysicalNuWindow_card_le_seven_mul_width
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    ((ndA5PhysicalNuWindow B branch C j).card : ℝ) ≤
      7 * ndA5TubeWidth B C := by
  let L := ndA5PaddedBandLower B branch C j
  let U := ndA5PaddedBandUpper B branch C j
  let J := ndA5PaddedBandWindow B branch C j
  let P := ndA5PhysicalNuWindow B branch C j
  let W := ndA5TubeWidth B C
  have hcardNat : P.card ≤ J.card := by
    dsimp [P, J, ndA5PhysicalNuWindow]
    exact (Finset.card_image_le.trans (Finset.card_filter_le _ _))
  have hcard : (P.card : ℝ) ≤ (J.card : ℝ) := by
    exact_mod_cast hcardNat
  have hW : (142 : ℝ) ≤ W := by
    simpa [W] using ndA5TubeWidth_ge_one_hundred_forty_two hC hlogB
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have hbeta := ndA5BandBeta_mem_Ico hcount
  have hbetaDiv : ndA5BandBeta B branch / ndA5LogFourThirds < 8 := by
    apply (div_lt_iff₀ ndA5LogFourThirds_pos).2
    nlinarith [one_fourth_le_ndA5LogFourThirds_card, hbeta.2]
  have hwidth : U - L =
      ndA5BandBeta B branch / ndA5LogFourThirds + 6 * W := by
    simpa [L, U, W] using
      ndA5PaddedBandUpper_sub_lower_eq_card
        (j := j) hB branch C
  by_cases hne : J.Nonempty
  · have hJ : J = Finset.Icc (Nat.ceil L) (Nat.floor U) := by
      rfl
    have hbounds : Nat.ceil L ≤ Nat.floor U := by
      rw [hJ] at hne
      exact Finset.nonempty_Icc.mp hne
    have hm0Ceil := ndA5M0_lt_ceil_paddedBandLower_of_guards
      hB hlogB hpadding hj
    have hceilPos : 0 < Nat.ceil L := by
      simpa [L] using (Nat.zero_le (Tao.taoSection5M0 B)).trans_lt hm0Ceil
    have hL0 : 0 ≤ L := (Nat.ceil_pos.mp hceilPos).le
    have hfloorPos : 0 < Nat.floor U := hceilPos.trans_le hbounds
    have hU0 : 0 ≤ U :=
      (Nat.pos_of_floor_pos hfloorPos).le
    have hround : |(J.card : ℝ) - (U - L)| ≤ 1 := by
      rw [hJ]
      exact Tao.abs_natCast_card_Icc_ceil_floor_sub_width_le_one
        hL0 hU0 (by simpa [hJ] using hne)
    have hJupper : (J.card : ℝ) ≤ (U - L) + 1 := by
      linarith [abs_le.mp hround]
    rw [hwidth] at hJupper
    nlinarith
  · have hJzero : J.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    have hPzero : P.card = 0 := by omega
    rw [hPzero]
    norm_num
    nlinarith

end

end ND
end Erdos1135
