import NaturalVectorMeans

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.NaturalPrefix
open Erdos1135

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Removing a small initial part of an odd prefix changes its normalized
vector average by at most twice the removed mass, plus the parity endpoint. -/
theorem odd_prefix_mean_sub_finite_mean_bound {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) (s : Finset ℕ) (hs : s ⊆ oddNaturalPrefix X)
    {R : ℝ} (hR : (((oddNaturalPrefix X) \ s).card : ℝ) ≤ R) :
    ‖(X : ℝ)⁻¹ • oddNaturalPrefixSum F X - (1 / 2 : ℝ) • finiteVectorMean s F‖ ≤
      (2 * R + 1) / (X : ℝ) := by
  classical
  let P := oddNaturalPrefix X
  let E := P \ s
  let m := finiteVectorMean s F
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hm : ‖m‖ ≤ 1 := finiteVectorMean_norm_le_one hF s
  have he : (E.card : ℝ) + (s.card : ℝ) = (P.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hs
  have hsum : (∑ q ∈ E, F q) + (∑ q ∈ s, F q) = ∑ q ∈ P, F q :=
    Finset.sum_sdiff hs
  have hid : (∑ q ∈ P, F q) - (P.card : ℝ) • m =
      (∑ q ∈ E, F q) - (E.card : ℝ) • m := by
    rw [← he, add_smul, ← hsum]
    have hsmean := finiteVectorMean_card_smul s F
    change (s.card : ℝ) • m = ∑ q ∈ s, F q at hsmean
    rw [hsmean]
    abel
  have hnormE : ‖∑ q ∈ E, F q‖ ≤ (E.card : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (fun q (_ : q ∈ E) => hF q)
  have htwice : ‖(∑ q ∈ P, F q) - (P.card : ℝ) • m‖ ≤ 2 * (E.card : ℝ) := by
    rw [hid]
    have hb := norm_sub_le (∑ q ∈ E, F q) ((E.card : ℝ) • m)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hb
    nlinarith [Nat.cast_nonneg (α := ℝ) E.card]
  have hcard := oddNaturalPrefix_card_error X
  change |(P.card : ℝ) - (X : ℝ) / 2| ≤ 1 at hcard
  have hfrac : (X : ℝ)⁻¹ * ((X : ℝ) / 2) = 1 / 2 := by field_simp
  have hsplit : (X : ℝ)⁻¹ • (∑ q ∈ P, F q) - (1 / 2 : ℝ) • m =
      (X : ℝ)⁻¹ • ((∑ q ∈ P, F q) - (P.card : ℝ) • m) +
        (X : ℝ)⁻¹ • (((P.card : ℝ) - (X : ℝ) / 2) • m) := by
    simp only [smul_sub, sub_smul, smul_smul]
    rw [hfrac]
    abel
  have hfirst : ‖(X : ℝ)⁻¹ • ((∑ q ∈ P, F q) - (P.card : ℝ) • m)‖ ≤
      (X : ℝ)⁻¹ * (2 * (E.card : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hXr)]
    exact mul_le_mul_of_nonneg_left htwice (inv_nonneg.mpr hXr.le)
  have hsecond : ‖(X : ℝ)⁻¹ • (((P.card : ℝ) - (X : ℝ) / 2) • m)‖ ≤ (X : ℝ)⁻¹ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hXr), Real.norm_eq_abs]
    have hb : |(P.card : ℝ) - (X : ℝ) / 2| * ‖m‖ ≤ 1 := by
      nlinarith [norm_nonneg m, abs_nonneg ((P.card : ℝ) - (X : ℝ) / 2)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hXr.le)
  rw [oddNaturalPrefixSum_eq_sum]
  change ‖(X : ℝ)⁻¹ • (∑ q ∈ P, F q) - (1 / 2 : ℝ) • m‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ (X : ℝ)⁻¹ * (2 * (E.card : ℝ)) + (X : ℝ)⁻¹ := add_le_add hfirst hsecond
    _ = (2 * (E.card : ℝ) + 1) / (X : ℝ) := by ring
    _ ≤ (2 * R + 1) / (X : ℝ) := div_le_div_of_nonneg_right (by dsimp [E, P]; linarith) hXr.le

/-- The native power block ending at X omits only numbers below its lower endpoint. -/
theorem natural_block_missing_prefix_bound (X : ℕ) :
    let y := (X : ℝ) ^ (1 / ND.alpha)
    ND.oddBlock y ⊆ oddNaturalPrefix X ∧
      (((oddNaturalPrefix X) \ ND.oddBlock y).card : ℝ) ≤ y + 1 := by
  dsimp only
  let y := (X : ℝ) ^ (1 / ND.alpha)
  have ha : 0 < ND.alpha := Tao.taoAlpha_pos
  have hy : 0 ≤ y := Real.rpow_nonneg (Nat.cast_nonneg X) _
  have hend : y ^ ND.alpha = (X : ℝ) := by
    dsimp only [y]
    rw [← Real.rpow_mul (Nat.cast_nonneg X), one_div_mul_cancel ha.ne', Real.rpow_one]
  have hset : ND.oddBlock y = Tao.oddLogWindow (Nat.ceil y) X := by
    unfold ND.oddBlock Tao.taoNyOddWindow Tao.taoNyLo Tao.taoNyHi
    rw [hend, Nat.floor_natCast]
  have hsub : ND.oddBlock y ⊆ oddNaturalPrefix X := by
    intro q hq
    rw [hset, Tao.oddLogWindow_mem] at hq
    exact oddNaturalPrefix_mem.mpr ⟨hq.2.1, hq.2.2⟩
  refine ⟨hsub, ?_⟩
  have hsmall : oddNaturalPrefix X \ ND.oddBlock y ⊆ Finset.range (Nat.ceil y) := by
    intro q hq
    obtain ⟨hp, hb⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqx, hqo⟩ := oddNaturalPrefix_mem.mp hp
    rw [hset, Tao.oddLogWindow_mem] at hb
    rw [Finset.mem_range]
    omega
  have hc : (((oddNaturalPrefix X) \ ND.oddBlock y).card : ℝ) ≤ Nat.ceil y := by
    exact_mod_cast (Finset.card_le_card hsmall).trans_eq (Finset.card_range _)
  exact hc.trans (Nat.ceil_lt_add_one hy).le

theorem odd_prefix_mean_sub_natural_block_bound {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) :
    ‖(X : ℝ)⁻¹ • oddNaturalPrefixSum F X -
      (1 / 2 : ℝ) • naturalOddVectorBlockMean F ((X : ℝ) ^ (1 / ND.alpha))‖ ≤
      (2 * (X : ℝ) ^ (1 / ND.alpha) + 3) / (X : ℝ) := by
  obtain ⟨hs, hr⟩ := natural_block_missing_prefix_bound X
  have h := odd_prefix_mean_sub_finite_mean_bound hF hX _ hs hr
  convert h using 1
  ring

#print axioms odd_prefix_mean_sub_natural_block_bound

end CollatzCanonical.NaturalPrefix
