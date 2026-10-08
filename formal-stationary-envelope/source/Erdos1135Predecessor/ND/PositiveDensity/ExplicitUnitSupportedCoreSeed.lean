/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitOnePeriodSeedToCount

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem explicit_unit_filter_card {q : ℕ} (hq : 1 ≤ q) :
    ((Finset.univ : Finset (ZMod (3 ^ q))).filter IsUnit).card = 2 * 3 ^ (q - 1) := by
  classical
  let emb : (ZMod (3 ^ q))ˣ ↪ ZMod (3 ^ q) :=
    ⟨((↑) : (ZMod (3 ^ q))ˣ → ZMod (3 ^ q)), Units.val_injective⟩
  have hs : (Finset.univ : Finset (ZMod (3 ^ q))).filter IsUnit =
      Finset.univ.map emb := by ext y; simp [emb, IsUnit]
  rw [hs, Finset.card_map, Finset.card_univ, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_three (by omega : 0 < q)]
  norm_num
  ring

theorem explicit_unit_levelOne_iff {q : ℕ} (hq : 1 ≤ q) (y : ZMod (3 ^ q)) :
    IsUnit (y.val : ZMod (3 ^ 1)) ↔ IsUnit y := by
  calc
    _ ↔ y.val.Coprime 3 := by rw [ZMod.isUnit_iff_coprime]; norm_num
    _ ↔ y.val.Coprime (3 ^ q) := (Nat.coprime_pow_right_iff (by omega : 0 < q) _ _).symm
    _ ↔ IsUnit y := by rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]

theorem explicit_exists_unit_ge_of_supported_mean {q : ℕ} (hq : 1 ≤ q)
    (g : ZMod (3 ^ q) → ℝ) (P : ℝ)
    (hzero : ∀ y, ¬ IsUnit y → g y = 0)
    (hmean : ndTernaryUniformMean q g = (2/3:ℝ) * P) :
    ∃ y, IsUnit y ∧ P ≤ g y := by
  classical
  let S := (Finset.univ : Finset (ZMod (3 ^ q))).filter IsUnit
  have hcard : S.card = 2 * 3 ^ (q - 1) := explicit_unit_filter_card hq
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; positivity)
  have hsum : (∑ y ∈ S, g y) = ∑ y, g y := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : IsUnit y <;> simp [hy, hzero y]
  have hpow : (3:ℝ) ^ q = 3 ^ (q-1) * 3 := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  change (1 / ((3 ^ q : ℕ) : ℝ)) * (∑ y, g y) = (2/3:ℝ) * P at hmean
  have hs : (∑ _y ∈ S, P) ≤ ∑ y ∈ S, g y := by
    rw [hsum, Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast at hmean ⊢
    rw [hpow] at hmean
    have hp : (3:ℝ) ^ (q-1) ≠ 0 := by positivity
    field_simp at hmean
    nlinarith only [hmean]
  obtain ⟨y, hy, hg⟩ := Finset.exists_le_of_sum_le hnonempty hs
  exact ⟨y, (Finset.mem_filter.mp hy).2, hg⟩

theorem exists_unit_rootCoreBackwardMark_ge_full_product
    {b k : ℕ} (hk : 1 ≤ k) (cap width : ℕ → ℕ) (n : ℕ) :
    ∃ y : ZMod (3 ^ ndRootCoreBackwardConductor b k n),
      IsUnit (y.val : ZMod (3 ^ 1)) ∧
      ndRootCoreProbabilityProduct b cap width n ≤
        ndRootCoreBackwardMark b cap width k n y := by
  have hq : 1 ≤ ndRootCoreBackwardConductor b k n := hk.trans (explicitBackwardConductor_ge b k n)
  obtain ⟨y, hy, hg⟩ := explicit_exists_unit_ge_of_supported_mean hq
    (ndRootCoreBackwardMark b cap width k n) (ndRootCoreProbabilityProduct b cap width n)
    (by
      intro y hy
      have hn : ¬ IsUnit (y.val : ZMod (3 ^ 1)) := fun hu =>
        hy ((explicit_unit_levelOne_iff hq y).mp hu)
      simpa only [ZMod.natCast_zmod_val] using
        rootCoreBackwardMark_natCast_eq_zero_of_not_unit b cap width hk n y.val hn)
    (rootCoreBackwardMark_fullMean_eq b cap width k n)
  exact ⟨y, (explicit_unit_levelOne_iff hq y).mpr hy, hg⟩

end

end Erdos1135Predecessor.ND.PositiveDensity
