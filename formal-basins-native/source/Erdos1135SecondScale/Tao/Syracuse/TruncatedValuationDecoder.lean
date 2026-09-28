/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135SecondScale.Tao.Syracuse.ValuationCylinder
import Erdos1135SecondScale.Terras.Parity.Residue

/-!
# Fixed-modulus truncated valuation decoder

This deterministic leaf decodes the first `n` Syracuse valuations from an odd
residue representative modulo `2^M`, retaining every long tuple in the single
overflow value.  It contains no probability law or total-variation argument.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The first `n` actual Syracuse valuations, strictly truncated at weight `M`. -/
noncomputable def taoTruncatedActualValuation
    (n M N : ℕ) (hN : Odd N) : TruncatedValuationTuple n M :=
  truncateValuationList n M (syracuseValuationPNatList n N hN)

/-- Decode an odd residue representative; even representatives belong to the
overflow atom.  At modulus one the sole representative is therefore `none`. -/
noncomputable def taoProp19ResidueDecoder
    (n M : ℕ) (r : ZMod (2 ^ M)) : TruncatedValuationTuple n M :=
  if hodd : Odd r.val then
    taoTruncatedActualValuation n M r.val hodd
  else
    none

private theorem syracuseValuationPNatList_eq_of_modEq_twoPow_of_weight_lt
    {n M N R : ℕ} (hN : Odd N) (hR : Odd R)
    (hmod : Nat.ModEq (2 ^ M) N R)
    (hweight : taoTupleWeight (syracuseValuationPNatList n N hN) < M) :
    syracuseValuationPNatList n R hR =
      syracuseValuationPNatList n N hN := by
  let as := syracuseValuationPNatList n N hN
  have hasLength : as.length = n := by
    exact syracuseValuationPNatList_length n N hN
  have hdepth : taoTupleWeight as + 1 ≤ M := Nat.succ_le_iff.mpr hweight
  have hmodSmall : Nat.ModEq (2 ^ (taoTupleWeight as + 1)) N R :=
    Nat.ModEq.of_dvd (Nat.pow_dvd_pow 2 hdepth) hmod
  have hprefix :
      Terras.parityPrefixList (taoTupleWeight as + 1) N =
        Terras.parityPrefixList (taoTupleWeight as + 1) R :=
    Terras.parityPrefixList_eq_of_modEq_twoPow
      (taoTupleWeight as + 1) hmodSmall
  have hprefixN :
      Terras.parityPrefixList (taoTupleWeight as + 1) N =
        syracuseValuationCylinderWord as := by
    simpa [as] using parityPrefixList_syracuseValuationCylinderWord n N hN
  have hprefixR :
      Terras.parityPrefixList (taoTupleWeight as + 1) R =
        syracuseValuationCylinderWord as := by
    rw [← hprefix]
    exact hprefixN
  have hvalue := (valuation_eq_iff_parityPrefixList_cylinder as hR).2 hprefixR
  simpa only [hasLength] using hvalue

/-- Strictly truncated actual valuations depend only on the source residue
modulo `2^M`. -/
theorem truncatedActualValuation_eq_of_modEq_twoPow
    {n M N R : ℕ} (hN : Odd N) (hR : Odd R)
    (hmod : Nat.ModEq (2 ^ M) N R) :
    taoTruncatedActualValuation n M N hN =
      taoTruncatedActualValuation n M R hR := by
  unfold taoTruncatedActualValuation
  let as := syracuseValuationPNatList n N hN
  let bs := syracuseValuationPNatList n R hR
  have hasLength : as.length = n := syracuseValuationPNatList_length n N hN
  have hbsLength : bs.length = n := syracuseValuationPNatList_length n R hR
  change truncateValuationList n M as = truncateValuationList n M bs
  by_cases hasWeight : taoTupleWeight as < M
  · have hbsEq : bs = as :=
      syracuseValuationPNatList_eq_of_modEq_twoPow_of_weight_lt
        hN hR hmod hasWeight
    rw [hbsEq]
  · by_cases hbsWeight : taoTupleWeight bs < M
    · have hasEq : as = bs :=
        syracuseValuationPNatList_eq_of_modEq_twoPow_of_weight_lt
          hR hN hmod.symm hbsWeight
      rw [hasEq]
    · rw [(truncateValuationList_eq_none_iff_of_length hasLength).2
          (Nat.le_of_not_gt hasWeight),
        (truncateValuationList_eq_none_iff_of_length hbsLength).2
          (Nat.le_of_not_gt hbsWeight)]

@[simp] theorem taoTruncatedActualValuation_cutoff_zero
    (n N : ℕ) (hN : Odd N) :
    taoTruncatedActualValuation n 0 N hN = none := by
  unfold taoTruncatedActualValuation
  rw [truncateValuationList_eq_none_iff]
  exact Or.inr (Nat.zero_le _)

/-- The total residue decoder commutes pointwise with reduction of every odd
natural source modulo `2^M`. -/
theorem taoProp19ResidueDecoder_natCast
    (n M N : ℕ) (hN : Odd N) :
    taoProp19ResidueDecoder n M (N : ZMod (2 ^ M)) =
      taoTruncatedActualValuation n M N hN := by
  cases M with
  | zero =>
      simp [taoProp19ResidueDecoder]
  | succ M =>
      have hmodulusEven : Even (2 ^ (M + 1)) :=
        even_iff_two_dvd.mpr (two_dvd_two_pow_succ M)
      have hoddVal : Odd ((N : ZMod (2 ^ (M + 1))).val) := by
        rw [ZMod.val_natCast]
        exact hN.mod_even hmodulusEven
      rw [taoProp19ResidueDecoder, dif_pos hoddVal]
      apply truncatedActualValuation_eq_of_modEq_twoPow hoddVal hN
      simp [Nat.ModEq, ZMod.val_natCast]

theorem taoProp19ResidueDecoder_modulus_zero
    (n : ℕ) (r : ZMod (2 ^ 0)) :
    taoProp19ResidueDecoder n 0 r = none := by
  simp [taoProp19ResidueDecoder]

theorem truncatedActualValuation_one_five_mod_four (n : ℕ) :
    taoTruncatedActualValuation n 2 1 (by norm_num) =
      taoTruncatedActualValuation n 2 5 (by norm_num) := by
  apply truncatedActualValuation_eq_of_modEq_twoPow
  norm_num [Nat.ModEq]

end

end Tao
end Erdos1135SecondScale
