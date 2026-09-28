import Erdos1135.Tao.Syracuse.ValuationCylinderResidue
import Mathlib.Data.Nat.ModEq

/-!
# Chinese Remainder Classes For Syracuse Valuation Cylinders

This module combines the exact valuation-cylinder class modulo `2 ^ (S + 1)` with an independent
class modulo `3 ^ q`.  The product modulus retains the forced initial odd bit; replacing `S + 1`
by `S` would not determine the valuation tuple.
-/

namespace Erdos1135
namespace Tao

private theorem coprime_two_pow_three_pow (a b : ℕ) :
    Nat.Coprime (2 ^ a) (3 ^ b) :=
  Nat.Coprime.pow a b (by decide)

/-- The canonical natural representative of the joint valuation-cylinder and `3 ^ q` class. -/
noncomputable def syracuseValuationCylinderCRTResidue
    (as : List ℕ+) (q : ℕ) (X : ZMod (3 ^ q)) : ℕ :=
  Nat.chineseRemainder
    (coprime_two_pow_three_pow (taoTupleWeight as + 1) q)
    (syracuseValuationCylinderResidue as).val X.val

theorem syracuseValuationCylinderCRTResidue_modEq_twoPow
    (as : List ℕ+) (q : ℕ) (X : ZMod (3 ^ q)) :
    syracuseValuationCylinderCRTResidue as q X ≡
      (syracuseValuationCylinderResidue as).val
        [MOD 2 ^ (taoTupleWeight as + 1)] := by
  exact (Nat.chineseRemainder
    (coprime_two_pow_three_pow (taoTupleWeight as + 1) q)
    (syracuseValuationCylinderResidue as).val X.val).prop.1

theorem syracuseValuationCylinderCRTResidue_modEq_threePow
    (as : List ℕ+) (q : ℕ) (X : ZMod (3 ^ q)) :
    syracuseValuationCylinderCRTResidue as q X ≡ X.val [MOD 3 ^ q] := by
  exact (Nat.chineseRemainder
    (coprime_two_pow_three_pow (taoTupleWeight as + 1) q)
    (syracuseValuationCylinderResidue as).val X.val).prop.2

/-- The valuation tuple and the coefficient-fiber residue are equivalent to one class modulo the
coprime product `2 ^ (S + 1) * 3 ^ q`. -/
theorem syracuseValuationPNatList_eq_and_natCast_eq_iff_modEq_crt
    (as : List ℕ+) (q : ℕ) (X : ZMod (3 ^ q)) {N : ℕ} (hN : Odd N) :
    (syracuseValuationPNatList as.length N hN = as ∧
        (N : ZMod (3 ^ q)) = X) ↔
      N ≡ syracuseValuationCylinderCRTResidue as q X
        [MOD 2 ^ (taoTupleWeight as + 1) * 3 ^ q] := by
  constructor
  · rintro ⟨hval, hthree⟩
    have htwoCast :
        (N : ZMod (2 ^ (taoTupleWeight as + 1))) =
          syracuseValuationCylinderResidue as :=
      (syracuseValuationPNatList_eq_iff_natCast_eq_cylinderResidue as hN).mp hval
    have htwo :
        N ≡ (syracuseValuationCylinderResidue as).val
          [MOD 2 ^ (taoTupleWeight as + 1)] := by
      rw [← ZMod.natCast_zmod_val (syracuseValuationCylinderResidue as),
        ZMod.natCast_eq_natCast_iff] at htwoCast
      exact htwoCast
    have hthree' : N ≡ X.val [MOD 3 ^ q] := by
      rw [← ZMod.natCast_zmod_val X, ZMod.natCast_eq_natCast_iff] at hthree
      exact hthree
    exact Nat.chineseRemainder_modEq_unique
      (coprime_two_pow_three_pow (taoTupleWeight as + 1) q) htwo hthree'
  · intro hcrt
    have htwo :
        N ≡ (syracuseValuationCylinderResidue as).val
          [MOD 2 ^ (taoTupleWeight as + 1)] :=
      (hcrt.of_mul_right (3 ^ q)).trans
        (syracuseValuationCylinderCRTResidue_modEq_twoPow as q X)
    have hthree : N ≡ X.val [MOD 3 ^ q] :=
      (hcrt.of_mul_left (2 ^ (taoTupleWeight as + 1))).trans
        (syracuseValuationCylinderCRTResidue_modEq_threePow as q X)
    have htwoCast :
        (N : ZMod (2 ^ (taoTupleWeight as + 1))) =
          syracuseValuationCylinderResidue as := by
      rw [← ZMod.natCast_zmod_val (syracuseValuationCylinderResidue as),
        ZMod.natCast_eq_natCast_iff]
      exact htwo
    have hthreeCast : (N : ZMod (3 ^ q)) = X := by
      rw [← ZMod.natCast_zmod_val X, ZMod.natCast_eq_natCast_iff]
      exact hthree
    exact ⟨
      (syracuseValuationPNatList_eq_iff_natCast_eq_cylinderResidue as hN).mpr htwoCast,
      hthreeCast⟩

end Tao
end Erdos1135
