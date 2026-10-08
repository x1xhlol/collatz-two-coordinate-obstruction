/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Probability.Geom2ListReverse
import Erdos1135Predecessor.Tao.Syracuse.AffineResidue

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

def taoAffineOffsetZModAt (N : ℕ) (as : List ℕ+) : ZMod (3 ^ N) :=
  (taoOffsetNum as : ZMod (3 ^ N)) *
    (((2 : ZMod (3 ^ N)) ^ taoTupleWeight as)⁻¹)

theorem taoAffineOffsetZModAt_self (q : ℕ) (as : List ℕ+) :
    taoAffineOffsetZModAt q as = taoAffineOffsetZMod q as := by
  rfl

theorem taoAffineOffsetZModAt_reverse_cons
    (N : ℕ) (a : ℕ+) (as : List ℕ+) :
    taoAffineOffsetZModAt N (a :: as).reverse =
      (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
        (1 + 3 * taoAffineOffsetZModAt N as.reverse) := by
  have hweightCons :
      taoTupleWeight (a :: as) = (a : ℕ) + taoTupleWeight as := by
    exact taoTupleWeight_cons a as
  unfold taoAffineOffsetZModAt
  rw [taoOffsetNum_reverse_cons, taoTupleWeight_reverse (a :: as),
    hweightCons, taoTupleWeight_reverse as]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [taoZModThreePow_inv_two_pow_add]
  calc
    ((2 : ZMod (3 ^ N)) ^ taoTupleWeight as +
          3 * (taoOffsetNum as.reverse : ZMod (3 ^ N))) *
        ((((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
          (((2 : ZMod (3 ^ N)) ^ taoTupleWeight as)⁻¹)) =
      (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
        ((((2 : ZMod (3 ^ N)) ^ taoTupleWeight as)⁻¹) *
            ((2 : ZMod (3 ^ N)) ^ taoTupleWeight as) +
          3 * ((taoOffsetNum as.reverse : ZMod (3 ^ N)) *
            (((2 : ZMod (3 ^ N)) ^ taoTupleWeight as)⁻¹))) := by
              ring
    _ = (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
        (1 + 3 * ((taoOffsetNum as.reverse : ZMod (3 ^ N)) *
          (((2 : ZMod (3 ^ N)) ^ taoTupleWeight as)⁻¹))) := by
      rw [taoZModThreePow_inv_two_pow_mul]

theorem taoSection7OffsetPrefix_cons
    (N k : ℕ) (a : ℕ+) (as : List ℕ+) :
    taoSection7OffsetPrefix N (k + 1) (a :: as) =
      (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
        (1 + 3 * taoSection7OffsetPrefix N k as) := by
  unfold taoSection7OffsetPrefix taoSection7OffsetSummand
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, List.take_succ_cons, List.take_zero,
    taoTupleWeight_cons, taoTupleWeight_nil, Nat.add_zero]
  have hshift :
    (∑ i ∈ Finset.range k,
        (3 : ZMod (3 ^ N)) ^ (i + 1) *
          (((2 : ZMod (3 ^ N)) ^
            ((a : ℕ) + taoTupleWeight (as.take (i + 1))))⁻¹)) =
      ∑ i ∈ Finset.range k,
        (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
          (3 * ((3 : ZMod (3 ^ N)) ^ i *
            (((2 : ZMod (3 ^ N)) ^
              taoTupleWeight (as.take (i + 1)))⁻¹))) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [taoZModThreePow_inv_two_pow_add, pow_succ']
    ring
  rw [hshift]
  have hfactor :
      (∑ i ∈ Finset.range k,
        (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
          (3 * ((3 : ZMod (3 ^ N)) ^ i *
            (((2 : ZMod (3 ^ N)) ^
              taoTupleWeight (as.take (i + 1)))⁻¹)))) =
        (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
          (3 * (∑ i ∈ Finset.range k,
            (3 : ZMod (3 ^ N)) ^ i *
              (((2 : ZMod (3 ^ N)) ^
                taoTupleWeight (as.take (i + 1)))⁻¹))) := by
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
  rw [hfactor]
  ring

theorem taoAffineOffsetZModAt_reverse_eq_offsetPrefix
    (N : ℕ) (as : List ℕ+) :
    taoAffineOffsetZModAt N as.reverse =
      taoSection7OffsetPrefix N as.length as := by
  induction as with
  | nil =>
      simp [taoAffineOffsetZModAt, taoOffsetNum, taoTupleWeight,
        taoSection7OffsetPrefix]
  | cons a as ih =>
      rw [List.length_cons, taoAffineOffsetZModAt_reverse_cons,
        taoSection7OffsetPrefix_cons, ih]

theorem taoAffineOffsetZMod_reverse_eq_taoSection7OffsetZMod
    {n : ℕ} {as : List ℕ+} (hlen : as.length = n) :
    taoAffineOffsetZMod n as.reverse = taoSection7OffsetZMod n as := by
  rw [← taoAffineOffsetZModAt_self]
  rw [taoAffineOffsetZModAt_reverse_eq_offsetPrefix]
  rw [hlen]
  exact (taoSection7OffsetZMod_eq_offsetPrefix n as).symm

end

end Tao

end Erdos1135Predecessor
