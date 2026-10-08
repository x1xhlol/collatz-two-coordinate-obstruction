/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7SourceLaw
import Erdos1135SecondScale.Tao.Probability.Geom2ListReverse
import Erdos1135SecondScale.Tao.Syracuse.AffineResidue

/-!
# Section 5 Unrestricted Affine Source Law

This leaf reverses only the unrestricted iid Geom(2) list law.  It identifies
the chronological affine residue map with the existing recursive Syracuse PMF
without reversing the prefix-typical finite family.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The affine offset residue in an arbitrary ambient modulus `3^N`. -/
def taoAffineOffsetZModAt (N : ℕ) (as : List ℕ+) : ZMod (3 ^ N) :=
  (taoOffsetNum as : ZMod (3 ^ N)) *
    (((2 : ZMod (3 ^ N)) ^ taoTupleWeight as)⁻¹)

theorem taoAffineOffsetZModAt_self (q : ℕ) (as : List ℕ+) :
    taoAffineOffsetZModAt q as = taoAffineOffsetZMod q as := by
  rfl

/-- The fixed-ambient affine residue of a reversed cons obeys the chronological
Section 7 recurrence. -/
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

/-- The fixed-ambient Section 7 prefix has the same chronological cons
recurrence as the reversed affine residue. -/
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

/-- In a fixed ambient modulus, reversing the affine list gives the Section 7
prefix with the original chronological order. -/
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

/-- Exact orientation bridge between the chronological Section 7 offset and
the affine offset of the reversed valuation list. -/
theorem taoAffineOffsetZMod_reverse_eq_taoSection7OffsetZMod
    {n : ℕ} {as : List ℕ+} (hlen : as.length = n) :
    taoAffineOffsetZMod n as.reverse = taoSection7OffsetZMod n as := by
  rw [← taoAffineOffsetZModAt_self]
  rw [taoAffineOffsetZModAt_reverse_eq_offsetPrefix]
  rw [hlen]
  exact (taoSection7OffsetZMod_eq_offsetPrefix n as).symm

private theorem pmf_map_eq_of_eq_on_support
    {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases hpa : p a = 0
  · simp [hpa]
  · have ha : a ∈ p.support := (p.mem_support_iff a).2 hpa
    rw [h a ha]

/-- The recursive Syracuse source law is exactly the image of the iid Geom(2)
list law under the chronological affine residue map. -/
theorem syracPMF_eq_geom2PNatListPMF_map_taoAffineOffsetZMod (n : ℕ) :
    syracPMF n =
      (geom2PNatListPMF n).map (taoAffineOffsetZMod n) := by
  rw [syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod]
  calc
    (geom2PNatListPMF n).map (taoSection7OffsetZMod n) =
        (geom2PNatListPMF n).map
          (fun as => taoAffineOffsetZMod n as.reverse) := by
      apply pmf_map_eq_of_eq_on_support
      intro as has
      exact (taoAffineOffsetZMod_reverse_eq_taoSection7OffsetZMod
        (geom2PNatListPMF_support_length_eq has)).symm
    _ = ((geom2PNatListPMF n).map List.reverse).map
          (taoAffineOffsetZMod n) := by
      rw [PMF.map_comp]
      rfl
    _ = (geom2PNatListPMF n).map (taoAffineOffsetZMod n) := by
      rw [geom2PNatListPMF_map_reverse]

end

end Tao
end Erdos1135SecondScale
