/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.OffsetInjectivity

/-!
# Odd Natural Endpoints Of Syracuse Affine Maps

This leaf proves the source-facing description of an `n`-Syracuse valuation:
an odd natural affine endpoint uniquely determines the positive valuation
tuple. It contains no probability or Section 5 payload infrastructure.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Closed affine form with its rational denominator and numerator both
represented by natural numbers. -/
theorem taoAffList_nat_eq_num_div
    (as : List ℕ+) (N : ℕ) :
    taoAffList as (N : ℚ) =
      ((3 ^ as.length * N + taoOffsetNum as : ℕ) : ℚ) /
        ((2 ^ taoTupleWeight as : ℕ) : ℚ) := by
  rw [taoAffList_closed, taoOffsetList_eq_num_div]
  push_cast
  field_simp

/-- Exact subtraction-free natural equation equivalent to an affine map
having a natural endpoint. -/
theorem taoAffList_eq_nat_iff_cleared
    (as : List ℕ+) (N M : ℕ) :
    taoAffList as (N : ℚ) = (M : ℚ) ↔
      3 ^ as.length * N + taoOffsetNum as =
        2 ^ taoTupleWeight as * M := by
  rw [taoAffList_nat_eq_num_div]
  have hden : (((2 ^ taoTupleWeight as : ℕ) : ℕ) : ℚ) ≠ 0 := by
    positivity
  constructor
  · intro h
    field_simp [hden] at h
    have hnat :
        3 ^ as.length * N + taoOffsetNum as =
          2 ^ taoTupleWeight as * M := by
      exact_mod_cast h
    exact hnat
  · intro h
    apply (div_eq_iff hden).2
    have hnat :
        3 ^ as.length * N + taoOffsetNum as =
          M * 2 ^ taoTupleWeight as := by
      simpa [Nat.mul_comm] using h
    exact_mod_cast hnat

/-- Strong induction engine: an odd natural affine endpoint reconstructs the
odd source, its actual positive valuation tuple, and its final iterate. -/
theorem taoAffList_oddNat_decode
    (as : List ℕ+) (N M : ℕ) (hM : Odd M)
    (hAff : taoAffList as (N : ℚ) = (M : ℚ)) :
    ∃ hN : Odd N,
      syracuseValuationPNatList as.length N hN = as ∧
        (syracuse^[as.length]) N = M := by
  induction as generalizing N with
  | nil =>
      have hNM : N = M := by
        simpa [taoAffList] using hAff
      subst M
      exact ⟨hM, by simp [syracuseValuationPNatList], by simp⟩
  | cons a tail ih =>
      have hcleared :=
        (taoAffList_eq_nat_iff_cleared (a :: tail) N M).mp hAff
      have hexpanded :
          3 ^ tail.length * (3 * N + 1) +
              2 ^ (a : ℕ) * taoOffsetNum tail =
            2 ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M) := by
        calc
          3 ^ tail.length * (3 * N + 1) +
                2 ^ (a : ℕ) * taoOffsetNum tail =
              3 ^ (a :: tail).length * N + taoOffsetNum (a :: tail) := by
                simp [taoOffsetNum, pow_succ]
                ring
          _ = 2 ^ taoTupleWeight (a :: tail) * M := hcleared
          _ = 2 ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M) := by
                simp [taoTupleWeight, pow_add]
                ring
      have hdiv_rhs :
          2 ^ (a : ℕ) ∣ 2 ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M) :=
        dvd_mul_right _ _
      have hdiv_sum :
          2 ^ (a : ℕ) ∣
            3 ^ tail.length * (3 * N + 1) +
              2 ^ (a : ℕ) * taoOffsetNum tail := by
        rw [hexpanded]
        exact hdiv_rhs
      have hdiv_offset :
          2 ^ (a : ℕ) ∣ 2 ^ (a : ℕ) * taoOffsetNum tail :=
        dvd_mul_right _ _
      have hdiv_product :
          2 ^ (a : ℕ) ∣ 3 ^ tail.length * (3 * N + 1) :=
        (Nat.dvd_add_iff_left hdiv_offset).mpr hdiv_sum
      have hcoprime : Nat.Coprime (2 ^ (a : ℕ)) (3 ^ tail.length) :=
        Nat.Coprime.pow (a : ℕ) tail.length (by decide : Nat.Coprime 2 3)
      have hdiv_head : 2 ^ (a : ℕ) ∣ 3 * N + 1 :=
        hcoprime.dvd_of_dvd_mul_left hdiv_product
      rcases hdiv_head with ⟨N₁, hN₁⟩
      have hfactor :
          2 ^ (a : ℕ) *
              (3 ^ tail.length * N₁ + taoOffsetNum tail) =
            2 ^ (a : ℕ) * (2 ^ taoTupleWeight tail * M) := by
        rw [← hexpanded]
        rw [hN₁]
        ring
      have htailCleared :
          3 ^ tail.length * N₁ + taoOffsetNum tail =
            2 ^ taoTupleWeight tail * M :=
        Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) (a : ℕ)) hfactor
      have htailAff : taoAffList tail (N₁ : ℚ) = (M : ℚ) :=
        (taoAffList_eq_nat_iff_cleared tail N₁ M).2 htailCleared
      rcases ih N₁ htailAff with ⟨hN₁odd, htailValues, htailIterate⟩
      have hNodd : Odd N := by
        rcases Nat.even_or_odd N with hNeven | hNodd
        · rcases hNeven with ⟨q, hq⟩
          obtain ⟨r, hr⟩ : ∃ r, (a : ℕ) = r + 1 := by
            exact Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt a.2)
          have hheadEven : Even (3 * N + 1) := by
            refine ⟨2 ^ r * N₁, ?_⟩
            rw [hN₁, hr, pow_succ]
            ring
          rcases hheadEven with ⟨b, hb⟩
          omega
        · exact hNodd
      have hfactorization :
          2 ^ (a : ℕ) * N₁ =
            2 ^ syracuseExponent N * syracuse N :=
        hN₁.symm.trans (two_pow_syracuseExponent_mul_syracuse N).symm
      rcases two_pow_mul_odd_cancel hN₁odd (syracuse_odd N) hfactorization with
        ⟨ha, hnext⟩
      have hhead :
          (⟨syracuseExponent N, syracuseExponent_pos_of_odd hNodd⟩ : ℕ+) = a :=
        Subtype.ext ha.symm
      have htailValues' :
          syracuseValuationPNatList tail.length (syracuse N) (syracuse_odd N) =
            tail := by
        simpa [hnext] using htailValues
      have hvalues :
          syracuseValuationPNatList (a :: tail).length N hNodd = a :: tail := by
        simp [syracuseValuationPNatList, hhead, htailValues']
      have hiterate : (syracuse^[(a :: tail).length]) N = M := by
        simpa [Function.iterate_succ_apply, hnext] using htailIterate
      exact ⟨hNodd, hvalues, hiterate⟩

/-- Source-facing uniqueness form of Tao's description of the `n`-Syracuse
valuation. Both the source and affine endpoint are explicitly odd. -/
theorem taoAffList_eq_oddNat_iff
    (as : List ℕ+) {N M : ℕ} (hN : Odd N) (hM : Odd M) :
    taoAffList as (N : ℚ) = (M : ℚ) ↔
      syracuseValuationPNatList as.length N hN = as ∧
        (syracuse^[as.length]) N = M := by
  constructor
  · intro hAff
    rcases taoAffList_oddNat_decode as N M hM hAff with
      ⟨hN', hvalues, hiterate⟩
    exact ⟨by simpa using hvalues, hiterate⟩
  · rintro ⟨hvalues, hiterate⟩
    calc
      taoAffList as (N : ℚ) =
          taoAffList (syracuseValuationPNatList as.length N hN) (N : ℚ) := by
            rw [hvalues]
      _ = ((syracuse^[as.length]) N : ℚ) := by
            exact (syracuse_iterate_eq_taoAffList as.length N hN).symm
      _ = (M : ℚ) := by rw [hiterate]

example :
    ∃ hN : Odd 3,
      syracuseValuationPNatList 2 3 hN = [(1 : ℕ+), (4 : ℕ+)] ∧
        (syracuse^[2]) 3 = 1 :=
  taoAffList_oddNat_decode [(1 : ℕ+), (4 : ℕ+)] 3 1 (by norm_num)
    taoAffList_one_four_three

example : taoAffList [(1 : ℕ+), (3 : ℕ+)] (3 : ℚ) = 2 := by
  norm_num [taoAffList, taoSingleAff]

example : ¬ Odd 2 := by norm_num

example :
    ∃ hN : Odd 7,
      syracuseValuationPNatList 3 7 hN = [(1 : ℕ+), (1 : ℕ+), (2 : ℕ+)] ∧
        (syracuse^[3]) 7 = 13 := by
  apply taoAffList_oddNat_decode [(1 : ℕ+), (1 : ℕ+), (2 : ℕ+)] 7 13
  · norm_num
  · norm_num [taoAffList, taoSingleAff]

end Tao
end Erdos1135SecondScale
