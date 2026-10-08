/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.ParityBridge

/-!
# Valuation Cylinder Shape Lemmas

This module starts the deterministic decoding bridge from terminal cylinder parity words back to
actual Syracuse valuation tuples.  The first layer only records list shape and odd-tail facts; the
factorization-heavy exponent decoder is left to a later theorem in this module.
-/

namespace Erdos1135SecondScale
namespace Tao

@[simp]
theorem syracuseValuationCylinderWord_nil :
    syracuseValuationCylinderWord ([] : List ℕ+) = [true] := by
  simp [syracuseValuationCylinderWord, syracuseParityList]

theorem syracuseValuationCylinderWord_cons (a : ℕ+) (as : List ℕ+) :
    syracuseValuationCylinderWord (a :: as) =
      syracuseParityBlock a ++ syracuseValuationCylinderWord as := by
  simp [syracuseValuationCylinderWord, syracuseParityList, List.append_assoc]

theorem followsParityList_syracuseValuationCylinderWord_cons
    {a : ℕ+} {as : List ℕ+} {N : ℕ} :
    Terras.FollowsParityList (syracuseValuationCylinderWord (a :: as)) N ↔
      Terras.FollowsParityList (syracuseParityBlock a) N ∧
        Terras.FollowsParityList (syracuseValuationCylinderWord as)
          ((Terras.accelerated^[(syracuseParityBlock a).length]) N) := by
  rw [syracuseValuationCylinderWord_cons]
  exact followsParityList_append

theorem followsParityList_syracuseValuationCylinderWord_cons_weight
    {a : ℕ+} {as : List ℕ+} {N : ℕ} :
    Terras.FollowsParityList (syracuseValuationCylinderWord (a :: as)) N ↔
      Terras.FollowsParityList (syracuseParityBlock a) N ∧
        Terras.FollowsParityList (syracuseValuationCylinderWord as)
          ((Terras.accelerated^[(a : ℕ)]) N) := by
  simpa [syracuseParityBlock_length] using
    (followsParityList_syracuseValuationCylinderWord_cons (a := a) (as := as) (N := N))

theorem odd_of_follows_syracuseValuationCylinderWord
    {as : List ℕ+} {N : ℕ}
    (h : Terras.FollowsParityList (syracuseValuationCylinderWord as) N) :
    Odd N := by
  cases as with
  | nil =>
      simpa [syracuseValuationCylinderWord, syracuseParityList,
        Terras.FollowsParityList, Terras.FollowsParityBit]
        using (Nat.not_even_iff_odd.mp h.1)
  | cons _a _as =>
      simpa [syracuseValuationCylinderWord, syracuseParityList,
        syracuseParityBlock, Terras.FollowsParityList, Terras.FollowsParityBit]
        using (Nat.not_even_iff_odd.mp h.1)

theorem odd_landing_of_follows_block_cylinder_tail
    {a : ℕ+} {as : List ℕ+} {N : ℕ}
    (h : Terras.FollowsParityList
      (syracuseParityBlock a ++ syracuseValuationCylinderWord as) N) :
    Odd ((Terras.accelerated^[(syracuseParityBlock a).length]) N) := by
  exact odd_of_follows_syracuseValuationCylinderWord
    ((followsParityList_append.mp h).2)

theorem twoAdicExponent_pow_mul_odd_local {a M : ℕ} (hM : Odd M) :
    Terras.twoAdicExponent ((2 : ℕ) ^ a * M) = a := by
  have hpowne : (2 : ℕ) ^ a ≠ 0 := by
    exact (Nat.pow_pos (by decide : 0 < (2 : ℕ))).ne'
  have hMne : M ≠ 0 := (Odd.pos hM).ne'
  have hnotdvd : ¬(2 : ℕ) ∣ M := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr hdiv)
  have hfactorM : M.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnotdvd
  unfold Terras.twoAdicExponent
  rw [Nat.factorization_mul hpowne hMne]
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  simp [hfactorM]

theorem two_pow_syracuseParityBlock_length_mul_landing
    {a : ℕ+} {N : ℕ}
    (h : Terras.FollowsParityList (syracuseParityBlock a) N) :
    (2 : ℕ) ^ (syracuseParityBlock a).length *
        ((Terras.accelerated^[(syracuseParityBlock a).length]) N) =
      3 * N + 1 := by
  have haff := Terras.affine_normal_form_list (syracuseParityBlock a) N h
  have haff' :
      ((2 : ℤ) ^ (syracuseParityBlock a).length) *
          ((Terras.accelerated^[(syracuseParityBlock a).length]) N : ℤ) =
        3 * (N : ℤ) + 1 := by
    simpa [branchScaleList_syracuseParityBlock, branchConstList_syracuseParityBlock] using haff
  exact_mod_cast haff'

theorem syracuseExponent_eq_of_follows_block_cylinder_tail
    {a : ℕ+} {as : List ℕ+} {N : ℕ}
    (h : Terras.FollowsParityList
      (syracuseParityBlock a ++ syracuseValuationCylinderWord as) N) :
    syracuseExponent N = (a : ℕ) := by
  rcases followsParityList_append.mp h with ⟨hblock, htail⟩
  have hodd :
      Odd ((Terras.accelerated^[(syracuseParityBlock a).length]) N) :=
    odd_of_follows_syracuseValuationCylinderWord htail
  have hmul := two_pow_syracuseParityBlock_length_mul_landing hblock
  unfold syracuseExponent
  rw [← hmul]
  simpa [syracuseParityBlock_length] using
    twoAdicExponent_pow_mul_odd_local
      (a := (syracuseParityBlock a).length)
      (M := (Terras.accelerated^[(syracuseParityBlock a).length]) N)
      hodd

theorem syracuseValuationPNatList_eq_of_follows_cylinder
    (as : List ℕ+) {N : ℕ} (hN : Odd N)
    (h : Terras.FollowsParityList (syracuseValuationCylinderWord as) N) :
    syracuseValuationPNatList as.length N hN = as := by
  induction as generalizing N with
  | nil =>
      simp [syracuseValuationPNatList]
  | cons a as ih =>
      have hconcat :
          Terras.FollowsParityList (syracuseParityBlock a ++ syracuseValuationCylinderWord as) N := by
        simpa [syracuseValuationCylinderWord_cons] using h
      have hsplit := (followsParityList_syracuseValuationCylinderWord_cons.mp h)
      have hExp : syracuseExponent N = (a : ℕ) :=
        syracuseExponent_eq_of_follows_block_cylinder_tail hconcat
      have hhead :
          (⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩ : ℕ+) = a := by
        ext
        exact hExp
      have hland : (Terras.accelerated^[(syracuseParityBlock a).length]) N = syracuse N := by
        rw [syracuseParityBlock_length]
        rw [← hExp]
        simpa [syracuseParityBlock_length] using
          accelerated_iterate_syracuseParityBlock_length_eq_syracuse hN
      have htail :
          Terras.FollowsParityList (syracuseValuationCylinderWord as) (syracuse N) := by
        rw [← hland]
        exact hsplit.2
      have htail_val := ih (syracuse_odd N) htail
      simp [syracuseValuationPNatList, hhead, htail_val]

theorem valuation_eq_iff_parityPrefixList_cylinder
    (as : List ℕ+) {N : ℕ} (hN : Odd N) :
    syracuseValuationPNatList as.length N hN = as ↔
      Terras.parityPrefixList (taoTupleWeight as + 1) N =
        syracuseValuationCylinderWord as := by
  constructor
  · intro hval
    have h := parityPrefixList_syracuseValuationCylinderWord as.length N hN
    simpa [hval] using h
  · intro hprefix
    have hf0 := Terras.followsParityList_parityPrefixList (taoTupleWeight as + 1) N
    have hf : Terras.FollowsParityList (syracuseValuationCylinderWord as) N := by
      simpa [hprefix] using hf0
    exact syracuseValuationPNatList_eq_of_follows_cylinder as hN hf

end Tao
end Erdos1135SecondScale
