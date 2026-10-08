import Erdos1135.Tao.Syracuse.Affine
import Erdos1135.Terras.Parity.Word

set_option backward.isDefEq.respectTransparency false

/-!
# Bridge From Syracuse Valuation Tuples To Terras Parity Lists

This module starts the deterministic convention bridge between Tao's positive valuation tuples and
the Terras accelerated parity-list affine infrastructure.  The initial surface fixes block shape,
length, odd-branch count, and cleared scale.
-/

namespace Erdos1135
namespace Tao

/-- Terras parity block for a positive Syracuse valuation: one odd branch then even branches. -/
def syracuseParityBlock (a : ℕ+) : List Bool :=
  true :: List.replicate ((a : ℕ) - 1) false

/-- Terras parity list associated to a source-ordered positive Syracuse valuation tuple. -/
def syracuseParityList : List ℕ+ → List Bool
  | [] => []
  | a :: as => syracuseParityBlock a ++ syracuseParityList as

/-- Terminal parity word for exact valuation cylinders; the final `true` starts the next block. -/
def syracuseValuationCylinderWord (as : List ℕ+) : List Bool :=
  syracuseParityList as ++ [true]

theorem syracuseParityBlock_length (a : ℕ+) :
    (syracuseParityBlock a).length = (a : ℕ) := by
  have ha : 1 ≤ (a : ℕ) := Nat.succ_le_iff.mpr a.2
  simp [syracuseParityBlock]
  omega

theorem syracuseParityList_length (as : List ℕ+) :
    (syracuseParityList as).length = taoTupleWeight as := by
  induction as with
  | nil =>
      simp [syracuseParityList, taoTupleWeight]
  | cons a as ih =>
      simp [syracuseParityList, taoTupleWeight, syracuseParityBlock_length, ih]

theorem syracuseValuationCylinderWord_length (as : List ℕ+) :
    (syracuseValuationCylinderWord as).length = taoTupleWeight as + 1 := by
  simp [syracuseValuationCylinderWord, syracuseParityList_length]

theorem syracuseParityBlock_count_true (a : ℕ+) :
    (syracuseParityBlock a).count true = 1 := by
  simp [syracuseParityBlock, List.count_replicate]

theorem syracuseParityList_count_true (as : List ℕ+) :
    (syracuseParityList as).count true = as.length := by
  induction as with
  | nil =>
      simp [syracuseParityList]
  | cons a as ih =>
      simp [syracuseParityList, syracuseParityBlock_count_true, ih]
      omega

theorem syracuseValuationCylinderWord_count_true (as : List ℕ+) :
    (syracuseValuationCylinderWord as).count true = as.length + 1 := by
  simp [syracuseValuationCylinderWord, List.count_append, syracuseParityList_count_true]

theorem branchScaleList_replicate_false (n : ℕ) :
    Terras.branchScaleList (List.replicate n false) = 1 := by
  induction n with
  | zero =>
      simp [Terras.branchScaleList]
  | succ n ih =>
      simp [List.replicate, Terras.branchScaleList, Terras.branchScale, ih]

theorem branchScaleList_syracuseParityBlock (a : ℕ+) :
    Terras.branchScaleList (syracuseParityBlock a) = 3 := by
  simp [syracuseParityBlock, Terras.branchScaleList, Terras.branchScale,
    branchScaleList_replicate_false]

theorem branchScaleList_append (xs ys : List Bool) :
    Terras.branchScaleList (xs ++ ys) =
      Terras.branchScaleList xs * Terras.branchScaleList ys := by
  simp [Terras.branchScaleList_eq_list_prod, List.map_append, List.prod_append]

theorem branchScaleList_syracuseParityList (as : List ℕ+) :
    Terras.branchScaleList (syracuseParityList as) = (3 : ℤ) ^ as.length := by
  induction as with
  | nil =>
      simp [syracuseParityList, Terras.branchScaleList]
  | cons a as ih =>
      simp [syracuseParityList, branchScaleList_append,
        branchScaleList_syracuseParityBlock, ih, pow_succ]
      ring

theorem branchConstList_append (xs ys : List Bool) :
    Terras.branchConstList (xs ++ ys) =
      Terras.branchScaleList ys * Terras.branchConstList xs +
        (2 : ℤ) ^ xs.length * Terras.branchConstList ys := by
  induction xs with
  | nil =>
      simp [Terras.branchConstList]
  | cons x xs ih =>
      simp [Terras.branchConstList, branchScaleList_append, ih, pow_succ]
      ring

theorem branchConstList_replicate_false (n : ℕ) :
    Terras.branchConstList (List.replicate n false) = 0 := by
  induction n with
  | zero =>
      simp [Terras.branchConstList]
  | succ n ih =>
      simp [List.replicate, Terras.branchConstList, Terras.branchOffset, ih]

theorem branchConstList_syracuseParityBlock (a : ℕ+) :
    Terras.branchConstList (syracuseParityBlock a) = 1 := by
  simp [syracuseParityBlock, Terras.branchConstList, Terras.branchOffset,
    branchScaleList_replicate_false, branchConstList_replicate_false]

theorem taoOffsetList_eq_branchConstList (as : List ℕ+) :
    taoOffsetList as =
      (Terras.branchConstList (syracuseParityList as) : ℚ) /
        (2 : ℚ) ^ taoTupleWeight as := by
  induction as with
  | nil =>
      simp [taoOffsetList, syracuseParityList, Terras.branchConstList, taoTupleWeight]
  | cons a as ih =>
      rw [taoOffsetList]
      simp only [syracuseParityList]
      rw [branchConstList_append]
      rw [branchConstList_syracuseParityBlock]
      rw [branchScaleList_syracuseParityList]
      rw [syracuseParityBlock_length]
      rw [ih]
      simp [taoTupleWeight]
      field_simp [pow_ne_zero]
      ring

theorem parityBit_eq_of_follows {b : Bool} {N : ℕ}
    (h : Terras.FollowsParityBit b N) :
    Terras.parityBit N = b := by
  cases b <;> simp [Terras.FollowsParityBit, Terras.parityBit] at h ⊢ <;> exact h

theorem parityPrefixList_eq_of_follows :
    ∀ {ps : List Bool} {N : ℕ},
      Terras.FollowsParityList ps N →
        Terras.parityPrefixList ps.length N = ps
  | [], _N, _h => by
      simp [Terras.parityPrefixList]
  | b :: ps, _N, h => by
      rcases h with ⟨hb, hps⟩
      simp [Terras.parityPrefixList, parityBit_eq_of_follows hb,
        parityPrefixList_eq_of_follows hps]

theorem followsParityList_replicate_false_of_pow_dvd :
    ∀ {k M : ℕ}, (2 : ℕ) ^ k ∣ M →
      Terras.FollowsParityList (List.replicate k false) M
  | 0, _M, _h => by
      simp [Terras.FollowsParityList]
  | k + 1, M, h => by
      have htwo_dvd_pow : (2 : ℕ) ∣ 2 ^ (k + 1) := by
        refine ⟨2 ^ k, ?_⟩
        rw [pow_succ]
        ring
      have hEven : Even M := even_iff_two_dvd.mpr (dvd_trans htwo_dvd_pow h)
      have htail : (2 : ℕ) ^ k ∣ Terras.accelerated M := by
        rw [Terras.accelerated_eq_div_two_of_even hEven]
        rw [Nat.dvd_div_iff_mul_dvd (even_iff_two_dvd.mp hEven)]
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
      simp [List.replicate, Terras.FollowsParityList, Terras.FollowsParityBit, hEven,
        followsParityList_replicate_false_of_pow_dvd htail]

theorem followsParityList_syracuseParityBlock {N : ℕ} (hN : Odd N) :
    Terras.FollowsParityList
      (syracuseParityBlock
        ⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩) N := by
  rcases Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (syracuseExponent_pos_of_odd hN)) with ⟨k, hk⟩
  have hpow : (2 : ℕ) ^ (k + 1) ∣ 3 * N + 1 := by
    rw [← Nat.succ_eq_add_one k]
    rw [← hk]
    simpa [syracuseExponent, Terras.twoAdicExponent] using Nat.ordProj_dvd (3 * N + 1) 2
  have htwo_dvd_pow : (2 : ℕ) ∣ 2 ^ (k + 1) := by
    refine ⟨2 ^ k, ?_⟩
    rw [pow_succ]
    ring
  have htwo : (2 : ℕ) ∣ 3 * N + 1 := dvd_trans htwo_dvd_pow hpow
  have hnotEven : ¬ Even N := Nat.not_even_iff_odd.mpr hN
  have htail : (2 : ℕ) ^ k ∣ Terras.accelerated N := by
    rw [Terras.accelerated_eq_three_mul_add_one_div_two_of_not_even hnotEven]
    rw [Nat.dvd_div_iff_mul_dvd htwo]
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hpow
  change Terras.FollowsParityList
    (true :: List.replicate (syracuseExponent N - 1) false) N
  rw [hk]
  simp [Terras.FollowsParityList, Terras.FollowsParityBit, hnotEven,
    followsParityList_replicate_false_of_pow_dvd htail]

theorem accelerated_iterate_syracuseParityBlock_length_eq_syracuse
    {N : ℕ} (hN : Odd N) :
    (Terras.accelerated^[
      (syracuseParityBlock
        ⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩).length]) N =
      syracuse N := by
  let a : ℕ+ := ⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩
  have hfollows : Terras.FollowsParityList (syracuseParityBlock a) N := by
    dsimp [a]
    exact followsParityList_syracuseParityBlock hN
  have haff := Terras.affine_normal_form_list (syracuseParityBlock a) N hfollows
  have haff' :
      ((2 : ℤ) ^ syracuseExponent N) *
          ((Terras.accelerated^[syracuseExponent N]) N : ℤ) =
        3 * (N : ℤ) + 1 := by
    dsimp [a] at haff
    simpa [syracuseParityBlock_length, branchScaleList_syracuseParityBlock,
      branchConstList_syracuseParityBlock] using haff
  have hsyr' :
      ((2 : ℤ) ^ syracuseExponent N) * (syracuse N : ℤ) =
        3 * (N : ℤ) + 1 := by
    exact_mod_cast two_pow_syracuseExponent_mul_syracuse N
  have hsame :
      ((2 : ℤ) ^ syracuseExponent N) *
          ((Terras.accelerated^[syracuseExponent N]) N : ℤ) =
        ((2 : ℤ) ^ syracuseExponent N) * (syracuse N : ℤ) :=
    haff'.trans hsyr'.symm
  rw [syracuseParityBlock_length]
  change (Terras.accelerated^[syracuseExponent N]) N = syracuse N
  exact_mod_cast (mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)) hsame)

theorem followsParityList_append {xs ys : List Bool} {N : ℕ} :
    Terras.FollowsParityList (xs ++ ys) N ↔
      Terras.FollowsParityList xs N ∧
        Terras.FollowsParityList ys ((Terras.accelerated^[xs.length]) N) := by
  induction xs generalizing N with
  | nil =>
      simp [Terras.FollowsParityList]
  | cons x xs ih =>
      simp [Terras.FollowsParityList, ih, Function.iterate_succ_apply, and_assoc]

theorem followsParityList_syracuseValuationPNatList
    (n N : ℕ) (hN : Odd N) :
    Terras.FollowsParityList
      (syracuseParityList (syracuseValuationPNatList n N hN)) N := by
  induction n generalizing N with
  | zero =>
      simp [syracuseValuationPNatList, syracuseParityList, Terras.FollowsParityList]
  | succ n ih =>
      let a : ℕ+ := ⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩
      have hblock : Terras.FollowsParityList (syracuseParityBlock a) N := by
        dsimp [a]
        exact followsParityList_syracuseParityBlock hN
      have hland : (Terras.accelerated^[(syracuseParityBlock a).length]) N = syracuse N := by
        dsimp [a]
        exact accelerated_iterate_syracuseParityBlock_length_eq_syracuse hN
      have htail :
          Terras.FollowsParityList
            (syracuseParityList (syracuseValuationPNatList n (syracuse N) (syracuse_odd N)))
            ((Terras.accelerated^[(syracuseParityBlock a).length]) N) := by
        rw [hland]
        exact ih (syracuse N) (syracuse_odd N)
      simp [syracuseValuationPNatList, syracuseParityList]
      exact followsParityList_append.2 ⟨hblock, htail⟩

theorem parityPrefixList_syracuseValuationPNatList
    (n N : ℕ) (hN : Odd N) :
    Terras.parityPrefixList
        (taoTupleWeight (syracuseValuationPNatList n N hN)) N =
      syracuseParityList (syracuseValuationPNatList n N hN) := by
  rw [← syracuseParityList_length]
  exact parityPrefixList_eq_of_follows
    (followsParityList_syracuseValuationPNatList n N hN)

theorem accelerated_iterate_taoTupleWeight_syracuseValuationPNatList
    (n N : ℕ) (hN : Odd N) :
    (Terras.accelerated^[taoTupleWeight (syracuseValuationPNatList n N hN)]) N =
      (syracuse^[n]) N := by
  induction n generalizing N with
  | zero =>
      simp [syracuseValuationPNatList, taoTupleWeight]
  | succ n ih =>
      let a : ℕ+ := ⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩
      have hland : (Terras.accelerated^[(syracuseParityBlock a).length]) N = syracuse N := by
        dsimp [a]
        exact accelerated_iterate_syracuseParityBlock_length_eq_syracuse hN
      have hland' : (Terras.accelerated^[syracuseExponent N]) N = syracuse N := by
        dsimp [a] at hland
        simpa [syracuseParityBlock_length] using hland
      simp [syracuseValuationPNatList, taoTupleWeight]
      rw [Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [hland']
      simpa [taoTupleWeight] using ih (syracuse N) (syracuse_odd N)

theorem syracuse_iterate_odd (n N : ℕ) (hN : Odd N) :
    Odd ((syracuse^[n]) N) := by
  induction n generalizing N with
  | zero =>
      simpa using hN
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (syracuse N) (syracuse_odd N)

theorem followsParityList_syracuseValuationCylinderWord
    (n N : ℕ) (hN : Odd N) :
    Terras.FollowsParityList
      (syracuseValuationCylinderWord (syracuseValuationPNatList n N hN)) N := by
  let as := syracuseValuationPNatList n N hN
  have hmain : Terras.FollowsParityList (syracuseParityList as) N := by
    dsimp [as]
    exact followsParityList_syracuseValuationPNatList n N hN
  have hland :
      (Terras.accelerated^[(syracuseParityList as).length]) N = (syracuse^[n]) N := by
    rw [syracuseParityList_length]
    dsimp [as]
    exact accelerated_iterate_taoTupleWeight_syracuseValuationPNatList n N hN
  have htail :
      Terras.FollowsParityList [true]
        ((Terras.accelerated^[(syracuseParityList as).length]) N) := by
    rw [hland]
    simp [Terras.FollowsParityList, Terras.FollowsParityBit,
      Nat.not_even_iff_odd.mpr (syracuse_iterate_odd n N hN)]
  dsimp [syracuseValuationCylinderWord, as]
  exact followsParityList_append.2 ⟨hmain, htail⟩

theorem parityPrefixList_syracuseValuationCylinderWord
    (n N : ℕ) (hN : Odd N) :
    Terras.parityPrefixList
        (taoTupleWeight (syracuseValuationPNatList n N hN) + 1) N =
      syracuseValuationCylinderWord (syracuseValuationPNatList n N hN) := by
  rw [← syracuseValuationCylinderWord_length]
  exact parityPrefixList_eq_of_follows
    (followsParityList_syracuseValuationCylinderWord n N hN)

end Tao
end Erdos1135
