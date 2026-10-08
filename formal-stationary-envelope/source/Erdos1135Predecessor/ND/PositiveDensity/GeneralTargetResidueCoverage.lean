/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetSeedNonreturn
import Erdos1135Predecessor.ND.PositiveDensity.PredecessorAnalyticSupport
import Erdos1135Predecessor.ND.PositiveDensity.SuccessfulRootTernaryResidueCoverage

namespace Erdos1135Predecessor.ND.PositiveDensity

def ndGeneralTargetRoot (r k : ℕ) : ℕ :=
  (3 * r + 1) * ndA5PreviousPhysicalCollapseSource k + r

theorem generalTargetRoot_cleared (r k : ℕ) :
    3 * ndGeneralTargetRoot r k + 1 = 4 ^ k * (3 * r + 1) := by
  have h := three_mul_ndA5PreviousPhysicalCollapseSource_add_one k
  unfold ndGeneralTargetRoot
  nlinarith

theorem generalTargetRoot_ge_index (r k : ℕ) : k ≤ ndGeneralTargetRoot r k := by
  have h := self_le_ndA5PreviousPhysicalCollapseSource k
  unfold ndGeneralTargetRoot
  nlinarith

theorem generalTargetRoot_odd (r k : ℕ) (hk : 0 < k) : Odd (ndGeneralTargetRoot r k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hc := three_mul_ndA5PreviousPhysicalCollapseSource_add_one (j + 1)
  have hform : ndGeneralTargetRoot r (j + 1) =
      4 ^ (j + 1) * r + ndA5PreviousPhysicalCollapseSource (j + 1) := by
    unfold ndGeneralTargetRoot
    nlinarith
  obtain ⟨t, ht⟩ := ndA5PreviousPhysicalCollapseSource_odd j
  refine ⟨2 * 4 ^ j * r + t, ?_⟩
  rw [hform, pow_succ, ht]
  ring

theorem generalTargetRoot_residue_injective (r q : ℕ) :
    Function.Injective (fun m : Fin (3 ^ q) =>
      (⟨ndGeneralTargetRoot r m % 3 ^ q, Nat.mod_lt _ (by positivity)⟩ : Fin (3 ^ q))) := by
  intro m n he
  have hmod : Nat.ModEq (3 ^ q) (ndGeneralTargetRoot r m) (ndGeneralTargetRoot r n) :=
    congrArg Fin.val he
  have hc : Nat.Coprime (3 ^ q) (3 * r + 1) := by
    apply Nat.Coprime.pow_left
    simpa only [Nat.add_comm] using (Nat.coprime_add_mul_left_right 3 1 r).mpr
      (Nat.coprime_one_right 3)
  have hm : Nat.ModEq (3 ^ q) (ndA5PreviousPhysicalCollapseSource m)
      (ndA5PreviousPhysicalCollapseSource n) :=
    Nat.ModEq.cancel_left_of_coprime hc (Nat.ModEq.add_right_cancel' r hmod)
  exact ndCollapseSource_residue_injective q (Fin.ext hm)

theorem generalTargetRoot_residue_surjective (r q : ℕ) :
    Function.Surjective (fun m : Fin (3 ^ q) =>
      (⟨ndGeneralTargetRoot r m % 3 ^ q, Nat.mod_lt _ (by positivity)⟩ : Fin (3 ^ q))) :=
  Finite.surjective_of_injective (generalTargetRoot_residue_injective r q)

theorem generalTargetRoot_modEq_of_period (r q m t : ℕ) :
    Nat.ModEq (3 ^ q) (ndGeneralTargetRoot r m)
      (ndGeneralTargetRoot r (m + t * 3 ^ q)) := by
  have h := (ndCollapseSource_modEq_of_add_iff q m (t * 3 ^ q)).2
    (Nat.dvd_mul_left _ _)
  exact (h.mul_left (3 * r + 1)).add_right r

theorem exists_generalTargetRoot_start {a : ℕ} (_ha : 0 < a) (hthree : ¬ 3 ∣ a) :
    ∃ r e : ℕ, 0 < e ∧ 3 * r + 1 = 2 ^ e * a := by
  have hmod : a % 3 = 1 ∨ a % 3 = 2 := by
    have hlt := Nat.mod_lt a (by norm_num : 0 < 3)
    have hn : a % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hthree
    omega
  rcases hmod with h | h
  · refine ⟨(4 * a) / 3, 2, by norm_num, ?_⟩
    have hm : (4 * a) % 3 = 1 := by simp [Nat.mul_mod, h]
    norm_num
    omega
  · refine ⟨(2 * a) / 3, 1, by norm_num, ?_⟩
    have hm : (2 * a) % 3 = 1 := by simp [Nat.mul_mod, h]
    norm_num
    omega

theorem generalTargetRoot_reaches {a r e k : ℕ}
    (hstart : 3 * r + 1 = 2 ^ e * a) (hk : 0 < k) :
    Erdos1135Predecessor.Reaches (ndGeneralTargetRoot r k) a := by
  have ho := generalTargetRoot_odd r k hk
  have hc : 3 * ndGeneralTargetRoot r k + 1 = 2 ^ (2 * k + e) * a := by
    rw [generalTargetRoot_cleared, hstart, pow_add, pow_mul]
    norm_num
    ring
  refine ⟨2 * k + e + 1, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_one,
    Erdos1135Predecessor.collatzStep_eq_three_mul_add_one_of_not_even (Nat.not_even_iff_odd.mpr ho), hc]
  exact Tao.collatz_iterate_powTwo_mul (2 * k + e) a

theorem generalTargetRoot_syracuse (r k : ℕ) :
    Tao.syracuse (ndGeneralTargetRoot r k) = Tao.syracuse r := by
  rw [Tao.syracuse_eq_ordCompl_two, generalTargetRoot_cleared,
    show 4 ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num]
  exact Nat.ordCompl_self_pow_mul (3 * r + 1) (2 * k) Nat.prime_two

theorem exists_large_nonreturning_predecessor_in_residue
    {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a)
    (q X : ℕ) (y : Fin (3 ^ q)) :
    ∃ R : ℕ, X < R ∧ Odd R ∧ Erdos1135Predecessor.Reaches R a ∧ R % 3 ^ q = y ∧
      ∀ k : ℕ, 0 < k → (Tao.syracuse^[k]) R ≠ R := by
  obtain ⟨r, e, he, hstart⟩ := exists_generalTargetRoot_start ha hthree
  obtain ⟨B, hB⟩ := exists_bound_predecessor_no_return Tao.syracuse (Tao.syracuse r)
  obtain ⟨m, hm⟩ := generalTargetRoot_residue_surjective r q y
  let k := (m : ℕ) + (max B X + 1) * 3 ^ q
  have hk : max B X < k := by
    have hq : 1 ≤ 3 ^ q := by
      have hp : 0 < 3 ^ q := by positivity
      omega
    have h := Nat.mul_le_mul_left (max B X + 1) hq
    dsimp only [k]
    omega
  have hR := hk.trans_le (generalTargetRoot_ge_index r k)
  have hmod := generalTargetRoot_modEq_of_period r q m (max B X + 1)
  change ndGeneralTargetRoot r m % 3 ^ q = ndGeneralTargetRoot r k % 3 ^ q at hmod
  have hy : ndGeneralTargetRoot r k % 3 ^ q = y :=
    hmod.symm.trans (congrArg Fin.val hm)
  refine ⟨ndGeneralTargetRoot r k, (le_max_right B X).trans_lt hR,
    generalTargetRoot_odd r k (by omega), generalTargetRoot_reaches hstart (by omega), hy, ?_⟩
  exact hB _ ((le_max_left B X).trans_lt hR)
    ⟨1, by simpa using generalTargetRoot_syracuse r k⟩

end Erdos1135Predecessor.ND.PositiveDensity
