import Erdos1135.Residues
import Erdos1135.Terras.Parity.Word
import Erdos1135.TwoAdic
import Mathlib.Data.Fintype.EquivFin

/-!
# Terras/Everett Parity Residues

This module starts the residue-class layer for the accelerated parity-prefix route.  The first
checked endpoint is the length-one equivalence between parity prefixes and congruence modulo `2`.
-/

namespace Erdos1135
namespace Terras

lemma parityBit_eq_of_modEq_two {m n : ℕ} (h : Nat.ModEq 2 m n) :
    parityBit m = parityBit n := by
  unfold Nat.ModEq at h
  by_cases hm : Even m
  · have hm0 : m % 2 = 0 := Nat.even_iff.mp hm
    have hn0 : n % 2 = 0 := by
      rw [← h, hm0]
    have hn : Even n := Nat.even_iff.mpr hn0
    simp [parityBit, hm, hn]
  · have hm1 : m % 2 = 1 := Nat.not_even_iff.mp hm
    have hn1 : n % 2 = 1 := by
      rw [← h, hm1]
    have hn : ¬ Even n := Nat.not_even_iff.mpr hn1
    simp [parityBit, hm, hn]

lemma modEq_two_of_parityBit_eq {m n : ℕ} (h : parityBit m = parityBit n) :
    Nat.ModEq 2 m n := by
  unfold Nat.ModEq
  by_cases hm : Even m <;> by_cases hn : Even n
  · rw [Nat.even_iff.mp hm, Nat.even_iff.mp hn]
  · have hfalse : False := by
      simp [parityBit, hm, hn] at h
    exact hfalse.elim
  · have hfalse : False := by
      simp [parityBit, hm, hn] at h
    exact hfalse.elim
  · rw [Nat.not_even_iff.mp hm, Nat.not_even_iff.mp hn]

theorem same_parityPrefix_one_iff_modEq_two (m n : ℕ) :
    parityPrefix 1 m = parityPrefix 1 n ↔ Nat.ModEq 2 m n := by
  constructor
  · intro h
    apply modEq_two_of_parityBit_eq
    have happ := congrFun h (0 : Fin 1)
    simpa [parityPrefix] using happ
  · intro h
    funext i
    fin_cases i
    simpa [parityPrefix] using parityBit_eq_of_modEq_two h

lemma accelerated_modEq_of_modEq_twoPow_succ {k m n : ℕ}
    (h : Nat.ModEq (2 ^ (k + 1)) m n) :
    Nat.ModEq (2 ^ k) (accelerated m) (accelerated n) := by
  have hmod2 : Nat.ModEq 2 m n :=
    Nat.ModEq.of_dvd (two_dvd_two_pow_succ k) h
  have hbit : parityBit m = parityBit n :=
    parityBit_eq_of_modEq_two hmod2
  have hmod_two_mul : Nat.ModEq (2 * 2 ^ k) m n := by
    simpa [two_pow_succ_two_mul k] using h
  by_cases hm : Even m
  · have hmbit : parityBit m = false :=
      (parityBit_eq_false_iff_even m).mpr hm
    have hnbit : parityBit n = false := by
      rw [← hbit, hmbit]
    have hn : Even n :=
      (parityBit_eq_false_iff_even n).mp hnbit
    rw [accelerated_eq_div_two_of_even hm, accelerated_eq_div_two_of_even hn]
    exact nat_modEq_div_two_of_modEq_mul_two_of_two_dvd (Even.two_dvd hm)
      (Even.two_dvd hn) hmod_two_mul
  · have hmbit : parityBit m = true :=
      (parityBit_eq_true_iff_not_even m).mpr hm
    have hnbit : parityBit n = true := by
      rw [← hbit, hmbit]
    have hn : ¬ Even n :=
      (parityBit_eq_true_iff_not_even n).mp hnbit
    have hmnum_even : Even (3 * m + 1) := by
      rcases Nat.not_even_iff_odd.mp hm with ⟨a, ha⟩
      refine ⟨3 * a + 2, ?_⟩
      omega
    have hnnum_even : Even (3 * n + 1) := by
      rcases Nat.not_even_iff_odd.mp hn with ⟨a, ha⟩
      refine ⟨3 * a + 2, ?_⟩
      omega
    rw [accelerated_eq_three_mul_add_one_div_two_of_not_even hm,
      accelerated_eq_three_mul_add_one_div_two_of_not_even hn]
    exact nat_modEq_div_two_of_modEq_mul_two_of_two_dvd (Even.two_dvd hmnum_even)
      (Even.two_dvd hnnum_even) (nat_modEq_three_mul_add_one hmod_two_mul)

theorem parityPrefixList_eq_of_modEq_twoPow :
    ∀ (k : ℕ) {m n : ℕ}, Nat.ModEq (2 ^ k) m n →
      parityPrefixList k m = parityPrefixList k n
  | 0, _, _, _ => rfl
  | k + 1, m, n, h => by
      have hmod2 : Nat.ModEq 2 m n :=
        Nat.ModEq.of_dvd (two_dvd_two_pow_succ k) h
      have hbit : parityBit m = parityBit n :=
        parityBit_eq_of_modEq_two hmod2
      have htail : parityPrefixList k (accelerated m) =
          parityPrefixList k (accelerated n) :=
        parityPrefixList_eq_of_modEq_twoPow k
          (accelerated_modEq_of_modEq_twoPow_succ h)
      simp [parityPrefixList, hbit, htail]

theorem parityPrefix_eq_of_modEq_twoPow {k m n : ℕ}
    (h : Nat.ModEq (2 ^ k) m n) :
    parityPrefix k m = parityPrefix k n := by
  exact List.ofFn_injective (by
    change parityWordToList (parityPrefix k m) = parityWordToList (parityPrefix k n)
    rw [parityWordToList_parityPrefix_eq_parityPrefixList k m,
      parityWordToList_parityPrefix_eq_parityPrefixList k n]
    exact parityPrefixList_eq_of_modEq_twoPow k h)

/-- On a fixed length-`q` parity prefix, the accelerated iterate has the exact affine tail
coefficient `3 ^ numOdd w` along the residue class modulo `2 ^ q`. -/
theorem accelerated_iterate_add_two_pow_mul_of_prefix
    {q u t : ℕ} {w : ParityWord q}
    (hprefix : parityPrefix q u = w) :
    accelerated^[q] (u + 2 ^ q * t) =
      accelerated^[q] u + 3 ^ numOdd w * t := by
  have hmod : u + 2 ^ q * t ≡ u [MOD 2 ^ q] := by
    rw [Nat.ModEq]
    exact Nat.add_mul_mod_self_left u (2 ^ q) t
  have hprefix' : parityPrefix q (u + 2 ^ q * t) = w := by
    rw [parityPrefix_eq_of_modEq_twoPow hmod, hprefix]
  have hbig := iterate_affine_of_parityPrefix hprefix'
  have hsmall := iterate_affine_of_parityPrefix hprefix
  have hmul :
      (2 : ℤ) ^ q * (accelerated^[q] (u + 2 ^ q * t) : ℤ) =
        (2 : ℤ) ^ q * (accelerated^[q] u + 3 ^ numOdd w * t : ℕ) := by
    rw [hbig]
    calc
      (3 : ℤ) ^ numOdd w * ↑(u + 2 ^ q * t) + branchConst w =
          ((3 : ℤ) ^ numOdd w * ↑u + branchConst w) +
            (2 : ℤ) ^ q * ((3 : ℤ) ^ numOdd w * ↑t) := by
        norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
        ring
      _ = (2 : ℤ) ^ q * ↑(accelerated^[q] u) +
            (2 : ℤ) ^ q * ((3 : ℤ) ^ numOdd w * ↑t) := by
        rw [← hsmall]
      _ = (2 : ℤ) ^ q * ↑(accelerated^[q] u + 3 ^ numOdd w * t) := by
        norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
        ring
  have hpow_ne : (2 : ℤ) ^ q ≠ 0 :=
    pow_ne_zero q (by decide : (2 : ℤ) ≠ 0)
  exact_mod_cast (mul_left_cancel₀ hpow_ne hmul)

lemma modEq_twoPow_succ_of_parityBit_eq_of_accelerated_modEq {k m n : ℕ}
    (hbit : parityBit m = parityBit n)
    (hacc : Nat.ModEq (2 ^ k) (accelerated m) (accelerated n)) :
    Nat.ModEq (2 ^ (k + 1)) m n := by
  have hacc_scaled : Nat.ModEq (2 * 2 ^ k) (2 * accelerated m) (2 * accelerated n) :=
    nat_modEq_mul_left_modulus (a := 2) hacc
  by_cases hm : Even m
  · have hmbit : parityBit m = false :=
      (parityBit_eq_false_iff_even m).mpr hm
    have hnbit : parityBit n = false := by
      rw [← hbit, hmbit]
    have hn : Even n :=
      (parityBit_eq_false_iff_even n).mp hnbit
    have hmn : Nat.ModEq (2 * 2 ^ k) m n := by
      simpa [two_mul_accelerated_eq_of_even hm, two_mul_accelerated_eq_of_even hn] using
        hacc_scaled
    simpa [two_pow_succ_two_mul k] using hmn
  · have hmbit : parityBit m = true :=
      (parityBit_eq_true_iff_not_even m).mpr hm
    have hnbit : parityBit n = true := by
      rw [← hbit, hmbit]
    have hn : ¬ Even n :=
      (parityBit_eq_true_iff_not_even n).mp hnbit
    have hthree_add :
        Nat.ModEq (2 * 2 ^ k) (3 * m + 1) (3 * n + 1) := by
      simpa [two_mul_accelerated_eq_of_not_even hm, two_mul_accelerated_eq_of_not_even hn] using
        hacc_scaled
    have hthree_sub :
        Nat.ModEq (2 * 2 ^ k) ((3 * m + 1) - 1) ((3 * n + 1) - 1) :=
      Nat.ModEq.sub (by omega) (by omega) hthree_add (Nat.ModEq.refl 1)
    have hthree : Nat.ModEq (2 * 2 ^ k) (3 * m) (3 * n) := by
      simpa using hthree_sub
    have hgcd : Nat.gcd (2 * 2 ^ k) 3 = 1 := by
      have hcop : Nat.Coprime (2 * 2 ^ k) 3 := by
        rw [← two_pow_succ_two_mul k]
        exact Nat.Coprime.pow_left (k + 1) (by decide : Nat.Coprime 2 3)
      exact hcop.gcd_eq_one
    have hmn : Nat.ModEq (2 * 2 ^ k) m n :=
      Nat.ModEq.cancel_left_of_coprime hgcd hthree
    simpa [two_pow_succ_two_mul k] using hmn

theorem modEq_twoPow_of_parityPrefixList_eq :
    ∀ (k : ℕ) {m n : ℕ}, parityPrefixList k m = parityPrefixList k n →
      Nat.ModEq (2 ^ k) m n
  | 0, _, _, _ => by
      change _ % 1 = _ % 1
      rw [Nat.mod_one, Nat.mod_one]
  | k + 1, m, n, h => by
      have hbit : parityBit m = parityBit n := by
        simpa [parityPrefixList] using congrArg List.head? h
      have htail : parityPrefixList k (accelerated m) =
          parityPrefixList k (accelerated n) := by
        simpa [parityPrefixList] using congrArg List.tail h
      exact modEq_twoPow_succ_of_parityBit_eq_of_accelerated_modEq hbit
        (modEq_twoPow_of_parityPrefixList_eq k htail)

theorem modEq_twoPow_of_parityPrefix_eq {k m n : ℕ}
    (h : parityPrefix k m = parityPrefix k n) :
    Nat.ModEq (2 ^ k) m n := by
  apply modEq_twoPow_of_parityPrefixList_eq k
  have hlist := congrArg parityWordToList h
  simpa [parityWordToList_parityPrefix_eq_parityPrefixList k m,
    parityWordToList_parityPrefix_eq_parityPrefixList k n] using hlist

theorem same_parityPrefix_iff_modEq_pow_two (k m n : ℕ) :
    parityPrefix k m = parityPrefix k n ↔ Nat.ModEq (2 ^ k) m n :=
  ⟨modEq_twoPow_of_parityPrefix_eq, parityPrefix_eq_of_modEq_twoPow⟩

/-- The parity prefix attached to a residue class, using the canonical natural representative. -/
def parityPrefixOfResidue (k : ℕ) (r : ZMod (2 ^ k)) : ParityWord k :=
  parityPrefix k r.val

lemma parityPrefixOfResidue_injective (k : ℕ) :
    Function.Injective (parityPrefixOfResidue k) := by
  intro r s h
  haveI : NeZero (2 ^ k) := ⟨two_pow_ne_zero k⟩
  have hmod : Nat.ModEq (2 ^ k) r.val s.val :=
    modEq_twoPow_of_parityPrefix_eq h
  have hcast : (r.val : ZMod (2 ^ k)) = (s.val : ZMod (2 ^ k)) :=
    (ZMod.natCast_eq_natCast_iff r.val s.val (2 ^ k)).mpr hmod
  calc
    r = (r.val : ZMod (2 ^ k)) := (ZMod.natCast_zmod_val r).symm
    _ = (s.val : ZMod (2 ^ k)) := hcast
    _ = s := ZMod.natCast_zmod_val s

lemma parityPrefixOfResidue_bijective (k : ℕ) :
    Function.Bijective (parityPrefixOfResidue k) := by
  classical
  haveI : NeZero (2 ^ k) := ⟨two_pow_ne_zero k⟩
  exact (Fintype.bijective_iff_injective_and_card (parityPrefixOfResidue k)).mpr
    ⟨parityPrefixOfResidue_injective k, by rw [ZMod.card, card_parityWord]⟩

/-- Finite Bernstein-Lagarias-style equivalence between residues mod `2 ^ k` and parity words. -/
noncomputable def parityPrefixZModEquiv (k : ℕ) : ZMod (2 ^ k) ≃ ParityWord k :=
  Equiv.ofBijective (parityPrefixOfResidue k) (parityPrefixOfResidue_bijective k)

/-- A parity word determines a unique residue class modulo `2 ^ k`. -/
noncomputable def parityPrefix_equiv_zmod (k : ℕ) : ParityWord k ≃ ZMod (2 ^ k) :=
  (parityPrefixZModEquiv k).symm

theorem natCast_eq_residue_iff_parityPrefix_eq (k : ℕ) (r : ZMod (2 ^ k)) (n : ℕ) :
    (n : ZMod (2 ^ k)) = r ↔ parityPrefix k n = parityPrefixOfResidue k r := by
  haveI : NeZero (2 ^ k) := ⟨two_pow_ne_zero k⟩
  constructor
  · intro h
    have hcast : (n : ZMod (2 ^ k)) = (r.val : ZMod (2 ^ k)) := by
      simpa [ZMod.natCast_zmod_val r] using h
    have hmod : Nat.ModEq (2 ^ k) n r.val :=
      (ZMod.natCast_eq_natCast_iff n r.val (2 ^ k)).mp hcast
    simpa [parityPrefixOfResidue] using
      (same_parityPrefix_iff_modEq_pow_two k n r.val).mpr hmod
  · intro h
    have hmod : Nat.ModEq (2 ^ k) n r.val :=
      (same_parityPrefix_iff_modEq_pow_two k n r.val).mp (by
        simpa [parityPrefixOfResidue] using h)
    have hcast : (n : ZMod (2 ^ k)) = (r.val : ZMod (2 ^ k)) :=
      (ZMod.natCast_eq_natCast_iff n r.val (2 ^ k)).mpr hmod
    simpa [ZMod.natCast_zmod_val r] using hcast

theorem unique_residue_for_word {k : ℕ} (w : ParityWord k) :
    ∃! r : ZMod (2 ^ k),
      ∀ n : ℕ, (n : ZMod (2 ^ k)) = r ↔ parityPrefix k n = w := by
  classical
  haveI : NeZero (2 ^ k) := ⟨two_pow_ne_zero k⟩
  let r : ZMod (2 ^ k) := parityPrefix_equiv_zmod k w
  have hr : parityPrefixOfResidue k r = w := by
    change parityPrefixZModEquiv k ((parityPrefixZModEquiv k).symm w) = w
    exact (parityPrefixZModEquiv k).apply_symm_apply w
  refine ⟨r, ?_, ?_⟩
  · intro n
    rw [natCast_eq_residue_iff_parityPrefix_eq k r n, hr]
  · intro s hs
    have hsval : (r.val : ZMod (2 ^ k)) = s :=
      (hs r.val).mpr (by simpa [parityPrefixOfResidue] using hr)
    calc
      s = (r.val : ZMod (2 ^ k)) := hsval.symm
      _ = r := ZMod.natCast_zmod_val r

end Terras
end Erdos1135
