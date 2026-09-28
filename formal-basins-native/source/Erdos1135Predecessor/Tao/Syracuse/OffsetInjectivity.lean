/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.Affine
import Mathlib.Data.Nat.Factorization.Basic

namespace Erdos1135Predecessor

namespace Tao

def taoOffsetNum : List ℕ+ → ℕ
  | [] => 0
  | a :: as => 3 ^ as.length + 2 ^ (a : ℕ) * taoOffsetNum as

theorem taoOffsetNum_odd_cons (a : ℕ+) (as : List ℕ+) :
    Odd (taoOffsetNum (a :: as)) := by
  have h3 : Odd (3 ^ as.length) := Odd.pow (by norm_num : Odd 3)
  have h2 : Even (2 ^ (a : ℕ) * taoOffsetNum as) := by
    have ha : 0 < (a : ℕ) := a.2
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha) with ⟨k, hk⟩
    refine ⟨2 ^ k * taoOffsetNum as, ?_⟩
    rw [hk, pow_succ, Nat.mul_assoc]
    ring_nf
  simpa [taoOffsetNum] using h3.add_even h2

theorem taoOffsetList_eq_num_div (as : List ℕ+) :
    taoOffsetList as =
      (taoOffsetNum as : ℚ) / (2 : ℚ) ^ taoTupleWeight as := by
  induction as with
  | nil =>
      simp [taoOffsetList, taoOffsetNum, taoTupleWeight]
  | cons a as ih =>
      simp [taoOffsetList, taoOffsetNum, taoTupleWeight, ih, pow_add]
      field_simp [pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)]

theorem pow_weight_mul_taoOffsetList_eq_num (as : List ℕ+) :
    (2 : ℚ) ^ taoTupleWeight as * taoOffsetList as = taoOffsetNum as := by
  rw [taoOffsetList_eq_num_div]
  field_simp [pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)]

theorem factorization_two_pow_mul_odd {a m : ℕ} (hm : Odd m) :
    (2 ^ a * m).factorization 2 = a := by
  have hm_ne : m ≠ 0 := by
    exact Nat.ne_of_gt hm.pos
  have hpow_ne : 2 ^ a ≠ 0 := by
    exact pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)
  have hnot_dvd : ¬ 2 ∣ m := by
    simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hm)
  have hmfac : m.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot_dvd
  rw [Nat.factorization_mul hpow_ne hm_ne]
  rw [Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2)]
  simp [hmfac]

theorem two_pow_mul_odd_cancel {a b m n : ℕ}
    (hm : Odd m) (hn : Odd n) (h : 2 ^ a * m = 2 ^ b * n) :
    a = b ∧ m = n := by
  have ha_eq : a = b := by
    calc
      a = (2 ^ a * m).factorization 2 := by
        rw [factorization_two_pow_mul_odd hm]
      _ = (2 ^ b * n).factorization 2 := by rw [h]
      _ = b := by
        rw [factorization_two_pow_mul_odd hn]
  refine ⟨ha_eq, ?_⟩
  subst b
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < (2 : ℕ)) a) h

theorem taoOffsetNum_injective_of_length_weight {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (hweight : taoTupleWeight as = taoTupleWeight bs)
    (hnum : taoOffsetNum as = taoOffsetNum bs) :
    as = bs := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs =>
          simp at hlen
  | cons a as ih =>
      cases bs with
      | nil =>
          simp at hlen
      | cons b bs =>
          have htail_len : as.length = bs.length := Nat.succ.inj hlen
          have hnum_expanded :
              3 ^ as.length + 2 ^ (a : ℕ) * taoOffsetNum as =
                3 ^ bs.length + 2 ^ (b : ℕ) * taoOffsetNum bs := by
            simpa [taoOffsetNum] using hnum
          have hmul :
              2 ^ (a : ℕ) * taoOffsetNum as =
                2 ^ (b : ℕ) * taoOffsetNum bs := by
            have hsame :
                3 ^ as.length + 2 ^ (a : ℕ) * taoOffsetNum as =
                  3 ^ as.length + 2 ^ (b : ℕ) * taoOffsetNum bs := by
              simpa [htail_len] using hnum_expanded
            exact Nat.add_left_cancel_iff.mp hsame
          cases as with
          | nil =>
              cases bs with
              | nil =>
                  have hab_nat : (a : ℕ) = (b : ℕ) := by
                    simpa [taoTupleWeight] using hweight
                  exact congrArg (fun x : ℕ+ => [x]) (Subtype.ext hab_nat)
              | cons b' bs' =>
                  simp at htail_len
          | cons a' as' =>
              cases bs with
              | nil =>
                  simp at htail_len
              | cons b' bs' =>
                  rcases two_pow_mul_odd_cancel
                      (taoOffsetNum_odd_cons a' as')
                      (taoOffsetNum_odd_cons b' bs') hmul with
                    ⟨hab_nat, htail_num⟩
                  have htail_weight :
                      taoTupleWeight (a' :: as') = taoTupleWeight (b' :: bs') := by
                    simpa [taoTupleWeight, hab_nat] using hweight
                  have htail_eq :
                      a' :: as' = b' :: bs' :=
                    ih (bs := b' :: bs') htail_len htail_weight htail_num
                  have hab : a = b := Subtype.ext hab_nat
                  simp [hab, htail_eq]

theorem taoOffsetList_injective_of_length {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (h : taoOffsetList as = taoOffsetList bs) :
    as = bs := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs =>
          simp at hlen
  | cons a as ih =>
      cases bs with
      | nil =>
          simp at hlen
      | cons b bs =>
          have hdiv :
              (taoOffsetNum (a :: as) : ℚ) /
                  (2 : ℚ) ^ taoTupleWeight (a :: as) =
                (taoOffsetNum (b :: bs) : ℚ) /
                  (2 : ℚ) ^ taoTupleWeight (b :: bs) := by
            simpa [taoOffsetList_eq_num_div] using h
          have hcrossQ :
              (taoOffsetNum (a :: as) : ℚ) *
                  (2 : ℚ) ^ taoTupleWeight (b :: bs) =
                (taoOffsetNum (b :: bs) : ℚ) *
                  (2 : ℚ) ^ taoTupleWeight (a :: as) := by
            have hden_a :
                (2 : ℚ) ^ taoTupleWeight (a :: as) ≠ 0 :=
              pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)
            have hden_b :
                (2 : ℚ) ^ taoTupleWeight (b :: bs) ≠ 0 :=
              pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)
            field_simp [hden_a, hden_b] at hdiv
            simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
          have hcrossNat :
              taoOffsetNum (a :: as) * 2 ^ taoTupleWeight (b :: bs) =
                taoOffsetNum (b :: bs) * 2 ^ taoTupleWeight (a :: as) := by
            exact_mod_cast hcrossQ
          have hpowCross :
              2 ^ taoTupleWeight (b :: bs) * taoOffsetNum (a :: as) =
                2 ^ taoTupleWeight (a :: as) * taoOffsetNum (b :: bs) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcrossNat
          rcases two_pow_mul_odd_cancel
              (taoOffsetNum_odd_cons a as)
              (taoOffsetNum_odd_cons b bs) hpowCross with
            ⟨hweight_sym, hnum⟩
          exact taoOffsetNum_injective_of_length_weight hlen hweight_sym.symm hnum

theorem taoLemma62_offset_injective {as bs : List ℕ+}
    (hlen : as.length = bs.length)
    (h : taoOffsetList as = taoOffsetList bs) :
    as = bs :=
  taoOffsetList_injective_of_length hlen h

end Tao

end Erdos1135Predecessor
