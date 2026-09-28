/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.CollatzStep
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Probability.Truncation
import Erdos1135Predecessor.Tao.Syracuse.ParityBridge
import Erdos1135Predecessor.Terras.Core.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn

namespace Erdos1135Predecessor

namespace Tao

noncomputable def geom2PNatListMass (as : List ℕ+) : ℝ :=
  (as.map fun a => (geom2PNat a).toReal).prod

theorem one_div_two_pow_eq_inv_pow (n : ℕ) :
    (1 / 2 : ℝ) ^ n = (1 : ℝ) / (2 ^ n : ℝ) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      field_simp [pow_ne_zero]

theorem geom2PNatListMass_eq_pow (as : List ℕ+) :
    geom2PNatListMass as = (1 / 2 : ℝ) ^ taoTupleWeight as := by
  induction as with
  | nil =>
      simp [geom2PNatListMass, taoTupleWeight]
  | cons a as ih =>
      rw [geom2PNatListMass] at ih
      simp [taoTupleWeight, geom2PNat_apply_toReal] at ih
      simp [geom2PNatListMass, taoTupleWeight, geom2PNat_apply_toReal, ih, pow_add]

theorem geom2PNatListMass_eq_inv_pow (as : List ℕ+) :
    geom2PNatListMass as = (1 : ℝ) / (2 ^ taoTupleWeight as : ℝ) := by
  rw [geom2PNatListMass_eq_pow, one_div_two_pow_eq_inv_pow]

noncomputable def geom2PNatListPMF : ℕ → PMF (List ℕ+)
  | 0 => PMF.pure []
  | n + 1 => geom2PNat.bind fun a =>
      (geom2PNatListPMF n).map fun as => a :: as

theorem geom2PNatListPMF_succ_apply_cons (n : ℕ) (a : ℕ+) (as : List ℕ+) :
    geom2PNatListPMF (n + 1) (a :: as) =
      geom2PNat a * geom2PNatListPMF n as := by
  classical
  rw [geom2PNatListPMF, PMF.bind_apply]
  have hmap : ∀ a' : ℕ+,
      ((geom2PNatListPMF n).map fun bs => a' :: bs) (a :: as) =
        if a = a' then geom2PNatListPMF n as else 0 := by
    intro a'
    rw [PMF.map_apply]
    by_cases h : a = a'
    · subst h
      rw [tsum_eq_single as]
      · simp
      · intro bs hbs
        have hc : ¬ a :: as = a :: bs := by
          intro hcons
          exact hbs (List.cons.inj hcons).2.symm
        simp [hc]
    · have hnone : ∀ bs : List ℕ+, ¬ a :: as = a' :: bs := by
        intro bs hcons
        exact h (List.cons.inj hcons).1
      simp [h, hnone]
  calc
    (∑' a' : ℕ+,
        geom2PNat a' * ((geom2PNatListPMF n).map fun bs => a' :: bs) (a :: as))
        = ∑' a' : ℕ+,
            geom2PNat a' * (if a = a' then geom2PNatListPMF n as else 0) := by
          apply tsum_congr
          intro a'
          rw [hmap a']
    _ = geom2PNat a * geom2PNatListPMF n as := by
          rw [tsum_eq_single a]
          · simp
          · intro a' ha'
            simp [ha'.symm]

theorem geom2PNatListPMF_apply_length_toReal (as : List ℕ+) :
    (geom2PNatListPMF as.length as).toReal = geom2PNatListMass as := by
  induction as with
  | nil =>
      simp [geom2PNatListPMF, geom2PNatListMass]
  | cons a as ih =>
      rw [List.length_cons, geom2PNatListPMF_succ_apply_cons]
      rw [ENNReal.toReal_mul, ih]
      simp [geom2PNatListMass]

theorem geom2PNatListPMF_apply_length_toReal_eq_weight (as : List ℕ+) :
    (geom2PNatListPMF as.length as).toReal =
      (1 / 2 : ℝ) ^ taoTupleWeight as := by
  rw [geom2PNatListPMF_apply_length_toReal, geom2PNatListMass_eq_pow]

theorem geom2PNatListPMF_succ_apply_nil (n : ℕ) :
    geom2PNatListPMF (n + 1) [] = 0 := by
  classical
  rw [geom2PNatListPMF, PMF.bind_apply]
  simp [PMF.map_apply]

theorem geom2PNatListPMF_apply_eq_zero_of_length_ne
    (n : ℕ) (as : List ℕ+) (h : as.length ≠ n) :
    geom2PNatListPMF n as = 0 := by
  induction n generalizing as with
  | zero =>
      cases as with
      | nil => exact (h rfl).elim
      | cons a as => simp [geom2PNatListPMF]
  | succ n ih =>
      cases as with
      | nil =>
          exact geom2PNatListPMF_succ_apply_nil n
      | cons a as =>
          rw [geom2PNatListPMF_succ_apply_cons]
          have htail : as.length ≠ n := by
            intro hs
            exact h (by simp [hs])
          rw [ih as htail, mul_zero]

theorem geom2PNatListPMF_support_length_eq
    {n : ℕ} {as : List ℕ+}
    (has : as ∈ (geom2PNatListPMF n).support) :
    as.length = n := by
  by_contra hlength
  have hnonzero : geom2PNatListPMF n as ≠ 0 :=
    ((geom2PNatListPMF n).mem_support_iff as).mp has
  exact hnonzero
    (geom2PNatListPMF_apply_eq_zero_of_length_ne n as hlength)

end Tao

end Erdos1135Predecessor
