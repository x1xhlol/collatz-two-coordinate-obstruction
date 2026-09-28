/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Lemmas

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoSingleAff (a : ℕ+) (x : ℚ) : ℚ :=
  ((3 : ℚ) * x + 1) / (2 : ℚ) ^ (a : ℕ)

def taoTupleWeight (as : List ℕ+) : ℕ :=
  (as.map fun a => (a : ℕ)).sum

noncomputable def taoOffsetList : List ℕ+ → ℚ
  | [] => 0
  | a :: as =>
      (3 : ℚ) ^ as.length / (2 : ℚ) ^ taoTupleWeight (a :: as) +
        taoOffsetList as

noncomputable def taoAffList : List ℕ+ → ℚ → ℚ
  | [], x => x
  | a :: as, x => taoAffList as (taoSingleAff a x)

def syracuseValuationPNatList : (n N : ℕ) → Odd N → List ℕ+
  | 0, _N, _hN => []
  | n + 1, N, hN =>
      ⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩ ::
        syracuseValuationPNatList n (syracuse N) (syracuse_odd N)

theorem taoAffList_closed (as : List ℕ+) (x : ℚ) :
    taoAffList as x =
      (3 : ℚ) ^ as.length / (2 : ℚ) ^ taoTupleWeight as * x +
        taoOffsetList as := by
  induction as generalizing x with
  | nil =>
      simp [taoAffList, taoTupleWeight, taoOffsetList]
  | cons a as ih =>
      simp [taoAffList, taoSingleAff, taoTupleWeight, taoOffsetList, ih]
      ring_nf

theorem syracuse_one_step_eq_taoSingleAff {N : ℕ} (hN : Odd N) :
    (syracuse N : ℚ) =
      taoSingleAff ⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩ (N : ℚ) := by
  unfold syracuse Terras.oddOnly syracuseExponent Terras.twoAdicExponent taoSingleAff
  rw [Nat.cast_div_charZero (Nat.ordProj_dvd (3 * N + 1) 2)]
  norm_num

theorem syracuse_iterate_eq_taoAffList (n N : ℕ) (hN : Odd N) :
    ((syracuse^[n]) N : ℚ) = taoAffList (syracuseValuationPNatList n N hN) (N : ℚ) := by
  induction n generalizing N with
  | zero =>
      simp [syracuseValuationPNatList, taoAffList]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp [syracuseValuationPNatList, taoAffList]
      rw [← syracuse_one_step_eq_taoSingleAff hN]
      exact ih (syracuse N) (syracuse_odd N)

end Tao

end Erdos1135Predecessor
