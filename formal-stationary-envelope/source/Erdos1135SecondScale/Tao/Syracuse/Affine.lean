/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Rational Affine Syracuse Conventions

This module records Tao's tuple-order convention for deterministic affine compositions.  It is a
small rational algebra surface only: no PMFs, finite random variables, Fourier analysis, or
Terras parity-word bridge is introduced here.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Single affine Syracuse branch with positive exponent `a`. -/
noncomputable def taoSingleAff (a : ℕ+) (x : ℚ) : ℚ :=
  ((3 : ℚ) * x + 1) / (2 : ℚ) ^ (a : ℕ)

/-- Total exponent weight of a positive valuation tuple. -/
def taoTupleWeight (as : List ℕ+) : ℕ :=
  (as.map fun a => (a : ℕ)).sum

/--
Tao's offset term for the affine composition ordered as
`Aff_{a_1,...,a_n} = Aff_{a_n} ∘ ... ∘ Aff_{a_1}`.
-/
noncomputable def taoOffsetList : List ℕ+ → ℚ
  | [] => 0
  | a :: as =>
      (3 : ℚ) ^ as.length / (2 : ℚ) ^ taoTupleWeight (a :: as) +
        taoOffsetList as

/-- Affine composition in Tao tuple order. -/
noncomputable def taoAffList : List ℕ+ → ℚ → ℚ
  | [], x => x
  | a :: as, x => taoAffList as (taoSingleAff a x)

/-- Natural valuation list along the first `n` Syracuse iterates. -/
def syracuseValuationNatList : ℕ → ℕ → List ℕ
  | 0, _N => []
  | n + 1, N => syracuseExponent N :: syracuseValuationNatList n (syracuse N)

theorem syracuseValuationNatList_length (n N : ℕ) :
    (syracuseValuationNatList n N).length = n := by
  induction n generalizing N with
  | zero =>
      simp [syracuseValuationNatList]
  | succ n ih =>
      simp [syracuseValuationNatList, ih]

theorem syracuseValuationNatList_forall_pos {n N : ℕ} (hN : Odd N) :
    (syracuseValuationNatList n N).Forall (fun a => 0 < a) := by
  induction n generalizing N with
  | zero =>
      simp [syracuseValuationNatList]
  | succ n ih =>
      simp [syracuseValuationNatList, syracuseExponent_pos_of_odd hN, ih (syracuse_odd N)]

/-- Positive valuation list along the first `n` Syracuse iterates from an odd start. -/
def syracuseValuationPNatList : (n N : ℕ) → Odd N → List ℕ+
  | 0, _N, _hN => []
  | n + 1, N, hN =>
      ⟨syracuseExponent N, syracuseExponent_pos_of_odd hN⟩ ::
        syracuseValuationPNatList n (syracuse N) (syracuse_odd N)

theorem syracuseValuationPNatList_length (n N : ℕ) (hN : Odd N) :
    (syracuseValuationPNatList n N hN).length = n := by
  induction n generalizing N with
  | zero =>
      simp [syracuseValuationPNatList]
  | succ n ih =>
      simp [syracuseValuationPNatList, ih]

theorem syracuseValuationPNatList_map (n N : ℕ) (hN : Odd N) :
    (syracuseValuationPNatList n N hN).map (fun a : ℕ+ => (a : ℕ)) =
      syracuseValuationNatList n N := by
  induction n generalizing N with
  | zero =>
      simp [syracuseValuationPNatList, syracuseValuationNatList]
  | succ n ih =>
      simp [syracuseValuationPNatList, syracuseValuationNatList, ih]

@[simp]
theorem taoOffsetList_nil : taoOffsetList [] = 0 :=
  rfl

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

theorem taoOffsetList_single (a : ℕ+) :
    taoOffsetList [a] = 1 / (2 : ℚ) ^ (a : ℕ) := by
  simp [taoOffsetList, taoTupleWeight]

theorem taoOffsetList_pair (a b : ℕ+) :
    taoOffsetList [a, b] =
      (3 : ℚ) / (2 : ℚ) ^ ((a : ℕ) + (b : ℕ)) +
        1 / (2 : ℚ) ^ (b : ℕ) := by
  simp [taoOffsetList, taoTupleWeight]

theorem taoAffList_one_four_three :
    taoAffList [(1 : ℕ+), (4 : ℕ+)] (3 : ℚ) = 1 := by
  norm_num [taoAffList, taoSingleAff]

theorem taoAffList_four_one_three :
    taoAffList [(4 : ℕ+), (1 : ℕ+)] (3 : ℚ) = (23 : ℚ) / 16 := by
  norm_num [taoAffList, taoSingleAff]

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
end Erdos1135SecondScale
