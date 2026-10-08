/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.Affine

/-!
# Coarse Syracuse Affine Envelope

This proof leaf bounds Tao's rational affine offset without changing the
widely imported affine-definition module.  It preserves the denominator gain
needed by the later Section 5 deterministic descent argument.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Tao's rational affine offset is nonnegative. -/
theorem taoOffsetList_nonneg (as : List ℕ+) :
    0 ≤ taoOffsetList as := by
  induction as with
  | nil => simp [taoOffsetList]
  | cons a as ih =>
      rw [taoOffsetList]
      exact add_nonneg
        (div_nonneg (pow_nonneg (by norm_num) _)
          (pow_nonneg (by norm_num) _)) ih

/-- A coarse denominator-free envelope for Tao's affine offset. -/
theorem taoOffsetList_le_three_pow_length (as : List ℕ+) :
    taoOffsetList as ≤ (3 : ℚ) ^ as.length := by
  induction as with
  | nil => simp [taoOffsetList]
  | cons a as ih =>
      have hhead :
          (3 : ℚ) ^ as.length /
              (2 : ℚ) ^ taoTupleWeight (a :: as) ≤
            (3 : ℚ) ^ as.length :=
        div_le_self (pow_nonneg (by norm_num) _)
          (one_le_pow₀ (by norm_num))
      calc
        taoOffsetList (a :: as) =
            (3 : ℚ) ^ as.length /
                (2 : ℚ) ^ taoTupleWeight (a :: as) + taoOffsetList as := rfl
        _ ≤ (3 : ℚ) ^ as.length + (3 : ℚ) ^ as.length :=
          add_le_add hhead ih
        _ ≤ (3 : ℚ) ^ (a :: as).length := by
          rw [List.length_cons, pow_succ]
          have hp : 0 ≤ (3 : ℚ) ^ as.length := pow_nonneg (by norm_num) _
          nlinarith

/-- The exact affine formula with its offset replaced by the coarse
denominator-free envelope. -/
theorem syracuse_iterate_le_affine_envelope
    (n N : ℕ) (hN : Odd N) :
    ((syracuse^[n]) N : ℚ) ≤
      (3 : ℚ) ^ n /
          (2 : ℚ) ^ taoTupleWeight (syracuseValuationPNatList n N hN) * N +
        (3 : ℚ) ^ n := by
  let as := syracuseValuationPNatList n N hN
  have hlength : as.length = n := by
    simpa only [as] using syracuseValuationPNatList_length n N hN
  have hiterate :
      ((syracuse^[n]) N : ℚ) = taoAffList as N := by
    simpa only [as] using syracuse_iterate_eq_taoAffList n N hN
  let mainTerm : ℚ :=
    (3 : ℚ) ^ as.length / (2 : ℚ) ^ taoTupleWeight as * N
  have hclosed : taoAffList as N = mainTerm + taoOffsetList as := by
    simpa only [mainTerm] using taoAffList_closed as (N : ℚ)
  have hoffset : taoOffsetList as ≤ (3 : ℚ) ^ as.length :=
    taoOffsetList_le_three_pow_length as
  have hreplace :
      mainTerm + taoOffsetList as ≤ mainTerm + (3 : ℚ) ^ as.length :=
    add_le_add_right hoffset mainTerm
  calc
    ((syracuse^[n]) N : ℚ) = taoAffList as N := hiterate
    _ = mainTerm + taoOffsetList as := hclosed
    _ ≤ mainTerm + (3 : ℚ) ^ as.length := hreplace
    _ = (3 : ℚ) ^ n /
          (2 : ℚ) ^ taoTupleWeight (syracuseValuationPNatList n N hN) * N +
        (3 : ℚ) ^ n := by
      simp only [mainTerm, as, hlength]

end Tao
end Erdos1135SecondScale
