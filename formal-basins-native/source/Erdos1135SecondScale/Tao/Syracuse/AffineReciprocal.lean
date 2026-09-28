/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.OddSource
import Erdos1135SecondScale.Tao.Syracuse.ValuationDistribution

/-!
# Exact Affine Reciprocals

This neutral leaf rewrites the reciprocal of an odd affine source using the
exact affine denominator.  It has no scheduling, source-window, residue, or
Section 5 hypotheses.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The exact affine denominator is positive, and the one geometric list mass
is precisely the reciprocal source factor. -/
theorem taoAffList_denominator_pos_and_reciprocal
    {q M : ℕ} {as : List ℕ+} {N : TaoOddNat}
    (hlen : as.length = q)
    (hAff : taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    0 < (M : ℝ) - (taoOffsetList as : ℝ) ∧
      (1 : ℝ) / (N.1 : ℝ) =
        ((3 : ℝ) ^ q * geom2PNatListMass as) /
          ((M : ℝ) - (taoOffsetList as : ℝ)) := by
  have hclosedQ :
      (M : ℚ) =
        (3 : ℚ) ^ as.length / (2 : ℚ) ^ taoTupleWeight as * (N.1 : ℚ) +
          taoOffsetList as :=
    hAff.symm.trans (taoAffList_closed as (N.1 : ℚ))
  have hclosedR := congrArg (fun x : ℚ => (x : ℝ)) hclosedQ
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat] at hclosedR
  have hdenEq :
      (M : ℝ) - (taoOffsetList as : ℝ) =
        (3 : ℝ) ^ q / (2 : ℝ) ^ taoTupleWeight as * (N.1 : ℝ) := by
    rw [hlen] at hclosedR
    linarith
  have hNpos : 0 < (N.1 : ℝ) := by
    exact_mod_cast Odd.pos N.2
  have hdenPos : 0 < (M : ℝ) - (taoOffsetList as : ℝ) := by
    rw [hdenEq]
    exact mul_pos (div_pos (by positivity) (by positivity)) hNpos
  refine ⟨hdenPos, ?_⟩
  rw [geom2PNatListMass_eq_inv_pow]
  rw [eq_div_iff hdenPos.ne', hdenEq]
  field_simp [hNpos.ne', pow_ne_zero]

/-- Positivity projection of the exact affine reciprocal packet. -/
theorem taoAffList_denominator_pos
    {q M : ℕ} {as : List ℕ+} {N : TaoOddNat}
    (hlen : as.length = q)
    (hAff : taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    0 < (M : ℝ) - (taoOffsetList as : ℝ) :=
  (taoAffList_denominator_pos_and_reciprocal hlen hAff).1

/-- Reciprocal projection of the exact affine reciprocal packet. -/
theorem taoAffList_reciprocal
    {q M : ℕ} {as : List ℕ+} {N : TaoOddNat}
    (hlen : as.length = q)
    (hAff : taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    (1 : ℝ) / (N.1 : ℝ) =
      ((3 : ℝ) ^ q * geom2PNatListMass as) /
        ((M : ℝ) - (taoOffsetList as : ℝ)) :=
  (taoAffList_denominator_pos_and_reciprocal hlen hAff).2

end

end Tao
end Erdos1135SecondScale
