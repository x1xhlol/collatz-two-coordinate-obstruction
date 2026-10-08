import UnitSourceAffineForward
import CanonicalSyracuseCylinderLaw

/-!
# Canonical cylinder probabilities and the native Syracuse PMF

The arithmetic geometric-word encoding and the positive-exponent PMF
encoding are identified through their literal affine recursion. The
bridge concerns the existing canonical measure, with no new stationarity
or cylinder-law hypothesis.
-/

set_option autoImplicit false
open scoped BigOperators

namespace CollatzCylinderPacking.Arithmetic

open Erdos1135.Tao

/-- Independent zero-based geometric coordinates on the arithmetic word type. -/
noncomputable def geometricWordPMF : (k : ℕ) → PMF (GeometricWord k)
  | 0 => PMF.pure ()
  | k + 1 => geom2Nat.bind (fun a => (geometricWordPMF k).map (fun w => (a, w)))

theorem geometricWordPMF_succ_apply (k a : ℕ) (w : GeometricWord k) :
    geometricWordPMF (k + 1) (a, w) = geom2Nat a * geometricWordPMF k w := by
  classical
  rw [geometricWordPMF, PMF.bind_apply]
  change (∑' b : ℕ, geom2Nat b *
    (((geometricWordPMF k).map (fun v => (b, v))) (a, w))) = _
  have hmap (b : ℕ) :
      ((geometricWordPMF k).map (fun v => (b, v))) (a, w) =
        if a = b then geometricWordPMF k w else 0 := by
    rw [PMF.map_apply]
    by_cases h : a = b
    · subst b
      simp only [Prod.mk.injEq, true_and]
      rw [tsum_eq_single w]
      · simp
      · intro v hv
        rw [if_neg (Ne.symm hv)]
    · simp [Prod.mk.injEq, h]
  simp only [hmap]
  simp only [mul_ite, mul_zero]
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    simp [Ne.symm hb]

theorem geometricWordPMF_apply_toReal (k : ℕ) (w : GeometricWord k) :
    (geometricWordPMF k w).toReal = (1 / 2 : ℝ) ^ wordLength k w := by
  induction k with
  | zero => cases w; simp [geometricWordPMF, wordLength]
  | succ k ih =>
      rcases w with ⟨a, w⟩
      rw [geometricWordPMF_succ_apply, ENNReal.toReal_mul,
        geom2Nat_apply_toReal, ih]
      simp only [wordLength, pow_add]

theorem wordResidue_succ_eq_syracStep (k a : ℕ) (w : GeometricWord k) :
    wordResidue (k + 1) (a, w) = syracStep k (wordResidue k w) a.succPNat := by
  rw [wordResidue_eq_truncatedSeries]
  change (↑((powerTwoUnit (k + 1) (a + 1))⁻¹) : ZMod (3 ^ (k + 1))) *
      (1 + 3 * truncatedSeries (k + 1) (wordList k w)) = _
  rw [← ZMod.inv_coe_unit, powerTwoUnit_coe]
  have hs := unitSourceAffineOneStep_eq_syracStep k a.succPNat
    (truncatedSeries (k + 1) (wordList k w))
  change ((2 : ZMod (3 ^ (k + 1))) ^ (a + 1))⁻¹ *
      (1 + 3 * truncatedSeries (k + 1) (wordList k w)) = _ at hs
  rw [hs]
  congr 1
  change reduceResidue k (k + 1) (Nat.le_succ k)
      (truncatedSeries (k + 1) (wordList k w)) = wordResidue k w
  rw [reduce_truncatedSeries, wordResidue_eq_truncatedSeries]

/-- Exact equality of the two concrete finite laws, including their encoding
of positive geometric exponents and their composition orientation. -/
theorem geometricWordPMF_map_wordResidue (k : ℕ) :
    (geometricWordPMF k).map (wordResidue k) = syracPMF k := by
  induction k with
  | zero =>
      rw [geometricWordPMF, PMF.pure_map, syracPMF]
      congr 1
  | succ k ih =>
      rw [geometricWordPMF, PMF.map_bind]
      have hstep :
          geom2Nat.bind (fun a =>
            ((geometricWordPMF k).map (fun w => (a, w))).map (wordResidue (k + 1))) =
          geom2PNat.bind (fun a =>
            ((geometricWordPMF k).map (wordResidue k)).map
              (fun y => syracStep k y a)) := by
        rw [geom2PNat, PMF.bind_map]
        apply congrArg (PMF.bind geom2Nat)
        funext a
        simp only [Function.comp_apply]
        change ((geometricWordPMF k).map (fun w => (a, w))).map
            (fun p : ℕ × GeometricWord k => wordResidue (k + 1) p) =
          ((geometricWordPMF k).map (wordResidue k)).map
            (fun y => syracStep k y a.succPNat)
        rw [PMF.map_comp, PMF.map_comp]
        apply congrArg (fun f => (geometricWordPMF k).map f)
        funext w
        exact wordResidue_succ_eq_syracStep k a w
      refine hstep.trans ?_
      rw [ih]
      change geom2PNat.bind (fun a => (syracPMF k).map (fun y => syracStep k y a)) =
        (syracPMF k).bind (fun y => geom2PNat.map (fun a => syracStep k y a))
      simp only [PMF.map]
      exact PMF.bind_comm _ _ _

theorem syracPMF_toReal_eq_residueMass (k : ℕ) (v : ZMod (3 ^ k)) :
    (syracPMF k v).toReal = residueMass k v := by
  classical
  rw [← geometricWordPMF_map_wordResidue, pmf_map_apply_toReal_tsum]
  unfold residueMass
  apply tsum_congr
  intro w
  rw [geometricWordPMF_apply_toReal]
  rfl

/-- The actual canonical 3-adic cylinder probability is the native finite
Syracuse PMF atom, without an external identification premise. -/
theorem canonical_cylinder_eq_syracPMF (k : ℕ) (v : ZMod (3 ^ k)) :
    canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v} =
      syracPMF k v := by
  rw [canonical_cylinder_probability, ← syracPMF_toReal_eq_residueMass,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

theorem canonical_cylinder_real_eq_syracPMF (k : ℕ) (v : ZMod (3 ^ k)) :
    (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal =
      (syracPMF k v).toReal := by
  rw [canonical_cylinder_eq_syracPMF]

#print axioms geometricWordPMF_map_wordResidue
#print axioms canonical_cylinder_eq_syracPMF

end CollatzCylinderPacking.Arithmetic
