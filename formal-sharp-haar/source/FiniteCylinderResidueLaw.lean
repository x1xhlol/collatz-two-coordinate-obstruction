import ArithmeticCylinderCongruence
import ArithmeticCylinderLower
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

def powerTwoUnit (k A : ℕ) : (ZMod (3 ^ k))ˣ :=
  ZMod.unitOfCoprime (2 ^ A)
    (((by decide : Nat.Coprime 2 3).pow_left A).pow_right k)

def wordResidue (k : ℕ) (w : GeometricWord k) : ZMod (3 ^ k) :=
  ↑(powerTwoUnit k (wordLength k w))⁻¹ * (affineNumerator (wordList k w) : ZMod (3 ^ k))

theorem validWord_iff_wordResidue {k N : ℕ} (hN : 0 < N) (w : GeometricWord k) :
    ValidWord k N w ↔ (N : ZMod (3 ^ k)) = wordResidue k w := by
  rw [validWord_iff_compatible hN w]
  unfold Compatible
  rw [wordList_length, wordList_sum, ← ZMod.natCast_eq_natCast_iff]
  unfold wordResidue
  rw [Units.eq_inv_mul_iff_mul_eq]
  simp only [powerTwoUnit, ZMod.coe_unitOfCoprime, Nat.cast_mul]

noncomputable def residueTerm (k : ℕ) (v : ZMod (3 ^ k)) (w : GeometricWord k) : ℝ := by
  classical
  exact if v = wordResidue k w then (1 / 2 : ℝ) ^ wordLength k w else 0

noncomputable def residueMass (k : ℕ) (v : ZMod (3 ^ k)) : ℝ :=
  ∑' w : GeometricWord k, residueTerm k v w

theorem residueTerm_nonneg (k : ℕ) (v : ZMod (3 ^ k)) (w : GeometricWord k) :
    0 ≤ residueTerm k v w := by
  classical
  unfold residueTerm
  split_ifs <;> positivity

theorem residueTerm_summable (k : ℕ) (v : ZMod (3 ^ k)) : Summable (residueTerm k v) := by
  classical
  apply Summable.of_nonneg_of_le (residueTerm_nonneg k v) _
    (geometric_word_probability k).summable
  intro w
  unfold residueTerm
  split_ifs
  · exact le_rfl
  · positivity

/-- Identification with the pushforward of the geometric tuple law to its
explicit affine residue. No measure on the 3-adic integers is assumed. -/
theorem arithmetic_mass_eq_residueMass {k N : ℕ} (hN : 0 < N) :
    arithmeticMass k N = residueMass k (N : ZMod (3 ^ k)) := by
  classical
  apply tsum_congr
  intro w
  simp only [arithmeticTerm, residueTerm, validWord_iff_wordResidue hN w]

theorem residue_mass_nonneg (k : ℕ) (v : ZMod (3 ^ k)) : 0 ≤ residueMass k v :=
  tsum_nonneg (residueTerm_nonneg k v)

/-- The residue masses sum to one: this is a finite probability law. -/
theorem residue_mass_total (k : ℕ) :
    (∑ v : ZMod (3 ^ k), residueMass k v) = 1 := by
  classical
  unfold residueMass
  rw [← Summable.tsum_finsetSum (fun v _ => residueTerm_summable k v)]
  have he : (fun w : GeometricWord k => ∑ v : ZMod (3 ^ k), residueTerm k v w) =
      (fun w : GeometricWord k => (1 / 2 : ℝ) ^ wordLength k w) := by
    funext w
    simp [residueTerm]
  rw [he]
  exact (geometric_word_probability k).tsum_eq

theorem positive_representative (k : ℕ) (v : ZMod (3 ^ k)) :
    0 < v.val + 3 ^ k ∧ ((v.val + 3 ^ k : ℕ) : ZMod (3 ^ k)) = v := by
  haveI : NeZero (3 ^ k) := ⟨by positivity⟩
  refine ⟨by positivity, ?_⟩
  simp

theorem residue_mass_upper {k : ℕ} (hk : 0 < k) (v : ZMod (3 ^ k)) :
    residueMass k v ≤ (2 * (k : ℝ) + 3) / (2 : ℝ) ^ k := by
  obtain ⟨hp, he⟩ := positive_representative k v
  rw [← he, ← arithmetic_mass_eq_residueMass hp]
  exact arithmetic_mass_upper hk hp

theorem residue_mass_lower {k : ℕ} (hk : 0 < k) :
    (1 / 2 : ℝ) ^ k ≤ residueMass k (-1) := by
  have hp : 0 < 3 ^ k - 1 := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ (3 : ℕ)) hk
    simp only [pow_one] at h
    omega
  have hc : ((3 ^ k - 1 : ℕ) : ZMod (3 ^ k)) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 3 ^ k)]
    simp
  rw [← hc, ← arithmetic_mass_eq_residueMass hp]
  exact arithmetic_mass_lower k

#print axioms validWord_iff_wordResidue
#print axioms arithmetic_mass_eq_residueMass
#print axioms residue_mass_total
#print axioms residue_mass_upper
#print axioms residue_mass_lower

end CollatzCylinderPacking.Arithmetic
