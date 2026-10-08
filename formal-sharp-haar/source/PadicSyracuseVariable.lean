import CompatibleSyracuseResidues
import Mathlib.NumberTheory.Padics.RingHoms

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

instance threePrimeFact : Fact (Nat.Prime 3) := ⟨by decide⟩

def integerResidue (k : ℕ) (f : ℕ → ℕ) : ℤ :=
  (wordResidue k (sequenceWord k f)).val

theorem integer_residue_increment (k : ℕ) (f : ℕ → ℕ) :
    (3 : ℤ) ^ k ∣ integerResidue (k + 1) f - integerResidue k f := by
  have hc := sequence_residue_compatible k f
  have he : ((wordResidue (k + 1) (sequenceWord (k + 1) f)).val : ZMod (3 ^ k)) =
      wordResidue k (sequenceWord k f) := by
    calc
      _ = reduceResidue k (k + 1) (by omega)
          ((wordResidue (k + 1) (sequenceWord (k + 1) f)).val : ZMod (3 ^ (k + 1))) := by
        rw [map_natCast]
      _ = _ := by rw [ZMod.natCast_zmod_val]; exact hc
  have hz : ((integerResidue (k + 1) f - integerResidue k f : ℤ) : ZMod (3 ^ k)) = 0 := by
    simp only [integerResidue, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, he, sub_self]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (3 ^ k)).mp hz
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hd

/-- The unique 3-adic value with all the explicit Syracuse prefix residues. -/
noncomputable def canonicalSyracuseVariable (f : ℕ → ℕ) : ℤ_[3] :=
  PadicInt.ofIntSeq (fun k => integerResidue k f)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun k => integerResidue k f) 3
      (fun k => integer_residue_increment k f))

theorem canonical_variable_projection (k : ℕ) (f : ℕ → ℕ) :
    PadicInt.toZModPow k (canonicalSyracuseVariable f) = wordResidue k (sequenceWord k f) := by
  have h := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun j => integerResidue j f) 3
    (fun j => integer_residue_increment j f) k
  simpa only [canonicalSyracuseVariable, integerResidue, Int.cast_natCast, ZMod.natCast_zmod_val]
    using h

theorem canonical_variable_unique (f : ℕ → ℕ) (x : ℤ_[3])
    (hx : ∀ k, PadicInt.toZModPow k x = wordResidue k (sequenceWord k f)) :
    x = canonicalSyracuseVariable f := by
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  rw [hx, canonical_variable_projection]

#print axioms integer_residue_increment
#print axioms canonical_variable_projection
#print axioms canonical_variable_unique

end CollatzCylinderPacking.Arithmetic
