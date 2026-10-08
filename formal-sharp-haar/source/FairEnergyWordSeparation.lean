import FairEnergyWordReversal

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

theorem affineNumerator_add_two_pow_le (k : ℕ) (w : GeometricWord k) :
    affineNumerator (wordList k w) + 2 ^ wordLength k w ≤
      3 ^ k * 2 ^ (wordLength k w - k) := by
  induction k with
  | zero => simp [wordList, affineNumerator, wordLength]
  | succ k ih =>
    rcases w with ⟨a, w⟩
    have hA := wordLength_ge_depth k w
    have hsplit : wordLength k w = k + (wordLength k w - k) := by omega
    have hU : 2 ^ wordLength k w ≤ 3 ^ k * 2 ^ (wordLength k w - k) := by
      conv_lhs => rw [hsplit, pow_add]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide : 2 ≤ 3) k)
    have htail := ih w
    have hexcess : a + 1 + wordLength k w - (k + 1) =
        a + (wordLength k w - k) := by omega
    have hr : 2 ^ a = (2 ^ a - 1) + 1 := by
      have hp : 0 < 2 ^ a := by positivity
      omega
    simp only [wordList, affineNumerator, wordList_sum, wordLength]
    rw [hexcess, pow_add, pow_add, pow_succ, pow_succ, hr]
    calc
      _ = 3 * (affineNumerator (wordList k w) + 2 ^ wordLength k w) +
          2 * ((2 ^ a - 1) * 2 ^ wordLength k w) := by ring
      _ ≤ 3 * (3 ^ k * 2 ^ (wordLength k w - k)) +
          2 * ((2 ^ a - 1) * (3 ^ k * 2 ^ (wordLength k w - k))) := by
        exact Nat.add_le_add (Nat.mul_le_mul_left 3 htail)
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (2 ^ a - 1) hU))
      _ ≤ _ := by
        rw [pow_add, hr]
        simp only [Nat.add_sub_cancel]
        nlinarith [Nat.zero_le ((2 ^ a - 1) * (3 ^ k * 2 ^ (wordLength k w - k)))]

theorem affineNumerator_lt_scaled_two_pow (k : ℕ) (w : GeometricWord k) :
    affineNumerator (wordList k w) < 3 ^ k * 2 ^ (wordLength k w - k) := by
  have h := affineNumerator_add_two_pow_le k w
  have hp : 0 < 2 ^ wordLength k w := by positivity
  omega

theorem numerator_quotient_lt (k : ℕ) (w : GeometricWord k) :
    affineNumerator (wordList k w) / 3 ^ k < 2 ^ (wordLength k w - k) := by
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 3 ^ k)).mpr
  simpa only [Nat.mul_comm] using affineNumerator_lt_scaled_two_pow k w

theorem numerator_quotient_le_translation (k : ℕ) (w : GeometricWord k) :
    ((affineNumerator (wordList k w) / 3 ^ k : ℕ) : ℝ) ≤ wordTranslation k w := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ k)).mpr
  exact_mod_cast Nat.div_mul_le_self (affineNumerator (wordList k w)) (3 ^ k)

theorem numerator_mod_eq_of_wordResidue {k : ℕ} {w v : GeometricWord k}
    (hA : wordLength k w = wordLength k v) (hres : wordResidue k w = wordResidue k v) :
    affineNumerator (wordList k w) % 3 ^ k = affineNumerator (wordList k v) % 3 ^ k := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  apply (Units.mul_right_inj (powerTwoUnit k (wordLength k v))⁻¹).mp
  simpa only [wordResidue, hA] using hres

theorem numerator_quotient_injective_on_fiber {k A : ℕ} (v : ZMod (3 ^ k)) :
    Set.InjOn (fun w : GeometricWord k => affineNumerator (wordList k w) / 3 ^ k)
      {w | wordLength k w = A ∧ wordResidue k w = v} := by
  intro w hw u hu hquot
  have hA : wordLength k w = wordLength k u := hw.1.trans hu.1.symm
  have hmod := numerator_mod_eq_of_wordResidue hA (hw.2.trans hu.2.symm)
  apply affineNumerator_injective_of_wordLength hA
  have hwdiv := Nat.mod_add_div (affineNumerator (wordList k w)) (3 ^ k)
  have hudiv := Nat.mod_add_div (affineNumerator (wordList k u)) (3 ^ k)
  dsimp only at hquot
  rw [hmod, hquot] at hwdiv
  exact hwdiv.symm.trans hudiv

end CollatzCylinderPacking.Arithmetic.FairEnergy
