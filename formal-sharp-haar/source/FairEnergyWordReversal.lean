import FairEnergyWordCore
import Erdos1135.Tao.Syracuse.AffineReverse

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

def wordPNatList : (k : ℕ) → GeometricWord k → List ℕ+
  | 0, _ => []
  | k + 1, (a, w) => ⟨a + 1, Nat.succ_pos a⟩ :: wordPNatList k w

theorem wordPNatList_coe (k : ℕ) (w : GeometricWord k) :
    (wordPNatList k w).map (fun a : ℕ+ => (a : ℕ)) = wordList k w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases w with ⟨a, w⟩
    simp [wordPNatList, wordList, ih]

theorem wordPNatList_length (k : ℕ) (w : GeometricWord k) :
    (wordPNatList k w).length = k := by
  have h := congrArg List.length (wordPNatList_coe k w)
  simpa only [List.length_map, wordList_length] using h

theorem wordPNatList_weight (k : ℕ) (w : GeometricWord k) :
    Erdos1135.Tao.taoTupleWeight (wordPNatList k w) = wordLength k w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases w with ⟨a, w⟩
    simp only [wordPNatList, Erdos1135.Tao.taoTupleWeight_cons, wordLength, ih]
    rfl

theorem wordPNatList_reverse_numerator (k : ℕ) (w : GeometricWord k) :
    Erdos1135.Tao.taoOffsetNum (wordPNatList k w).reverse =
      affineNumerator (wordList k w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases w with ⟨a, w⟩
    simp only [wordPNatList, Erdos1135.Tao.taoOffsetNum_reverse_cons,
      wordPNatList_weight, ih, wordList, affineNumerator, wordList_sum]

theorem affineNumerator_injective_of_wordLength {k : ℕ} {w v : GeometricWord k}
    (hA : wordLength k w = wordLength k v)
    (hB : affineNumerator (wordList k w) = affineNumerator (wordList k v)) :
    w = v := by
  have hrev : (wordPNatList k w).reverse = (wordPNatList k v).reverse := by
    apply Erdos1135.Tao.taoOffsetNum_injective_of_length_weight
    · simp only [List.length_reverse, wordPNatList_length]
    · simpa only [Erdos1135.Tao.taoTupleWeight_reverse, wordPNatList_weight] using hA
    · simpa only [wordPNatList_reverse_numerator] using hB
  have hlist : wordPNatList k w = wordPNatList k v := by
    simpa only [List.reverse_reverse] using congrArg List.reverse hrev
  apply wordList_injective k
  simpa only [wordPNatList_coe] using
    congrArg (List.map (fun a : ℕ+ => (a : ℕ))) hlist

#print axioms wordPNatList_reverse_numerator
#print axioms affineNumerator_injective_of_wordLength

end CollatzCylinderPacking.Arithmetic.FairEnergy
