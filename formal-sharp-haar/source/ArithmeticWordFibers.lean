import ArithmeticInverseTuples
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem wordLength_ge_depth (k : ℕ) (w : GeometricWord k) : k ≤ wordLength k w := by
  have h := List.length_le_sum_of_one_le (wordList k w) (by
    intro a ha
    exact wordList_positive k w a ha)
  simpa only [wordList_length, wordList_sum] using h

noncomputable def wordBox : (k : ℕ) → ℕ → Finset (GeometricWord k)
  | 0, _ => {()}
  | k + 1, B => (Finset.range B).product (wordBox k B)

theorem word_mem_box_of_length_lt (k B : ℕ) (w : GeometricWord k)
    (h : wordLength k w < B) : w ∈ wordBox k B := by
  induction k with
  | zero => cases w; exact Finset.mem_singleton.mpr rfl
  | succ k ih =>
    rcases w with ⟨a, w⟩
    change a + 1 + wordLength k w < B at h
    change (a, w) ∈ (Finset.range B).product (wordBox k B)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), ih w (by omega)⟩

noncomputable def wordFiber (k A : ℕ) : Finset (GeometricWord k) := by
  classical
  exact (wordBox k (A + 1)).filter (fun w => wordLength k w = A)

theorem mem_wordFiber (k A : ℕ) (w : GeometricWord k) :
    w ∈ wordFiber k A ↔ wordLength k w = A := by
  classical
  simp only [wordFiber, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨word_mem_box_of_length_lt k (A + 1) w (by omega), h⟩⟩

noncomputable def validFiber (k N A : ℕ) : Finset (GeometricWord k) := by
  classical
  exact (wordFiber k A).filter (ValidWord k N)

theorem mem_validFiber (k N A : ℕ) (w : GeometricWord k) :
    w ∈ validFiber k N A ↔ wordLength k w = A ∧ ValidWord k N w := by
  classical
  simp only [validFiber, Finset.mem_filter, mem_wordFiber]

noncomputable def tupleFiber (k N A : ℕ) : Finset (List ℕ) := by
  classical
  exact (validFiber k N A).image (wordList k)

theorem tupleFiber_card (k N A : ℕ) :
    (tupleFiber k N A).card = (validFiber k N A).card := by
  classical
  exact Finset.card_image_of_injOn (fun _ _ _ _ h => wordList_injective k h)

theorem tupleFiber_sum {k N A : ℕ} {as : List ℕ} (h : as ∈ tupleFiber k N A) :
    as.sum = A := by
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
  rw [wordList_sum]
  exact ((mem_validFiber k N A w).mp hw).1

theorem tupleFiber_length {k N A : ℕ} {as : List ℕ} (h : as ∈ tupleFiber k N A) :
    as.length = k := by
  classical
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h
  exact wordList_length k w

theorem tupleFiber_admissible {k N A : ℕ} (hk : 0 < k) (hN : 0 < N)
    {as : List ℕ} (h : as ∈ tupleFiber k N A) :
    Admissible N as (tupleEndpoint N as) := by
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
  exact valid_word_admissible hk hN ((mem_validFiber k N A w).mp hw).2

noncomputable def headSet (k N : ℕ) : Finset (GeometricWord k) := by
  classical
  exact (wordBox k (5 * k)).filter (fun w => ValidWord k N w ∧ wordLength k w < 5 * k)

theorem mem_headSet (k N : ℕ) (w : GeometricWord k) :
    w ∈ headSet k N ↔ ValidWord k N w ∧ wordLength k w < 5 * k := by
  classical
  simp only [headSet, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨word_mem_box_of_length_lt k (5 * k) w h.2, h⟩⟩

theorem headSet_fiber (k N i : ℕ) (hi : i < 4 * k) :
    (headSet k N).filter (fun w => wordLength k w - k = i) = validFiber k N (k + i) := by
  classical
  ext w
  rw [Finset.mem_filter, mem_headSet, mem_validFiber]
  have hg := wordLength_ge_depth k w
  constructor
  · rintro ⟨⟨hv, hl⟩, he⟩
    exact ⟨by omega, hv⟩
  · rintro ⟨he, hv⟩
    exact ⟨⟨hv, by omega⟩, by omega⟩

#print axioms tupleFiber_admissible
#print axioms headSet_fiber

end CollatzCylinderPacking.Arithmetic
