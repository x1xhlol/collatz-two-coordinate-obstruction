import ArithmeticInverseBlocks
import GeometricWordTail

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem iterate_add (A B n : ℕ) :
    iterate (A + B) n = iterate B (iterate A n) := by
  induction B with
  | zero => simp [iterate]
  | succ B ih => exact congrArg step ih

theorem oddCount_add (A B n : ℕ) :
    oddCount (A + B) n = oddCount A n + oddCount B (iterate A n) := by
  induction B with
  | zero => simp [oddCount]
  | succ B ih =>
    change oddCount (A + B) n + iterate (A + B) n % 2 =
      oddCount A n + (oddCount B (iterate A n) + iterate B (iterate A n) % 2)
    rw [ih, iterate_add]
    omega

theorem reverseItinerary_add (A B n : ℕ) :
    reverseItinerary (A + B) n =
      reverseItinerary B (iterate A n) ++ reverseItinerary A n := by
  induction B with
  | zero => simp [reverseItinerary]
  | succ B ih =>
    change iterate (A + B) n % 2 :: reverseItinerary (A + B) n =
      (iterate B (iterate A n) % 2 :: reverseItinerary B (iterate A n)) ++
        reverseItinerary A n
    rw [iterate_add, ih]
    rfl

def tupleEndpoint : ℕ → List ℕ → ℕ
  | N, [] => N
  | N, a :: as => tupleEndpoint (inverseValue a N) as

def ValidTuple : ℕ → List ℕ → Prop
  | _, [] => True
  | N, a :: as => ValidBlock a N ∧ ValidTuple (inverseValue a N) as

theorem validTuple_positive {N : ℕ} {as : List ℕ} (h : ValidTuple N as) :
    ∀ a ∈ as, 0 < a := by
  induction as generalizing N with
  | nil => simp
  | cons a as ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1.1
    · exact ih h.2 b hb

theorem valid_tuple_path {N : ℕ} {as : List ℕ}
    (hN : 0 < N) (h : ValidTuple N as) :
    0 < tupleEndpoint N as ∧
    iterate as.sum (tupleEndpoint N as) = N ∧
    reverseItinerary as.sum (tupleEndpoint N as) = encode as ∧
    (as ≠ [] → tupleEndpoint N as % 2 = 1) := by
  induction as generalizing N with
  | nil => simp [tupleEndpoint, iterate, reverseItinerary, encode, hN]
  | cons a as ih =>
    have hp := inverse_positive hN h.1
    have hb := inverse_block_admissible hN h.1
    have hi := ih hp h.2
    change 0 < tupleEndpoint (inverseValue a N) as ∧
      iterate (a + as.sum) (tupleEndpoint (inverseValue a N) as) = N ∧
      reverseItinerary (a + as.sum) (tupleEndpoint (inverseValue a N) as) = encode (a :: as) ∧
      (a :: as ≠ [] → tupleEndpoint (inverseValue a N) as % 2 = 1)
    refine ⟨hi.1, ?_, ?_, ?_⟩
    · rw [Nat.add_comm a as.sum, iterate_add, hi.2.1]
      simpa using hb.endpoint
    · rw [Nat.add_comm a as.sum, reverseItinerary_add, hi.2.1, hi.2.2.1]
      have hpar : reverseItinerary a (inverseValue a N) =
          List.replicate (a - 1) 0 ++ [1] :=
        (block_path h.1.1 (inverse_identity hN h.1)).2.2.2
      rw [hpar, encode]
      simp [List.append_assoc]
    · intro _
      cases as with
      | nil => simpa only [tupleEndpoint] using hb.odd_start
      | cons b bs => exact hi.2.2.2 (by simp)

theorem valid_tuple_admissible {N : ℕ} {as : List ℕ}
    (hN : 0 < N) (h : ValidTuple N as) (hne : as ≠ []) :
    Admissible N as (tupleEndpoint N as) := by
  have hp := valid_tuple_path hN h
  exact ⟨validTuple_positive h, hp.2.2.2 hne, hp.2.1, hp.2.2.1⟩

def wordList : (k : ℕ) → GeometricWord k → List ℕ
  | 0, _ => []
  | k + 1, (a, w) => (a + 1) :: wordList k w

theorem wordList_length (k : ℕ) (w : GeometricWord k) : (wordList k w).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases w with ⟨a, w⟩
    simp [wordList, ih]

theorem wordList_sum (k : ℕ) (w : GeometricWord k) : (wordList k w).sum = wordLength k w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases w with ⟨a, w⟩
    simp [wordList, wordLength, ih]

theorem wordList_positive (k : ℕ) (w : GeometricWord k) :
    ∀ a ∈ wordList k w, 0 < a := by
  induction k with
  | zero => simp [wordList]
  | succ k ih =>
    rcases w with ⟨a, w⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · exact ih w b hb

theorem wordList_injective (k : ℕ) : Function.Injective (wordList k) := by
  induction k with
  | zero => intro x y _; cases x; cases y; rfl
  | succ k ih =>
    intro x y he
    rcases x with ⟨a, x⟩
    rcases y with ⟨b, y⟩
    change (a + 1) :: wordList k x = (b + 1) :: wordList k y at he
    injection he with hab hxy
    have hab' : a = b := by omega
    have hxy' := ih hxy
    subst b
    subst y
    rfl

theorem wordList_ne_nil {k : ℕ} (hk : 0 < k) (w : GeometricWord k) : wordList k w ≠ [] := by
  intro he
  have hl := wordList_length k w
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega

def ValidWord (k N : ℕ) (w : GeometricWord k) : Prop := ValidTuple N (wordList k w)

theorem valid_word_admissible {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    {w : GeometricWord k} (h : ValidWord k N w) :
    Admissible N (wordList k w) (tupleEndpoint N (wordList k w)) :=
  valid_tuple_admissible hN h (wordList_ne_nil hk w)

#print axioms valid_tuple_path
#print axioms valid_word_admissible
#print axioms wordList_injective

end CollatzCylinderPacking.Arithmetic
