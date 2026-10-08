import OptimalCylinderPacking
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace CollatzCylinderPacking

/-- Inverse order: a block of a-1 even predecessors followed by one odd
predecessor. Actual admissibility is checked against the trajectory below. -/
def encode : List ℕ → List ℕ
  | [] => []
  | a :: as => List.replicate (a - 1) 0 ++ 1 :: encode as

def bumpHead : List ℕ → List ℕ
  | [] => []
  | a :: as => (a + 1) :: as

def decode : List ℕ → List ℕ
  | [] => []
  | b :: bs => if b = 1 then 1 :: decode bs else bumpHead (decode bs)

theorem decode_zeros_one (z : ℕ) (w : List ℕ) :
    decode (List.replicate z 0 ++ 1 :: w) = (z + 1) :: decode w := by
  induction z with
  | zero => simp [decode]
  | succ z ih => simp [List.replicate_succ, decode, ih, bumpHead]

theorem decode_encode (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    decode (encode as) = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := hpos a (by simp)
    have ht : ∀ b ∈ as, 0 < b := fun b hb => hpos b (by simp [hb])
    rw [encode, decode_zeros_one, ih ht]
    congr 1
    omega

theorem encode_injective {as bs : List ℕ}
    (ha : ∀ a ∈ as, 0 < a) (hb : ∀ b ∈ bs, 0 < b)
    (he : encode as = encode bs) : as = bs := by
  have h := congrArg decode he
  simpa only [decode_encode as ha, decode_encode bs hb] using h

theorem encode_sum (as : List ℕ) : (encode as).sum = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [encode, ih, Nat.add_comm]

theorem encode_length (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    (encode as).length = as.sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := hpos a (by simp)
    have ht : ∀ b ∈ as, 0 < b := fun b hb => hpos b (by simp [hb])
    simp only [encode, List.length_append, List.length_replicate,
      List.length_cons, ih ht, List.sum_cons]
    omega

def reverseItinerary : ℕ → ℕ → List ℕ
  | 0, _ => []
  | A + 1, n => iterate A n % 2 :: reverseItinerary A n

theorem reverseItinerary_sum (A n : ℕ) :
    (reverseItinerary A n).sum = oddCount A n := by
  induction A with
  | zero => rfl
  | succ A ih => simp [reverseItinerary, oddCount, ih, Nat.add_comm]

theorem reverseItinerary_length (A n : ℕ) :
    (reverseItinerary A n).length = A := by
  induction A with
  | zero => rfl
  | succ A ih => simp [reverseItinerary, ih]

/-- A positive exponent tuple together with its actual integer inverse-word
trajectory. This certificate contains no measure-theoretic assumption. -/
structure Admissible (N : ℕ) (as : List ℕ) (m : ℕ) : Prop where
  positive : ∀ a ∈ as, 0 < a
  odd_start : m % 2 = 1
  endpoint : iterate as.sum m = N
  parities : reverseItinerary as.sum m = encode as

theorem Admissible.odd_count {N m : ℕ} {as : List ℕ}
    (h : Admissible N as m) : oddCount as.sum m = as.length := by
  have hs := congrArg List.sum h.parities
  simpa only [reverseItinerary_sum, encode_sum] using hs

/-- With total shortcut length fixed, two admissible inverse tuples cannot
have the same integer endpoint. This includes even final targets. -/
theorem admissible_endpoint_injective {N m n : ℕ} {as bs : List ℕ}
    (ha : Admissible N as m) (hb : Admissible N bs n)
    (hlen : as.sum = bs.sum) (he : m = n) : as = bs := by
  apply encode_injective ha.positive hb.positive
  rw [← ha.parities, ← hb.parities, hlen, he]

/-- The uniform combinatorial cylinder bound, for every finite family of
actual admissible positive exponent tuples with fixed length and sum. -/
theorem admissible_tuple_card_bound {A k N : ℕ} {S : Finset (List ℕ)}
    (endpoint : List ℕ → ℕ)
    (hsum : ∀ as ∈ S, as.sum = A)
    (hlen : ∀ as ∈ S, as.length = k)
    (hadm : ∀ as ∈ S, Admissible N as (endpoint as)) :
    S.card ≤ 2 ^ (A - k) / 2 + 1 := by
  classical
  have hm : Set.MapsTo endpoint S (endpointSet A k N) := by
    intro as ha
    apply mem_endpointSet.mpr
    have h := hadm as ha
    refine ⟨h.odd_start, ?_, ?_⟩
    · simpa only [hsum as ha] using h.endpoint
    · simpa only [hsum as ha, hlen as ha] using h.odd_count
  have hi : Set.InjOn endpoint S := by
    intro as ha bs hb he
    apply admissible_endpoint_injective (hadm as ha) (hadm bs hb) _ he
    rw [hsum as ha, hsum bs hb]
  calc
    S.card ≤ (endpointSet A k N).card :=
      Finset.card_le_card_of_injOn endpoint hm hi
    _ ≤ 2 ^ (A - k) / 2 + 1 := endpointCount_bound A k N

theorem admissible_tuple_scaled_card_bound {A k N : ℕ} {S : Finset (List ℕ)}
    (endpoint : List ℕ → ℕ)
    (hsum : ∀ as ∈ S, as.sum = A)
    (hlen : ∀ as ∈ S, as.length = k)
    (hadm : ∀ as ∈ S, Admissible N as (endpoint as)) :
    2 * S.card ≤ 2 ^ (A - k) + 2 := by
  have h := admissible_tuple_card_bound endpoint hsum hlen hadm
  omega

#print axioms encode_injective
#print axioms admissible_endpoint_injective
#print axioms admissible_tuple_scaled_card_bound

end CollatzCylinderPacking
