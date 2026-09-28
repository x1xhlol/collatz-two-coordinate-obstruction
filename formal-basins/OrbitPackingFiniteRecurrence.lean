import OrbitPackingParityCount
import Mathlib.Order.Interval.Finset.Nat

/-! The finite distinct-trajectory recurrence, including terminal indices. -/

set_option autoImplicit false

namespace CollatzOrbitPackingFiniteRecurrence

open CollatzCylinderPacking CollatzOrbitPackingParityCount

def prefixCount (N L X : ℕ) : ℕ :=
  ((Finset.range L).filter (fun i => iterate i N ≤ X)).card

theorem iterate_add (a b n : ℕ) : iterate (a + b) n = iterate b (iterate a n) := by
  induction b with
  | zero => simp [iterate]
  | succ b ih => simpa only [Nat.add_succ, iterate] using congrArg step ih

theorem step_positive {n : ℕ} (hn : 0 < n) : 0 < step n := by
  unfold step
  split_ifs <;> omega

theorem iterate_positive {N : ℕ} (hN : 0 < N) (i : ℕ) : 0 < iterate i N := by
  induction i with
  | zero => exact hN
  | succ i ih => exact step_positive ih

theorem prefixCount_mono (N L : ℕ) {X Y : ℕ} (hXY : X ≤ Y) :
    prefixCount N L X ≤ prefixCount N L Y := by
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi, hx⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, hx.trans hXY⟩

/-- A distinct positive trajectory has at most `X` states at most `X`. -/
theorem prefixCount_le (N L X : ℕ) (hN : 0 < N)
    (hinj : Set.InjOn (fun i => iterate i N) (Finset.range L)) :
    prefixCount N L X ≤ X := by
  have hm : Set.MapsTo (fun i => iterate i N)
      ((Finset.range L).filter (fun i => iterate i N ≤ X)) (Finset.Icc 1 X) := by
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter] at hi
    simp only [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨iterate_positive hN i, hi.2⟩
  have hi := hinj.mono (Finset.filter_subset (fun i => iterate i N ≤ X) (Finset.range L))
  have hc := Finset.card_le_card_of_injOn (fun i => iterate i N) hm hi
  simpa [prefixCount] using hc

theorem small_start_endpoint {h n : ℕ} (hn : n < 2 * 2 ^ h) :
    iterate h n < 3 * 3 ^ oddCount h n := by
  have hu := (scaled_bounds h n).2
  have hp : 2 ^ (h - oddCount h n) ≤ 2 ^ h :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have h2 : 0 < (2 : ℕ) ^ h := by positivity
  have h3 : 0 < (3 : ℕ) ^ oddCount h n := by positivity
  have hs := Nat.mul_lt_mul_of_pos_left hn h3
  have he := Nat.mul_le_mul_left (3 ^ oddCount h n) hp
  have ht : 2 ^ h * iterate h n < 2 ^ h * (3 * 3 ^ oddCount h n) := by
    nlinarith only [hu, hs, he, h2]
  exact Nat.lt_of_mul_lt_mul_left ht

/-- The last `h` positions contribute at most `h`, even when the whole
trajectory is shorter than the requested window. -/
theorem terminal_card_le (L h : ℕ) {S : Finset ℕ} (hS : S ⊆ Finset.range L)
    (htail : ∀ i ∈ S, L ≤ i + h) : S.card ≤ h := by
  have hm : Set.MapsTo (fun i => L - (i + 1)) S (Finset.range h) := by
    intro i hi
    have hiL := Finset.mem_range.mp (hS hi)
    have ht := htail i hi
    change L - (i + 1) ∈ Finset.range h
    exact Finset.mem_range.mpr (by omega)
  have hi : Set.InjOn (fun i => L - (i + 1)) S := by
    intro i hi j hj he
    have hiL := Finset.mem_range.mp (hS hi)
    have hjL := Finset.mem_range.mp (hS hj)
    change L - (i + 1) = L - (j + 1) at he
    omega
  simpa using Finset.card_le_card_of_injOn (fun i => L - (i + 1)) hm hi

/-- The finite packing recurrence before replacing the binomial tail by
entropy.  Every term refers to the same finite distinct trajectory. -/
theorem finite_counting_recurrence (N L X h m : ℕ)
    (hinj : Set.InjOn (fun i => iterate i N) (Finset.range L))
    (hX : X < 2 * 2 ^ h) :
    prefixCount N L X ≤ prefixCount N L (3 * 3 ^ m) +
      2 * (∑ j ∈ (Finset.range (h + 1)).filter (fun j => m < j), h.choose j) + h := by
  let S := (Finset.range L).filter (fun i => iterate i N ≤ X)
  let good := S.filter (fun i => i + h < L ∧ oddCount h (iterate i N) ≤ m)
  let high := S.filter (fun i => m < oddCount h (iterate i N))
  let tail := S.filter (fun i => L ≤ i + h)
  have hgood : good.card ≤ prefixCount N L (3 * 3 ^ m) := by
    have hm : Set.MapsTo (fun i => i + h) good
        ((Finset.range L).filter (fun i => iterate i N ≤ 3 * 3 ^ m)) := by
      intro i hi
      simp only [good, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨⟨_, hiX⟩, hiL, him⟩ := hi
      have hend := small_start_endpoint (hiX.trans_lt hX)
      have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (3 : ℕ)) him
      change i + h ∈ (Finset.range L).filter (fun i => iterate i N ≤ 3 * 3 ^ m)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hiL, ?_⟩
      rw [iterate_add]
      exact hend.le.trans (Nat.mul_le_mul_left 3 hpow)
    have hi : Set.InjOn (fun i => i + h) good := by
      intro i _ j _ he
      change i + h = j + h at he
      omega
    exact Finset.card_le_card_of_injOn (fun i => i + h) hm hi
  have hhigh : high.card ≤
      2 * ∑ j ∈ (Finset.range (h + 1)).filter (fun j => m < j), h.choose j := by
    have hm : Set.MapsTo (fun i => iterate i N) high
        ((Finset.range (2 * 2 ^ h)).filter (fun n => m < oddCount h n)) := by
      intro i hi
      simp only [high, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨⟨_, hiX⟩, him⟩ := hi
      change iterate i N ∈ (Finset.range (2 * 2 ^ h)).filter (fun n => m < oddCount h n)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hiX.trans_lt hX), him⟩
    have hi : Set.InjOn (fun i => iterate i N) high := by
      apply hinj.mono
      intro i hi
      simp only [high, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact hi.1.1
    calc
      high.card ≤ ((Finset.range (2 * 2 ^ h)).filter (fun n => m < oddCount h n)).card :=
        Finset.card_le_card_of_injOn (fun i => iterate i N) hm hi
      _ = _ := card_oddCount_filter_double h (fun j => m < j)
  have htail : tail.card ≤ h := by
    apply terminal_card_le L h
    · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hcover : S ⊆ good ∪ high ∪ tail := by
    intro i hi
    by_cases hiL : i + h < L
    · by_cases him : oddCount h (iterate i N) ≤ m
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hi, hiL, him⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hi, by omega⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, by omega⟩)
  have hc : S.card ≤ good.card + high.card + tail.card := by
    calc
      S.card ≤ (good ∪ high ∪ tail).card := Finset.card_le_card hcover
      _ ≤ (good ∪ high).card + tail.card := Finset.card_union_le _ _
      _ ≤ good.card + high.card + tail.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  change S.card ≤ _
  omega

#print axioms prefixCount_le
#print axioms small_start_endpoint
#print axioms terminal_card_le
#print axioms finite_counting_recurrence

end CollatzOrbitPackingFiniteRecurrence
