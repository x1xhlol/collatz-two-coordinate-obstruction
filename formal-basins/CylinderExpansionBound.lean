import CylinderHeadBound
import GeometricWordTail

set_option autoImplicit false

namespace CollatzCylinderPacking

theorem certificate_card_le_endpointCount {A k N : ℕ} {F : Finset (List ℕ)}
    (endpoint : List ℕ → ℕ)
    (hsum : ∀ as ∈ F, as.sum = A)
    (hlen : ∀ as ∈ F, as.length = k)
    (hadm : ∀ as ∈ F, Admissible N as (endpoint as)) :
    F.card ≤ endpointCount A k N := by
  classical
  have hm : Set.MapsTo endpoint F (endpointSet A k N) := by
    intro as ha
    apply mem_endpointSet.mpr
    have h := hadm as ha
    refine ⟨h.odd_start, ?_, ?_⟩
    · simpa only [hsum as ha] using h.endpoint
    · simpa only [hsum as ha, hlen as ha] using h.odd_count
  have hi : Set.InjOn endpoint F := by
    intro as ha bs hb he
    apply admissible_endpoint_injective (hadm as ha) (hadm bs hb) _ he
    rw [hsum as ha, hsum bs hb]
  exact Finset.card_le_card_of_injOn endpoint hm hi

theorem certificate_head_bound_rat (k N : ℕ)
    (F : ℕ → Finset (List ℕ)) (endpoint : ℕ → List ℕ → ℕ)
    (hsum : ∀ i < 4 * k, ∀ as ∈ F i, as.sum = k + i)
    (hlen : ∀ i < 4 * k, ∀ as ∈ F i, as.length = k)
    (hadm : ∀ i < 4 * k, ∀ as ∈ F i, Admissible N as (endpoint i as)) :
    (∑ i ∈ Finset.range (4 * k), ((F i).card : ℚ) / 2 ^ (k + i)) ≤
      (2 * (k : ℚ) + 2) / (2 : ℚ) ^ k := by
  calc
    (∑ i ∈ Finset.range (4 * k), ((F i).card : ℚ) / 2 ^ (k + i)) ≤
        ∑ i ∈ Finset.range (4 * k), endpointMass (k + i) k N := by
      apply Finset.sum_le_sum
      intro i hi
      have hib := Finset.mem_range.mp hi
      have hc := certificate_card_le_endpointCount (endpoint i)
        (hsum i hib) (hlen i hib) (hadm i hib)
      unfold endpointMass
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ ≤ (2 * (k : ℚ) + 2) / (2 : ℚ) ^ k := endpoint_head_bound k N

theorem certificate_head_bound_real (k N : ℕ)
    (F : ℕ → Finset (List ℕ)) (endpoint : ℕ → List ℕ → ℕ)
    (hsum : ∀ i < 4 * k, ∀ as ∈ F i, as.sum = k + i)
    (hlen : ∀ i < 4 * k, ∀ as ∈ F i, as.length = k)
    (hadm : ∀ i < 4 * k, ∀ as ∈ F i, Admissible N as (endpoint i as)) :
    (∑ i ∈ Finset.range (4 * k), ((F i).card : ℝ) / 2 ^ (k + i)) ≤
      (2 * (k : ℝ) + 2) / (2 : ℝ) ^ k := by
  have h := (Rat.cast_le (K := ℝ)).mpr
    (certificate_head_bound_rat k N F endpoint hsum hlen hadm)
  push_cast at h
  exact h

noncomputable def filteredGeometricTail (k : ℕ) (P : GeometricWord k → Prop)
    (w : GeometricWord k) : ℝ := by
  classical
  exact if P w then geometricTailTerm k w else 0

theorem filtered_tail_nonneg (k : ℕ) (P : GeometricWord k → Prop)
    (w : GeometricWord k) : 0 ≤ filteredGeometricTail k P w := by
  classical
  unfold filteredGeometricTail
  split_ifs
  · exact geometricTailTerm_nonneg k w
  · exact le_rfl

theorem filtered_tail_le (k : ℕ) (P : GeometricWord k → Prop)
    (w : GeometricWord k) : filteredGeometricTail k P w ≤ geometricTailTerm k w := by
  classical
  unfold filteredGeometricTail
  split_ifs
  · exact le_rfl
  · exact geometricTailTerm_nonneg k w

theorem filtered_tail_summable (k : ℕ) (P : GeometricWord k → Prop) :
    Summable (filteredGeometricTail k P) :=
  Summable.of_nonneg_of_le (filtered_tail_nonneg k P) (filtered_tail_le k P)
    (geometric_tail_summable k)

theorem filtered_tail_bound (k : ℕ) (P : GeometricWord k → Prop) :
    (∑' w : GeometricWord k, filteredGeometricTail k P w) ≤ (1 / 2 : ℝ) ^ k := by
  exact (Summable.tsum_le_tsum (filtered_tail_le k P)
    (filtered_tail_summable k P) (geometric_tail_summable k)).trans
      (geometric_tail_le_half_pow k)

/-- The uniform numerical cylinder bound from an EXPLICIT expansion equality.
The equality is a hypothesis, not a formalized theorem about the stationary
measure. Its finite part is certified by actual Collatz inverse trajectories;
the infinite part may impose any further admissibility predicate. -/
theorem cylinder_bound_of_expansion (k N : ℕ) (q : ℝ)
    (F : ℕ → Finset (List ℕ)) (endpoint : ℕ → List ℕ → ℕ)
    (P : GeometricWord k → Prop)
    (hsum : ∀ i < 4 * k, ∀ as ∈ F i, as.sum = k + i)
    (hlen : ∀ i < 4 * k, ∀ as ∈ F i, as.length = k)
    (hadm : ∀ i < 4 * k, ∀ as ∈ F i, Admissible N as (endpoint i as))
    (expansion : q =
      (∑ i ∈ Finset.range (4 * k), ((F i).card : ℝ) / 2 ^ (k + i)) +
      ∑' w : GeometricWord k, filteredGeometricTail k P w) :
    q ≤ (2 * (k : ℝ) + 3) / (2 : ℝ) ^ k := by
  rw [expansion]
  calc
    (∑ i ∈ Finset.range (4 * k), ((F i).card : ℝ) / 2 ^ (k + i)) +
        (∑' w : GeometricWord k, filteredGeometricTail k P w) ≤
        (2 * (k : ℝ) + 2) / (2 : ℝ) ^ k + (1 / 2 : ℝ) ^ k :=
      add_le_add (certificate_head_bound_real k N F endpoint hsum hlen hadm)
        (filtered_tail_bound k P)
    _ = (2 * (k : ℝ) + 3) / (2 : ℝ) ^ k := by
      rw [one_div_pow]
      ring

#print axioms certificate_head_bound_real
#print axioms cylinder_bound_of_expansion

end CollatzCylinderPacking
