import NonperiodicFiniteCylinder
import FirstHitEndpointTail

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

theorem ValidPrefix.odd {n k : ℕ} {x : ℕ → ℕ} (h : ValidPrefix n k x)
    (hnodd : n % 2 = 1) {i : ℕ} (hi : i ≤ k) : x i % 2 = 1 := by
  cases i with
  | zero => simpa only [h.1] using hnodd
  | succ i =>
    obtain ⟨a, ha, hx⟩ := h.2.2 i (by omega)
    rw [hx]
    exact (inverseEndpoint_block ha).1

theorem ValidPrefix.suffix_hit_clock {n k : ℕ} {x : ℕ → ℕ}
    (h : ValidPrefix n k x) {i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    ∃ A : ℕ, iterate A (x j) = x i ∧ oddCount A (x j) = j - i := by
  induction j generalizing i with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact ⟨0, rfl, rfl⟩
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i
      exact ⟨0, rfl, by simp [oddCount]⟩
    · obtain ⟨A, hA, hcount⟩ := ih (i := i) (by omega) (by omega)
      obtain ⟨a, ha, hx⟩ := h.2.2 j (by omega)
      have hstep : iterate (a + 1) (x (j + 1)) = x j := by
        rw [hx]
        exact (inverseEndpoint_block ha).2.1
      have hone : oddCount (a + 1) (x (j + 1)) = 1 := by
        rw [hx]
        exact (inverseEndpoint_block ha).2.2
      refine ⟨a + 1 + A, ?_, ?_⟩
      · rw [iterate_add, hstep, hA]
      · rw [oddCount_add, hstep, hone, hcount]
        omega

theorem ValidPrefix.hit_clock {n k : ℕ} {x : ℕ → ℕ}
    (h : ValidPrefix n k x) :
    ∃ A : ℕ, iterate A (x k) = n ∧ oddCount A (x k) = k := by
  simpa only [h.1, Nat.sub_zero] using h.suffix_hit_clock (i := 0) (j := k)
    (Nat.zero_le k) le_rfl

theorem oddCount_strict_of_odd_endpoint {q A B : ℕ} (hAB : A < B)
    (hodd : iterate A q % 2 = 1) : oddCount A q < oddCount B q := by
  have hpos := oddCount_pos_of_odd_start (q := iterate A q)
    (show 0 < B - A by omega) hodd
  have he : B = A + (B - A) := by omega
  rw [he, oddCount_add]
  omega

theorem odd_endpoint_time_eq_of_oddCount_eq {q A B : ℕ}
    (hAodd : iterate A q % 2 = 1) (hBodd : iterate B q % 2 = 1)
    (hcount : oddCount A q = oddCount B q) : A = B := by
  rcases lt_trichotomy A B with h | h | h
  · have := oddCount_strict_of_odd_endpoint h hAodd
    omega
  · exact h
  · have := oddCount_strict_of_odd_endpoint h hBodd
    omega

theorem ValidPrefix.endpoint_eq_of_common_ancestor {n k q : ℕ}
    {x z : ℕ → ℕ} (hx : ValidPrefix n k x) (hz : ValidPrefix n k z)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hqx : ∃ A, iterate A q = x k) (hqz : ∃ B, iterate B q = z k) :
    x k = z k := by
  obtain ⟨A, hA⟩ := hqx
  obtain ⟨B, hB⟩ := hqz
  obtain ⟨C, hC, hCx⟩ := hx.hit_clock
  obtain ⟨D, hD, hDz⟩ := hz.hit_clock
  have htotalx : iterate (A + C) q = n := by rw [iterate_add, hA, hC]
  have htotalz : iterate (B + D) q = n := by rw [iterate_add, hB, hD]
  have htime : A + C = B + D :=
    (hitting_time_iff_eq_first_of_no_return
      (firstHit_of_nonperiodic hnp htotalz)
      (fun r hr hret => hnp ⟨r, hr, hret⟩)).mp htotalx
  have hcounts := congrArg (fun t => oddCount t q) htime
  change oddCount (A + C) q = oddCount (B + D) q at hcounts
  rw [oddCount_add, hA, hCx, oddCount_add, hB, hDz] at hcounts
  have hAB : A = B := odd_endpoint_time_eq_of_oddCount_eq
    (by rw [hA]; exact hx.odd hnodd le_rfl)
    (by rw [hB]; exact hz.odd hnodd le_rfl) (by omega)
  rw [← hA, ← hB, hAB]

theorem ValidPrefix.eq_of_common_ancestor {n k q : ℕ}
    {x z : ℕ → ℕ} (hx : ValidPrefix n k x) (hz : ValidPrefix n k z)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hqx : ∃ A, iterate A q = x k) (hqz : ∃ B, iterate B q = z k) :
    ∀ i ≤ k, x i = z i := by
  intro i hi
  obtain ⟨A, hA⟩ := hqx
  obtain ⟨B, hB⟩ := hqz
  obtain ⟨C, hC, _⟩ := hx.suffix_hit_clock hi le_rfl
  obtain ⟨D, hD, _⟩ := hz.suffix_hit_clock hi le_rfl
  exact (hx.restrict hi).endpoint_eq_of_common_ancestor (hz.restrict hi) hnodd hnp
    ⟨A + C, by rw [iterate_add, hA, hC]⟩
    ⟨B + D, by rw [iterate_add, hB, hD]⟩

#print axioms ValidPrefix.suffix_hit_clock
#print axioms ValidPrefix.endpoint_eq_of_common_ancestor
#print axioms ValidPrefix.eq_of_common_ancestor

end CollatzCylinderPacking.Arithmetic.InverseDoob
