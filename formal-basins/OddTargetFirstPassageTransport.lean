import FirstPassageExpectationTransport

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem OddBarrierPassage.prefix_avoids_odd_target {q A N : ℕ} {M : ℝ}
    (h : OddBarrierPassage q A M) (hN : (N : ℝ) ≤ M) (hodd : N % 2 = 1) :
    ∀ i < A, iterate i q ≠ N := by
  intro i hi he
  have ho : iterate i q % 2 = 1 := by rw [he]; exact hodd
  have hh := h.prefix_high i hi ho
  rw [he] at hh
  linarith

/-- For an odd target, every successful barrier passage has the deterministic
weight bound, without any restriction on how small its landing is. -/
theorem firstHitWeight_uniform_barrier_stability_of_odd_target (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A q N : ℕ) (M : ℝ),
      0 < q → 1 ≤ M → (N : ℝ) ≤ M → N % 2 = 1 → OddBarrierPassage q A M →
      |firstHitWeight N q - firstHitWeight N (iterate A q)| ≤ C * M ^ (b - 1) := by
  obtain ⟨C, hC, htransport⟩ := firstHitWeight_uniform_prefix_transport b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro A q N M hq hM hN hodd hpass
  exact htransport A q N hq (hpass.prefix_avoids_odd_target hN hodd)
    hpass.prefix_injective M hM (fun i hi ho => (hpass.prefix_high i hi ho).le)

def SuccessfulOddBarrierLanding (q l : ℕ) (M : ℝ) : Prop :=
  ∃ A, OddBarrierPassage q A M ∧ iterate A q = l

/-- At odd targets, the exceptional set in the expectation transport only
needs to contain passage failures. -/
theorem firstHitWeight_odd_target_passage_expectation (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
      (p : ι → ℝ) (q : κ → ℝ) (startP : ι → ℕ) (startQ : κ → ℕ)
      (landingP : ι → η) (landingQ : κ → η) (value : η → ℕ)
      (badP : ι → Prop) (badQ : κ → Prop) (N : ℕ) (M : ℝ),
      (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ q i) →
      (∑ i, p i) = 1 → (∑ i, q i) = 1 →
      (∀ i, 0 < startP i) → (∀ i, 0 < startQ i) →
      1 ≤ M → (N : ℝ) ≤ M → N % 2 = 1 →
      (∀ i, ¬badP i → SuccessfulOddBarrierLanding (startP i) (value (landingP i)) M) →
      (∀ i, ¬badQ i → SuccessfulOddBarrierLanding (startQ i) (value (landingQ i)) M) →
      |finiteMean p (fun i => firstHitWeight N (startP i)) -
        finiteMean q (fun i => firstHitWeight N (startQ i))| ≤
          2 * C * M ^ (b - 1) + finiteBadMass p badP + finiteBadMass q badQ +
            ∑ z, |finitePushforward p landingP z - finitePushforward q landingQ z| := by
  obtain ⟨C, hC, hbound⟩ :=
    firstHitWeight_uniform_barrier_stability_of_odd_target b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro ι κ η _ _ _ p q startP startQ landingP landingQ value badP badQ N M
    hp hq hmassP hmassQ hstartP hstartQ hM hN hodd hpassP hpassQ
  have hP (i : ι) (hi : ¬badP i) :
      |firstHitWeight N (startP i) - firstHitWeight N (value (landingP i))| ≤
        C * M ^ (b - 1) := by
    obtain ⟨A, hA, hland⟩ := hpassP i hi
    have he := hbound A (startP i) N M (hstartP i) hM hN hodd hA
    simpa only [hland] using he
  have hQ (i : κ) (hi : ¬badQ i) :
      |firstHitWeight N (startQ i) - firstHitWeight N (value (landingQ i))| ≤
        C * M ^ (b - 1) := by
    obtain ⟨A, hA, hland⟩ := hpassQ i hi
    have he := hbound A (startQ i) N M (hstartQ i) hM hN hodd hA
    simpa only [hland] using he
  have he := finiteMean_two_passage_bound p q
    (fun i => firstHitWeight N (startP i)) (fun i => firstHitWeight N (startQ i))
    landingP landingQ (fun z => firstHitWeight N (value z)) badP badQ
    (C * M ^ (b - 1)) (C * M ^ (b - 1)) hp hq hmassP hmassQ
    (fun i => firstHitWeight_bounds N (startP i))
    (fun i => firstHitWeight_bounds N (startQ i))
    (fun z => firstHitWeight_bounds N (value z)) (by positivity) (by positivity) hP hQ
  convert he using 1
  ring

#print axioms OddBarrierPassage.prefix_avoids_odd_target
#print axioms firstHitWeight_uniform_barrier_stability_of_odd_target
#print axioms firstHitWeight_odd_target_passage_expectation

end CollatzCylinderPacking.Arithmetic
