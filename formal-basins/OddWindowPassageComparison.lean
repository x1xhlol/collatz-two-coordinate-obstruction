import OddWindowFiniteProbability

set_option autoImplicit false

open scoped BigOperators
open CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.DirichletAbelian

/-- The actual odd harmonic-window expectations inherit the first-passage
comparison, with normalized reciprocal source weights constructed explicitly. -/
theorem oddWindow_firstHitWeight_passage_comparison (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η : Type*} [Fintype η] (sP tP sQ tQ : ℝ)
      (landingP : {n : ℕ // n ∈ oddWindowIndices sP tP} → η)
      (landingQ : {n : ℕ // n ∈ oddWindowIndices sQ tQ} → η) (value : η → ℕ)
      (badP : {n : ℕ // n ∈ oddWindowIndices sP tP} → Prop)
      (badQ : {n : ℕ // n ∈ oddWindowIndices sQ tQ} → Prop) (N : ℕ) (M : ℝ),
      sP ≤ tP → sQ ≤ tQ → 0 < oddWindowMass sP tP → 0 < oddWindowMass sQ tQ →
      1 ≤ M → (N : ℝ) ≤ M → N % 2 = 1 →
      (∀ i, ¬badP i → SuccessfulOddBarrierLanding (i.1 + 1) (value (landingP i)) M) →
      (∀ i, ¬badQ i → SuccessfulOddBarrierLanding (i.1 + 1) (value (landingQ i)) M) →
      |oddWindowExpectation (firstHitWeight N) sP tP -
        oddWindowExpectation (firstHitWeight N) sQ tQ| ≤
          2 * C * M ^ (b - 1) + finiteBadMass (oddWindowProbability sP tP) badP +
            finiteBadMass (oddWindowProbability sQ tQ) badQ +
            ∑ z, |finitePushforward (oddWindowProbability sP tP) landingP z -
              finitePushforward (oddWindowProbability sQ tQ) landingQ z| := by
  obtain ⟨C, hC, hbound⟩ := firstHitWeight_odd_target_passage_expectation b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro η _ sP tP sQ tQ landingP landingQ value badP badQ N M
    hstP hstQ hmassP hmassQ hM hN hodd hpassP hpassQ
  have he := hbound (oddWindowProbability sP tP) (oddWindowProbability sQ tQ)
    (fun i => i.1 + 1) (fun i => i.1 + 1) landingP landingQ value badP badQ N M
    (oddWindowProbability_nonneg hmassP) (oddWindowProbability_nonneg hmassQ)
    (oddWindowProbability_mass hstP hmassP) (oddWindowProbability_mass hstQ hmassQ)
    (fun i => Nat.succ_pos i.1) (fun i => Nat.succ_pos i.1) hM hN hodd hpassP hpassQ
  rw [finiteMean_oddWindowProbability _ hstP, finiteMean_oddWindowProbability _ hstQ] at he
  exact he

#print axioms oddWindow_firstHitWeight_passage_comparison

end CollatzCanonical.DirichletAbelian
