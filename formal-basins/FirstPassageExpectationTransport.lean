import FiniteObservableTransport

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- A successful odd-barrier landing above the target, with an actual shortcut
orbit prefix as its witness. -/
def GoodOddBarrierLanding (q l N : ℕ) (M : ℝ) : Prop :=
  ∃ A, OddBarrierPassage q A M ∧ iterate A q = l ∧ N < l

/-- The deterministic orbit estimate gives a uniform bound on the expectation
error under an arbitrary finite probability distribution. -/
theorem firstHitWeight_finite_passage_transport (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] (p : ι → ℝ)
      (start landing : ι → ℕ) (bad : ι → Prop) (N : ℕ) (M : ℝ),
      (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 → (∀ i, 0 < start i) →
      1 ≤ M → (N : ℝ) ≤ M →
      (∀ i, ¬bad i → GoodOddBarrierLanding (start i) (landing i) N M) →
      |finiteMean p (fun i => firstHitWeight N (start i)) -
        finiteMean p (fun i => firstHitWeight N (landing i))| ≤
          C * M ^ (b - 1) + finiteBadMass p bad := by
  obtain ⟨C, hC, hbound⟩ := firstHitWeight_uniform_barrier_stability b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro ι _ p start landing bad N M hp hmass hstart hM hN hpass
  apply finiteMean_transport p _ _ bad (C * M ^ (b - 1)) hp hmass
    (fun i => firstHitWeight_bounds N (start i))
    (fun i => firstHitWeight_bounds N (landing i)) (by positivity)
  intro i hi
  obtain ⟨A, hA, hland, hgt⟩ := hpass i hi
  have he := hbound A (start i) N M (hstart i) hM hN hA (by simpa [hland] using hgt)
  simpa only [hland] using he

/-- For the actual first-hit observable, two passage laws give an expectation
comparison with explicit deterministic, exceptional-set, and full L1 errors. -/
theorem firstHitWeight_two_passage_expectation (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
      (p : ι → ℝ) (q : κ → ℝ) (startP : ι → ℕ) (startQ : κ → ℕ)
      (landingP : ι → η) (landingQ : κ → η) (value : η → ℕ)
      (badP : ι → Prop) (badQ : κ → Prop) (N : ℕ) (M : ℝ),
      (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ q i) →
      (∑ i, p i) = 1 → (∑ i, q i) = 1 →
      (∀ i, 0 < startP i) → (∀ i, 0 < startQ i) → 1 ≤ M → (N : ℝ) ≤ M →
      (∀ i, ¬badP i → GoodOddBarrierLanding (startP i) (value (landingP i)) N M) →
      (∀ i, ¬badQ i → GoodOddBarrierLanding (startQ i) (value (landingQ i)) N M) →
      |finiteMean p (fun i => firstHitWeight N (startP i)) -
        finiteMean q (fun i => firstHitWeight N (startQ i))| ≤
          2 * C * M ^ (b - 1) + finiteBadMass p badP + finiteBadMass q badQ +
            ∑ z, |finitePushforward p landingP z - finitePushforward q landingQ z| := by
  obtain ⟨C, hC, hbound⟩ := firstHitWeight_uniform_barrier_stability b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro ι κ η _ _ _ p q startP startQ landingP landingQ value badP badQ N M
    hp hq hmassP hmassQ hstartP hstartQ hM hN hpassP hpassQ
  have hP (i : ι) (hi : ¬badP i) :
      |firstHitWeight N (startP i) - firstHitWeight N (value (landingP i))| ≤
        C * M ^ (b - 1) := by
    obtain ⟨A, hA, hland, hgt⟩ := hpassP i hi
    have he := hbound A (startP i) N M (hstartP i) hM hN hA
      (by simpa [hland] using hgt)
    simpa only [hland] using he
  have hQ (i : κ) (hi : ¬badQ i) :
      |firstHitWeight N (startQ i) - firstHitWeight N (value (landingQ i))| ≤
        C * M ^ (b - 1) := by
    obtain ⟨A, hA, hland, hgt⟩ := hpassQ i hi
    have he := hbound A (startQ i) N M (hstartQ i) hM hN hA
      (by simpa [hland] using hgt)
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

#print axioms firstHitWeight_finite_passage_transport
#print axioms firstHitWeight_two_passage_expectation

end CollatzCylinderPacking.Arithmetic
