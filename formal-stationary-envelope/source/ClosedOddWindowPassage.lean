import ClosedOddWindowComparison

set_option autoImplicit false

open scoped BigOperators
open CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.DirichletAbelian

/-- The inclusive odd natural source support attached to real logarithmic endpoints. -/
noncomputable def closedOddWindowValues (s t : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊).filter (fun q => q % 2 = 1)

noncomputable def closedOddWindowProbability (s t : ℝ)
    (q : {n : ℕ // n ∈ closedOddWindowValues s t}) : ℝ :=
  (1 / (q.1 : ℝ)) / closedOddWindowMass s t

theorem closedOddWindowValues_pos {s t : ℝ}
    (q : {n : ℕ // n ∈ closedOddWindowValues s t}) : 0 < q.1 := by
  have ho : q.1 % 2 = 1 := (Finset.mem_filter.mp q.2).2
  omega

theorem closedOddWindowProbability_nonneg {s t : ℝ}
    (hmass : 0 < closedOddWindowMass s t)
    (q : {n : ℕ // n ∈ closedOddWindowValues s t}) :
    0 ≤ closedOddWindowProbability s t q := by
  unfold closedOddWindowProbability
  positivity

theorem closedOddWindowProbability_mass {s t : ℝ} (hs : 0 ≤ s)
    (hmass : 0 < closedOddWindowMass s t) :
    ∑ q, closedOddWindowProbability s t q = 1 := by
  classical
  have he : (∑ q : {n : ℕ // n ∈ closedOddWindowValues s t}, (1 : ℝ) / (q.1 : ℝ)) =
      closedOddWindowMass s t := by
    unfold closedOddWindowMass
    rw [closedOddWindowNumerator_eq_inclusive_sum (fun _ => 1) hs]
    exact Finset.sum_coe_sort _ (fun q : ℕ => (1 : ℝ) / q)
  unfold closedOddWindowProbability
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simp only [← div_eq_mul_inv]
  rw [he, div_self hmass.ne']

theorem finiteMean_closedOddWindowProbability (w : ℕ → ℝ) {s t : ℝ} (hs : 0 ≤ s) :
    finiteMean (closedOddWindowProbability s t) (fun q => w q.1) =
      closedOddWindowExpectation w s t := by
  classical
  unfold finiteMean closedOddWindowProbability closedOddWindowExpectation
  have he (q : {n : ℕ // n ∈ closedOddWindowValues s t}) :
      (1 / (q.1 : ℝ)) / closedOddWindowMass s t * w q.1 =
        (w q.1 / (q.1 : ℝ)) * (closedOddWindowMass s t)⁻¹ := by ring
  simp_rw [he]
  have hsum : (∑ q : {n : ℕ // n ∈ closedOddWindowValues s t}, w q.1 / (q.1 : ℝ)) =
      closedOddWindowNumerator w s t := by
    rw [closedOddWindowNumerator_eq_inclusive_sum w hs]
    exact Finset.sum_coe_sort _ (fun q : ℕ => w q / q)
  rw [← Finset.sum_mul, hsum, div_eq_mul_inv]

/-- Every target admits the actual inclusive-window comparison when the
successful passage lands above that target. The exceptional events can contain
both failures and small landings. -/
theorem closedOddWindow_firstHitWeight_passage_comparison (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η : Type*} [Fintype η] (sP tP sQ tQ : ℝ)
      (landingP : {n : ℕ // n ∈ closedOddWindowValues sP tP} → η)
      (landingQ : {n : ℕ // n ∈ closedOddWindowValues sQ tQ} → η) (value : η → ℕ)
      (badP : {n : ℕ // n ∈ closedOddWindowValues sP tP} → Prop)
      (badQ : {n : ℕ // n ∈ closedOddWindowValues sQ tQ} → Prop) (N : ℕ) (M : ℝ),
      0 ≤ sP → 0 ≤ sQ → 0 < closedOddWindowMass sP tP → 0 < closedOddWindowMass sQ tQ →
      1 ≤ M → (N : ℝ) ≤ M →
      (∀ q, ¬badP q → GoodOddBarrierLanding q.1 (value (landingP q)) N M) →
      (∀ q, ¬badQ q → GoodOddBarrierLanding q.1 (value (landingQ q)) N M) →
      |closedOddWindowExpectation (firstHitWeight N) sP tP -
        closedOddWindowExpectation (firstHitWeight N) sQ tQ| ≤
          2 * C * M ^ (b - 1) + finiteBadMass (closedOddWindowProbability sP tP) badP +
            finiteBadMass (closedOddWindowProbability sQ tQ) badQ +
            ∑ z, |finitePushforward (closedOddWindowProbability sP tP) landingP z -
              finitePushforward (closedOddWindowProbability sQ tQ) landingQ z| := by
  obtain ⟨C, hC, hbound⟩ := firstHitWeight_two_passage_expectation b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro η _ sP tP sQ tQ landingP landingQ value badP badQ N M
    hsP hsQ hmassP hmassQ hM hN hpassP hpassQ
  have he := hbound (closedOddWindowProbability sP tP) (closedOddWindowProbability sQ tQ)
    (fun q => q.1) (fun q => q.1) landingP landingQ value badP badQ N M
    (closedOddWindowProbability_nonneg hmassP) (closedOddWindowProbability_nonneg hmassQ)
    (closedOddWindowProbability_mass hsP hmassP) (closedOddWindowProbability_mass hsQ hmassQ)
    closedOddWindowValues_pos closedOddWindowValues_pos hM hN hpassP hpassQ
  rw [finiteMean_closedOddWindowProbability _ hsP, finiteMean_closedOddWindowProbability _ hsQ] at he
  exact he

#print axioms closedOddWindowProbability_mass
#print axioms finiteMean_closedOddWindowProbability
#print axioms closedOddWindow_firstHitWeight_passage_comparison

end CollatzCanonical.DirichletAbelian
