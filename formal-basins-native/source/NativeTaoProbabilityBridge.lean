import ClosedOddWindowPassage
import Erdos1135.Tao.Probability.LogWindowPMF
import Erdos1135.Tao.Section3

set_option autoImplicit false

open scoped BigOperators
open CollatzCylinderPacking.Arithmetic
open CollatzCanonical.DirichletAbelian

namespace CollatzCanonical.NativeTao

open Erdos1135

theorem logNatWeight_eq_reciprocal (n : ℕ) : Tao.logNatWeight n = 1 / (n : ℝ) := by
  cases n with
  | zero => simp [Tao.logNatWeight]
  | succ n => simp [Tao.logNatWeight_succ, Tao.logWeight]

theorem closed_support_eq_native (s t : ℝ) :
    closedOddWindowValues s t = Tao.oddLogWindow ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊ := rfl

theorem closed_mass_eq_native {s t : ℝ} (hs : 0 ≤ s) :
    closedOddWindowMass s t =
      Tao.logFinsetMass (Tao.oddLogWindow ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊) := by
  unfold closedOddWindowMass
  rw [closedOddWindowNumerator_eq_inclusive_sum (fun _ => 1) hs]
  unfold Tao.logFinsetMass Tao.oddLogWindow
  apply Finset.sum_congr rfl
  intro n _
  exact (logNatWeight_eq_reciprocal n).symm

theorem closed_probability_eq_native {s t : ℝ} (hs : 0 ≤ s)
    (hmass : 0 < Tao.logFinsetMass (Tao.oddLogWindow ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊))
    (q : {n : ℕ // n ∈ closedOddWindowValues s t}) :
    (Tao.oddLogWindowPMF ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊ hmass q).toReal =
      closedOddWindowProbability s t q := by
  rw [Tao.oddLogWindowPMF_apply_toReal, logNatWeight_eq_reciprocal,
    ← closed_mass_eq_native hs]
  rfl

theorem native_closed_expectation (w : ℕ → ℝ) {s t : ℝ} (hs : 0 ≤ s)
    (hmass : 0 < Tao.logFinsetMass (Tao.oddLogWindow ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊)) :
    Tao.pmfExpectation (Tao.oddLogWindowPMF ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊ hmass)
      (fun q => w q.1) = closedOddWindowExpectation w s t := by
  rw [← finiteMean_closedOddWindowProbability w hs]
  unfold Tao.pmfExpectation finiteMean
  apply Finset.sum_congr rfl
  intro q _
  rw [closed_probability_eq_native hs hmass]

theorem finitePushforward_eq_native_map {ι η : Type*} [Fintype ι]
    (p : PMF ι) (landing : ι → η) (z : η) :
    finitePushforward (fun i => (p i).toReal) landing z = ((p.map landing) z).toReal := by
  classical
  simpa only [finitePushforward, Tao.pmfProb, Set.mem_setOf_eq] using
    Tao.pmfProb_singleton_eq_map_apply_toReal p landing z

theorem finiteBadMass_eq_native_probability {ι : Type*} [Fintype ι]
    (p : PMF ι) (bad : ι → Prop) :
    finiteBadMass (fun i => (p i).toReal) bad = Tao.pmfProb p {i | bad i} := by
  classical
  rfl

theorem finite_landing_fullL1_eq_native_TV {ι κ η : Type*}
    [Fintype ι] [Fintype κ] [Fintype η]
    (p : PMF ι) (q : PMF κ) (landingP : ι → η) (landingQ : κ → η) :
    (∑ z, |finitePushforward (fun i => (p i).toReal) landingP z -
      finitePushforward (fun i => (q i).toReal) landingQ z|) =
        Tao.taoTV (p.map landingP) (q.map landingQ) := by
  simp only [finitePushforward_eq_native_map, Tao.taoTV]

/-- Native finite Tao PMFs now feed directly into the actual first-hit-weight
transport theorem, with the native full-L1 landing-law convention. -/
theorem native_firstHitWeight_passage_expectation (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
      (p : PMF ι) (q : PMF κ) (startP : ι → ℕ) (startQ : κ → ℕ)
      (landingP : ι → η) (landingQ : κ → η) (value : η → ℕ)
      (badP : ι → Prop) (badQ : κ → Prop) (N : ℕ) (M : ℝ),
      (∀ i, 0 < startP i) → (∀ i, 0 < startQ i) → 1 ≤ M → (N : ℝ) ≤ M →
      (∀ i, ¬badP i → GoodOddBarrierLanding (startP i) (value (landingP i)) N M) →
      (∀ i, ¬badQ i → GoodOddBarrierLanding (startQ i) (value (landingQ i)) N M) →
      |Tao.pmfExpectation p (fun i => firstHitWeight N (startP i)) -
        Tao.pmfExpectation q (fun i => firstHitWeight N (startQ i))| ≤
          2 * C * M ^ (b - 1) + Tao.pmfProb p {i | badP i} + Tao.pmfProb q {i | badQ i} +
            Tao.taoTV (p.map landingP) (q.map landingQ) := by
  obtain ⟨C, hC, hbound⟩ := firstHitWeight_two_passage_expectation b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro ι κ η _ _ _ p q startP startQ landingP landingQ value badP badQ N M
    hstartP hstartQ hM hN hpassP hpassQ
  have he := hbound (fun i => (p i).toReal) (fun i => (q i).toReal)
    startP startQ landingP landingQ value badP badQ N M
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (Tao.pmf_sum_toReal p) (Tao.pmf_sum_toReal q) hstartP hstartQ hM hN hpassP hpassQ
  rw [finiteBadMass_eq_native_probability, finiteBadMass_eq_native_probability,
    finite_landing_fullL1_eq_native_TV] at he
  exact he

#print axioms native_closed_expectation
#print axioms finite_landing_fullL1_eq_native_TV
#print axioms native_firstHitWeight_passage_expectation

end CollatzCanonical.NativeTao
