import GeometricOddWindowDensity
import NativeTaoProbabilityBridge
import Erdos1135.Tao.Probability.LogWindowResidue

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.NativeTao
open Erdos1135.Tao CollatzCanonical.DirichletAbelian

noncomputable def oddEventWeight (G : Set TaoOddNat) (n : ℕ) : ℝ := by
  classical
  exact if ∃ hn : Odd n, (⟨n, hn⟩ : TaoOddNat) ∈ G then 1 else 0

theorem oddEventWeight_bounds (G : Set TaoOddNat) (n : ℕ) :
    0 ≤ oddEventWeight G n ∧ oddEventWeight G n ≤ 1 := by
  classical
  unfold oddEventWeight
  split_ifs <;> norm_num

theorem oddEventWeight_of_odd (G : Set TaoOddNat) (q : TaoOddNat) :
    oddEventWeight G q.1 = G.indicator (fun _ => (1 : ℝ)) q := by
  classical
  have he : (∃ h : Odd q.1, (⟨q.1, h⟩ : TaoOddNat) ∈ G) ↔ q ∈ G := by
    constructor
    · rintro ⟨_, h⟩; exact h
    · exact fun h => ⟨q.2, h⟩
  simp only [oddEventWeight, he, Set.indicator_apply]

/-- The event probability under the actual odd source PMF is exactly the
closed logarithmic-window expectation of its arithmetic indicator. -/
theorem native_odd_event_eq_closed_expectation (G : Set TaoOddNat)
    {s t : ℝ} (hs : 0 ≤ s)
    (hmass : 0 < logFinsetMass (oddLogWindow ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊)) :
    ((oddLogWindowOddNatPMF ⌈Real.exp s⌉₊ ⌊Real.exp t⌋₊ hmass).toOuterMeasure G).toReal =
      closedOddWindowExpectation (oddEventWeight G) s t := by
  classical
  rw [oddLogWindowOddNatPMF, PMF.toOuterMeasure_map_apply,
    ← pmfProb_eq_toOuterMeasure_toReal, ← native_closed_expectation _ hs hmass]
  unfold pmfProb pmfExpectation
  apply Finset.sum_congr rfl
  intro q _
  have he := oddEventWeight_of_odd G (oddLogWindowValueToOddNat q)
  change (if oddLogWindowValueToOddNat q ∈ G then _ else 0) = _
  change oddEventWeight G q.1 = _ at he
  dsimp only
  rw [he]
  by_cases hq : oddLogWindowValueToOddNat q ∈ G <;> simp [hq]

/-- Actual native probability estimates on the geometric passage windows
imply an absolute, rather than basin-relative, logarithmic-density bound. -/
theorem native_odd_event_logarithmic_mean_zero (G : Set TaoOddNat) {a : ℝ}
    (ha : 1 < a)
    (hsmall : ∀ d : ℝ, 0 < d → ∃ M : ℝ, 1 < M ∧
      ∀ᶠ j : ℕ in atTop,
        ∃ hmass : 0 < logFinsetMass (oddLogWindow
          ⌈Real.exp (a ^ (j + 1) * Real.log M)⌉₊
          ⌊Real.exp (a ^ (j + 2) * Real.log M)⌋₊),
        ((oddLogWindowOddNatPMF
          ⌈Real.exp (a ^ (j + 1) * Real.log M)⌉₊
          ⌊Real.exp (a ^ (j + 2) * Real.log M)⌋₊ hmass).toOuterMeasure G).toReal ≤ d) :
    Tendsto (fun t : ℝ => oddLogarithmicCumulative (oddEventWeight G) t / t)
      atTop (𝓝 0) := by
  apply odd_logarithmic_mean_zero_of_ladder_windows
    (fun n => (oddEventWeight_bounds G n).1)
    (fun n => (oddEventWeight_bounds G n).2) ha
  intro d hd
  obtain ⟨M, hM, hstep⟩ := hsmall d hd
  refine ⟨M, hM, ?_⟩
  filter_upwards [hstep] with j hj
  obtain ⟨hmass, hp⟩ := hj
  have hs : 0 ≤ a ^ (j + 1) * Real.log M :=
    mul_nonneg (pow_nonneg (by linarith) _) (Real.log_pos hM).le
  rwa [native_odd_event_eq_closed_expectation G hs hmass] at hp

end CollatzCanonical.NativeTao
