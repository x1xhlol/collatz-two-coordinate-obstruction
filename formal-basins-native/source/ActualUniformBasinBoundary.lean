import NoSmallAncestorAtom
import UniformBottomPassageAtoms
import GeometricWindowUpperMean
import NativeTargetClockDensity
import ActualBasinDensity

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.NativeTao
open Erdos1135.Tao CollatzClockAudit CollatzCanonical.DirichletAbelian
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

def basinOddSourceEvent (v : ℕ) : Set TaoOddNat :=
  {q | ∃ K, iterate K q.val = v}

theorem oddEventWeight_basinOddSourceEvent (v q : ℕ) :
    oddEventWeight (basinOddSourceEvent v) q = oddBasinIndicator v q := by
  classical
  have he : (∃ hq : Odd q, (⟨q, hq⟩ : TaoOddNat) ∈ basinOddSourceEvent v) ↔
      q % 2 = 1 ∧ ∃ K, iterate K q = v := by
    constructor
    · rintro ⟨hq, hhit⟩
      exact ⟨Nat.odd_iff.mp hq, hhit⟩
    · rintro ⟨hq, hhit⟩
      exact ⟨Nat.odd_iff.mpr hq, hhit⟩
  simp only [oddEventWeight, he, oddBasinIndicator, basinIndicator]
  by_cases hq : q % 2 = 1 <;> by_cases hhit : ∃ K, iterate K q = v <;> simp [hq, hhit]

theorem odd_basin_event_mean (v : ℕ) :
    Tendsto (fun t : ℝ => oddLogarithmicCumulative (oddEventWeight (basinOddSourceEvent v)) t / t)
      atTop (𝓝 (actualBasinDensity v / 2)) := by
  have he (t : ℝ) : oddLogarithmicCumulative (oddEventWeight (basinOddSourceEvent v)) t =
      logarithmicCumulative (oddBasinIndicator v) t := by
    unfold oddLogarithmicCumulative
    congr 1
    funext q
    rw [oddEventWeight_basinOddSourceEvent]
    unfold oddBasinIndicator
    split_ifs <;> rfl
  simp_rw [he]
  exact actual_basin_odd_mean v

theorem basin_density_le_of_ladder_probability_bound (v : ℕ) {M d : ℝ}
    (hM : 1 < M) (hd : 0 ≤ d)
    (hprob : ∀ j : ℕ,
      ∃ hmass : 0 < logFinsetMass (oddLogWindow
        (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha)),
      ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha) hmass).toOuterMeasure
        (basinOddSourceEvent v)).toReal ≤ d) :
    actualBasinDensity v ≤ 2 * (d * taoAlpha) := by
  have hsmall : ∀ᶠ j : ℕ in atTop,
      closedOddWindowExpectation (oddEventWeight (basinOddSourceEvent v))
        (taoAlpha ^ (j + 1) * Real.log M) (taoAlpha ^ (j + 2) * Real.log M) ≤ d := by
    apply Filter.Eventually.of_forall
    intro j
    obtain ⟨hmass, hp⟩ := hprob j
    obtain ⟨hl, hu⟩ := clock_ladder_source_endpoints (by linarith : 0 < M) j
    have hmass' : 0 < logFinsetMass (oddLogWindow
        ⌈Real.exp (taoAlpha ^ (j + 1) * Real.log M)⌉₊
        ⌊Real.exp (taoAlpha ^ (j + 2) * Real.log M)⌋₊) := by
      rw [← hl, ← hu]
      exact hmass
    rw [native_odd_probability_congr (basinOddSourceEvent v) hl hu hmass hmass'] at hp
    have hs : 0 ≤ taoAlpha ^ (j + 1) * Real.log M :=
      mul_nonneg (pow_nonneg (by linarith [taoAlpha_one_lt]) _) (Real.log_pos hM).le
    rwa [native_odd_event_eq_closed_expectation (basinOddSourceEvent v) hs hmass'] at hp
  have h := odd_logarithmic_mean_le_of_ladder_windows
    (fun q => (oddEventWeight_bounds (basinOddSourceEvent v) q).1)
    (fun q => (oddEventWeight_bounds (basinOddSourceEvent v) q).2)
    taoAlpha_one_lt hM hd hsmall (odd_basin_event_mean v)
  linarith

/-- One quantitative error controls every positive target basin with no
small ancestor. The cutoff and constants do not depend on the target. -/
theorem exists_uniform_noSmallAncestor_basin_bound :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ M : ℝ in atTop,
      ∀ v : ℕ, 0 < v → NoSmallAncestor v M →
        actualBasinDensity v ≤ C * (Real.log M) ^ (-c) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_uniform_bottom_passage_atom_log_rate
  have ha0 : 0 < taoAlpha := lt_trans zero_lt_one taoAlpha_one_lt
  refine ⟨2 * taoAlpha * C, c, by positivity, hc, ?_⟩
  filter_upwards [hbound] with M hMbound
  obtain ⟨hM, hprob⟩ := hMbound
  intro v hv hno
  obtain ⟨m, hm⟩ := noSmallAncestor_odd_basin_in_passage_atom hv hM.le hno
  have hd : 0 ≤ C * (Real.log M) ^ (-c) :=
    mul_nonneg hC (Real.rpow_nonneg (Real.log_pos hM).le _)
  have h := basin_density_le_of_ladder_probability_bound v hM hd (by
    intro j
    obtain ⟨hmass, hj⟩ := hprob j
    refine ⟨hmass, ?_⟩
    apply le_trans _ (hj m)
    apply pmf_outer_probability_mono_support
    intro q hq
    exact hm q.val q.property hq.1)
  convert h using 1
  ring

#print axioms basin_density_le_of_ladder_probability_bound
#print axioms exists_uniform_noSmallAncestor_basin_bound

end CollatzCanonical.NativeTao
