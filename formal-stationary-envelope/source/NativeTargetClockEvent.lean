import NativeTargetClockRemainder
import GlobalBarrierClock

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao

open Erdos1135.Tao CollatzCylinderPacking CollatzCylinderPacking.Arithmetic CollatzClockAudit

/-- Actual basin starts whose target odd clock has a relative error
larger than ε about log(q)/log(4/3). -/
def actualTargetClockBadEvent (N : ℕ) (ε : ℝ) : Set TaoOddNat :=
  {q | (∃ K, iterate K q.1 = N) ∧
    ε * Real.log (q.1 : ℝ) / clockDrift <
      |(firstHitOddDepth N q.1 : ℝ) - Real.log (q.1 : ℝ) / clockDrift|}

theorem eventually_global_barrier_implies_target_clock (N : ℕ) {M ε : ℝ}
    (hM : 1 ≤ M) (hN : (N : ℝ) ≤ M) (hNsqrt : (N : ℝ) ≤ M ^ (1 / 2 : ℝ))
    (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ hq : Odd q,
      (⟨q, hq⟩ : TaoOddNat) ∈ globalBarrierClockEvent M →
        (⟨q, hq⟩ : TaoOddNat) ∉ actualTargetClockBadEvent N ε := by
  let R : ℝ := boundedTargetOddRemainder N ⌊M⌋₊
  have hsmall := eventually_sublinear_clock_error
    (p := (3 / 5 : ℝ)) (C := globalClockErrorConstant)
    (D := R + |Real.log M / clockDrift|) (by norm_num) hε
  filter_upwards [hsmall] with q hqsmall
  intro hq hgood hbad
  obtain ⟨τ, hfirst, hclock, hlarge⟩ := hgood
  have hland : N < (syracuse^[τ]) q := by
    exact_mod_cast lt_of_le_of_lt hNsqrt hlarge
  obtain ⟨hτk, hrem⟩ := native_first_passage_bounded_target_remainder
    (by linarith : 0 ≤ M) hq hfirst hN hland hbad.1
  have hremR : (firstHitOddDepth N q : ℝ) - τ ≤ R := by
    dsimp only [R]
    exact_mod_cast hrem
  have hrough := clock_error_with_bounded_remainder hτk hremR hclock
  have hbound : |(firstHitOddDepth N q : ℝ) - Real.log (q : ℝ) / clockDrift| ≤
      ε * Real.log (q : ℝ) / clockDrift := by
    linarith
  exact (not_lt_of_ge hbound) hbad.2

#print axioms eventually_global_barrier_implies_target_clock

end CollatzCanonical.NativeTao
