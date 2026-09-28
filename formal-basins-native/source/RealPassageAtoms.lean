import CanonicalPassageAtoms
import RealCanonicalClockRates

set_option autoImplicit false
open Filter Topology

namespace CollatzPassageAtoms
open Erdos1135.Tao CollatzClockAudit

/-- Moving to the actual real source window costs only the checked floor-window
perturbation error; the totalized point event is exactly the same at the floor. -/
theorem eventually_real_passage_atom_floor_bound :
    ∀ᶠ x : ℝ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)),
      ∀ hx : 1 ≤ x, ∀ m : ℕ,
      ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
        hmass).toOuterMeasure
        {q : TaoOddNat | (syracusePassLocationRealFloorOrOne x q.1 hx).val = m}).toReal ≤
          5 * ((Nat.floor x : ℕ) : ℝ) ^ (-(1 / 12800000 : ℝ)) +
            taoProp111FloorSourceError (Nat.floor x) := by
  have hf : Tendsto (fun x : ℝ => Nat.floor x) atTop atTop := tendsto_nat_floor_atTop
  filter_upwards [eventually_taoProp111RealFloorWindowMassFacts,
    hf.eventually eventually_canonical_passage_atom_polynomial] with x facts hatom
  intro branch hmass hx m
  let G : Set TaoOddNat := {q | (syracusePassLocationRealFloorOrOne x q.1 hx).val = m}
  have hp := real_source_event_probability_le_floor_add facts branch hmass G
  have hn := hatom branch (floor_clock_source_mass_pos facts branch)
    (one_le_floor_of_one_le hx) m
  exact hp.trans (add_le_add hn le_rfl)

/-- Every point mass of the actual real-threshold first-passage law is
polynomially small, uniformly over both full source windows and all targets.
The atom at one includes every failed passage. -/
theorem eventually_real_passage_atom_polynomial :
    ∀ᶠ x : ℝ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)),
      ∀ hx : 1 ≤ x, ∀ m : ℕ,
      ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
        hmass).toOuterMeasure
        {q : TaoOddNat | (syracusePassLocationRealFloorOrOne x q.1 hx).val = m}).toReal ≤
          200000 * x ^ (-(1 / 12800000 : ℝ)) := by
  filter_upwards [eventually_real_passage_atom_floor_bound,
    eventually_taoProp111RealFloorWindowMassFacts, eventually_ge_atTop (2 : ℝ)]
    with x hprob facts hx
  intro branch hmass hx1 m
  have hf := floor_rpow_neg_le_two_mul hx
    (c := (1 / 12800000 : ℝ)) (by norm_num) (by norm_num)
  have he := floorSourceError_le_real_rpow hx
    (show 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ) by linarith [facts.log_floor_large])
    (c := (1 / 12800000 : ℝ)) (by norm_num) (by norm_num)
  have hp := hprob branch hmass hx1 m
  have hn : 0 ≤ x ^ (-(1 / 12800000 : ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith

end CollatzPassageAtoms
