import Erdos1135.Tao.Syracuse.FirstPassage
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Real-Threshold Syracuse First Passage

This module records the deterministic floor bridge from Tao's real threshold
`T_x`/`Pass_x` notation to the existing natural-threshold first-passage API.
It deliberately does not define the probabilistic `Pass_x` law.
-/

namespace Erdos1135
namespace Tao

/-- The Syracuse orbit of `N` eventually hits at most the real threshold `x`. -/
def syracuseHitsAtMostReal (N : ℕ) (x : ℝ) : Prop :=
  ∃ m : ℕ, ((syracuse^[m]) N : ℝ) ≤ x

/-- The Syracuse orbit first hits the real threshold `x` at time `n`. -/
def syracuseFirstHitAtMostReal (x : ℝ) (N n : ℕ) : Prop :=
  ((syracuse^[n]) N : ℝ) ≤ x ∧
    ∀ k < n, x < ((syracuse^[k]) N : ℝ)

/-- The first-passage location relation at real threshold `x`. -/
def syracusePassLocationAtMostReal (x : ℝ) (N M : ℕ) : Prop :=
  ∃ n, syracuseFirstHitAtMostReal x N n ∧ M = (syracuse^[n]) N

/-- For nonnegative real thresholds, a natural value above the floor is above the threshold. -/
theorem floor_lt_nat_iff_real_lt {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    Nat.floor x < n ↔ x < (n : ℝ) :=
  Nat.floor_lt hx

/--
Real-threshold Syracuse hits are exactly natural-threshold hits at
`Nat.floor x`, provided `x` is nonnegative.
-/
theorem syracuseHitsAtMostReal_iff_floor {N : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    syracuseHitsAtMostReal N x ↔ syracuseHitsAtMost N (Nat.floor x) := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (Nat.le_floor_iff hx).2 hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (Nat.le_floor_iff hx).1 hm⟩

/--
Real first-hit predicates reduce to the existing natural-threshold first-hit
predicate at `Nat.floor x`.
-/
theorem syracuseFirstHitAtMostReal_iff_floor {x : ℝ} {N n : ℕ}
    (hx : 0 ≤ x) :
    syracuseFirstHitAtMostReal x N n ↔
      syracuseFirstHitAtMost (Nat.floor x) N n := by
  constructor
  · intro h
    constructor
    · exact (Nat.le_floor_iff hx).2 h.1
    · intro k hk
      exact (Nat.floor_lt hx).2 (h.2 k hk)
  · intro h
    constructor
    · exact (Nat.le_floor_iff hx).1 h.1
    · intro k hk
      exact (Nat.floor_lt hx).1 (h.2 k hk)

/--
Real first-passage locations reduce to the existing natural-threshold
pass-location relation at `Nat.floor x`.
-/
theorem syracusePassLocationAtMostReal_iff_floor {x : ℝ} {N M : ℕ}
    (hx : 0 ≤ x) :
    syracusePassLocationAtMostReal x N M ↔
      syracusePassLocationAtMost (Nat.floor x) N M := by
  constructor
  · rintro ⟨n, hn, hM⟩
    exact ⟨n, (syracuseFirstHitAtMostReal_iff_floor hx).1 hn, hM⟩
  · rintro ⟨n, hn, hM⟩
    exact ⟨n, (syracuseFirstHitAtMostReal_iff_floor hx).2 hn, hM⟩

end Tao
end Erdos1135
