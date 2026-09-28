import Erdos1135.Tao.Density.LogDensity
import Erdos1135.Tao.Syracuse.Defs

/-!
# Syracuse Statement Surface For The Tao Lane

This module records theorem-shaped Syracuse targets from Tao's Section 1.2.  The growth
hypothesis is over odd inputs, represented through the ambient function `m ↦ 2*m+1`.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

/-- The Syracuse orbit of `N` eventually hits below the real threshold `b`. -/
def syracuseHitsBelowReal (N : ℕ) (b : ℝ) : Prop :=
  ∃ m : ℕ, ((syracuse^[m]) N : ℝ) < b

/-- A real-valued function tends to `+∞` along the odd positive naturals. -/
def GrowsOnOddsToInfinity (f : ℕ → ℝ) : Prop :=
  Tendsto (fun m : ℕ => f (2 * m + 1)) atTop atTop

/--
The ambient logarithmic-density target corresponding to Tao's Theorem 1.6.  This is a `Prop`
target, not an asserted theorem.
-/
def TaoSyracuseAmbientStatement : Prop :=
  ∀ f : ℕ → ℝ,
    GrowsOnOddsToInfinity f →
      HasLogDensity {N : ℕ | Odd N ∧ syracuseHitsBelowReal N (f N)} (1 / 2)

/-- A finite natural threshold below a real threshold gives a real Syracuse hit-below witness. -/
theorem syracuseHitsAtMost_to_hitsBelowReal {N B : ℕ} {b : ℝ}
    (h : syracuseHitsAtMost N B) (hb : (B : ℝ) < b) :
    syracuseHitsBelowReal N b := by
  rcases h with ⟨m, hm⟩
  exact ⟨m, lt_of_le_of_lt (by exact_mod_cast hm) hb⟩

end Tao
end Erdos1135
