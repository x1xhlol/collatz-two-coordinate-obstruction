import Erdos1135.Tao.Syracuse.FirstPassage

/-!
# Section 5 Pass-Location Step Back

This leaf records the deterministic event identity behind the corrected
Proposition 5.2 decomposition. It keeps the source window, probability, and
asymptotic estimates out of the first-passage kernel.
-/

namespace Erdos1135
namespace Tao

/-- The Syracuse orbit first hits `B` at time `n` and lands in `E`. -/
def taoSection5PassEventAtTime
    (B N n : ℕ) (E : Set ℕ) : Prop :=
  syracuseFirstHitAtMost B N n ∧ (syracuse^[n]) N ∈ E

/-- Step back `m` iterates from a first hit while preserving the exact landing
event. This is the typed correction used before partitioning the source event
by its unique first-hit time. -/
theorem taoSection5PassEventAtTime_iff_stepBack
    {B N n m : ℕ} (E : Set ℕ) (hm : m ≤ n) :
    taoSection5PassEventAtTime B N n E ↔
      (∀ k < n - m, B < (syracuse^[k]) N) ∧
        syracuseFirstHitAtMost B ((syracuse^[n - m]) N) m ∧
          (syracuse^[m]) ((syracuse^[n - m]) N) ∈ E := by
  have hiter :
      (syracuse^[m]) ((syracuse^[n - m]) N) = (syracuse^[n]) N := by
    rw [← Function.iterate_add_apply, Nat.add_comm m (n - m),
      Nat.sub_add_cancel hm]
  rw [taoSection5PassEventAtTime,
    syracuseFirstHitAtMost_iff_prefix_tail hm]
  constructor
  · rintro ⟨⟨hpre, htail⟩, hmem⟩
    exact ⟨hpre, htail, hiter.symm ▸ hmem⟩
  · rintro ⟨hpre, htail, hmem⟩
    exact ⟨⟨hpre, htail⟩, hiter ▸ hmem⟩

end Tao
end Erdos1135
