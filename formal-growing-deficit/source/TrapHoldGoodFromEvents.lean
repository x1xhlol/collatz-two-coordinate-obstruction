import TrapHoldIncrementPath
import TrapPMFEventTransport
import TrapGoodPathFromTube

/-! Separating the concrete good-path failure into increment and gated-tube failures. -/

set_option autoImplicit false

namespace Erdos1135.Tao
open CollatzResearch

def TrapHoldListTube (J : ℕ) (D : ℝ) : List TaoSection7RenewalPoint → Prop
  | [] => True
  | start :: full =>
      ∀ q ≤ full.length, ((taoSection7RenewalPathPoint start full q).j : ℕ) ≤ J →
        |((taoSection7RenewalPathPoint start full q).l : ℝ) -
          4 * (((taoSection7RenewalPathPoint start full q).j : ℕ) : ℝ)| ≤ D

theorem trap_holdList_good_of_increments_and_tube
    (n J H : ℕ) (V D : ℝ) (hs : List TaoSection7RenewalPoint)
    (hlen : hs.length = n / 2 + 1)
    (hincrements : ∀ h ∈ hs, TrapHoldIncrementGood (H : ℝ) V h)
    (htube : TrapHoldListTube J D hs) : trapHoldListGood n J H V D hs := by
  cases hs with
  | nil => simp at hlen
  | cons start full =>
      have hstart := hincrements start (by simp)
      have hsteps := trap_hold_increment_bounds_path H V start full
        (fun h hh => hincrements h (by simp [hh]))
      refine ⟨by simpa using hlen, ?_⟩
      exact ⟨by exact_mod_cast hstart.2.1,
        fun q hq => (hsteps q hq).1,
        fun q hq => (hsteps q hq).2.1,
        fun q hq => (hsteps q hq).2.2,
        htube⟩

theorem trap_holdList_bad_good_le_increment_add_tube
    (n J H : ℕ) (V D : ℝ) :
    trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1))
        (fun hs => ¬ trapHoldListGood n J H V D hs) ≤
      trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1))
        (fun hs => ¬ ∀ h ∈ hs, TrapHoldIncrementGood (H : ℝ) V h) +
      trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1))
        (fun hs => ¬ TrapHoldListTube J D hs) := by
  classical
  let BadIncrement := fun hs : List TaoSection7RenewalPoint =>
    ¬ ∀ h ∈ hs, TrapHoldIncrementGood (H : ℝ) V h
  let BadTube := fun hs => ¬ TrapHoldListTube J D hs
  have hmono := trap_pmf_event_mono_on_support (taoSection7HoldListPMF (n / 2 + 1))
    (fun hs => ¬ trapHoldListGood n J H V D hs)
    (fun hs => BadIncrement hs ∨ BadTube hs) ?_
  · exact hmono.trans (trap_pmf_event_le_add_of_cover _ _ BadIncrement BadTube (by tauto))
  · intro hs hmass hbad
    by_contra hne
    have hinc : ∀ h ∈ hs, TrapHoldIncrementGood (H : ℝ) V h := by
      simpa [BadIncrement] using (not_or.mp hne).1
    have htube : TrapHoldListTube J D hs := by
      simpa [BadTube] using (not_or.mp hne).2
    have hlen : hs.length = n / 2 + 1 := by
      by_contra hlen
      rw [taoSection7HoldListPMF_apply_eq_zero_of_length_ne (n / 2 + 1) hs hlen] at hmass
      exact hmass rfl
    exact hbad (trap_holdList_good_of_increments_and_tube n J H V D hs hlen hinc htube)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_holdList_bad_good_le_increment_add_tube
