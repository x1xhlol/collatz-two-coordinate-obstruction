import TrapRawPrefixProbability
import TrapHoldGoodFromEvents
import TrapSupportedHoldTube

/-! Finite probability bound for the concrete good event on the original iid Hold list. -/

set_option autoImplicit false

namespace Erdos1135.Tao
open CollatzResearch

theorem trap_holdList_bad_tube_probability_le
    (J N : ℕ) (hJ : 0 < J) (hJN : J ≤ N) (D : ℝ) (hD : 0 < D) :
    trapPMFEvent (taoSection7HoldListPMF N) (fun hs => ¬ TrapHoldListTube J D hs) ≤
      ((2 * J : ℕ) : ℝ) * (2 * Real.exp
        (-min (D ^ 2 / (32 * ((2 * J : ℕ) : ℝ))) (D / 8))) := by
  classical
  rw [← taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq N, trap_pmf_event_map]
  have hcompare :
      trapPMFEvent (taoSection7HoldSourcePrefixListPMF N)
          (fun xs => ¬ TrapHoldListTube J D
            (xs.map fun y => taoSection7HoldPointOfPrefix y.1 y.2)) ≤
        trapPMFEvent (taoSection7HoldSourcePrefixListPMF N)
          (fun xs => ¬ TrapPascalPrefixGood J D (taoSection7RawPrefixOfHoldBlocks J xs)) := by
    apply trap_pmf_event_mono_on_support
    intro xs hmass hbad
    by_contra hnot
    have hprefix : TrapPascalPrefixGood J D (taoSection7RawPrefixOfHoldBlocks J xs) :=
      hnot
    have hsupp := trap_holdSourceList_toReal_ne_zero_support hmass
    apply hbad
    cases hmap : xs.map (fun y => taoSection7HoldPointOfPrefix y.1 y.2) with
    | nil => trivial
    | cons start full =>
        intro q hq hj
        exact trap_supported_hold_source_tube J D xs
          (fun y hy => (hsupp.2 y hy).1) hprefix start full hmap q hq hj
  exact hcompare.trans (trap_hold_source_bad_prefix_probability_le J N hJ hJN D hD)

theorem trap_holdList_bad_good_probability_le
    (n J H : ℕ) (hJ : 0 < J) (hJn : 2 * J ≤ n) (V D : ℝ) (hD : 0 < D) :
    trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1))
        (fun hs => ¬ trapHoldListGood n J H V D hs) ≤
      ((n / 2 + 1 : ℕ) : ℝ) *
          (15 * Real.exp (-Real.log (21 / 20 : ℝ) * min (H : ℝ) V)) +
        ((2 * J : ℕ) : ℝ) * (2 * Real.exp
          (-min (D ^ 2 / (32 * ((2 * J : ℕ) : ℝ))) (D / 8))) := by
  exact (trap_holdList_bad_good_le_increment_add_tube n J H V D).trans
    (add_le_add (trap_holdList_bad_increment_probability_le (n / 2 + 1) (H : ℝ) V)
      (trap_holdList_bad_tube_probability_le J (n / 2 + 1) hJ (by omega) D hD))

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_holdList_bad_tube_probability_le
#print axioms Erdos1135.Tao.trap_holdList_bad_good_probability_le
