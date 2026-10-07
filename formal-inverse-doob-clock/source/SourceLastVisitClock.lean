import SourceSuffixPrefix
import LastVisitGeometry
import ShortcutOddEndpoints
import NativeSyracuseClockBridge
import BoundedBottomPassageClock

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open Erdos1135.Tao CollatzCanonical.NativeTao CollatzCanonical.RawOccupation CollatzClockAudit

theorem syracuse_of_odd_shortcut_hit {q y A : ℕ} (hq : Odd q) (hy : Odd y)
    (h : iterate A q = y) : (syracuse^[oddCount A q]) q = y := by
  obtain ⟨j, hj⟩ := shortcut_odd_endpoint_is_syracuse_clock A q hq (by rwa [h])
  rw [hj, syracuse_shortcut_oddCount]
  simpa only [hj, syracuse_shortcut_landing] using h

theorem syracuse_firstHitOddDepth {n q : ℕ} (hnodd : n % 2 = 1) (hq : Odd q)
    (hhit : ∃ A, iterate A q = n) :
    (syracuse^[firstHitOddDepth n q]) q = n := by
  have hfirst := firstHit_find hhit
  rw [firstHitOddDepth_of_first_hit hfirst]
  exact syracuse_of_odd_shortcut_hit hq (Nat.odd_iff.mpr hnodd) hfirst.1

theorem ValidPrefix.firstHitOddDepth_eq {n K i : ℕ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hnp : Nonperiodic n) (hi : i ≤ K) :
    firstHitOddDepth n (x i) = i := by
  obtain ⟨A, hA, hcount⟩ := (hx.restrict hi).hit_clock
  rw [firstHitOddDepth_of_first_hit (firstHit_of_nonperiodic hnp hA), hcount]

theorem ValidPrefix.source_depth_split {n K q : ℕ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hnp : Nonperiodic n)
    {A : ℕ} (hA : iterate A q = x K) :
    firstHitOddDepth n q = oddCount A q + K := by
  obtain ⟨B, hB, hcount⟩ := hx.hit_clock
  have htotal : iterate (A + B) q = n := by rw [iterate_add, hA, hB]
  rw [firstHitOddDepth_of_first_hit (firstHit_of_nonperiodic hnp htotal),
    oddCount_add, hA, hcount]

theorem ValidPrefix.le_source_depth {n K q : ℕ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hnp : Nonperiodic n)
    (hhit : ∃ A, iterate A q = x K) : K ≤ firstHitOddDepth n q := by
  obtain ⟨A, hA⟩ := hhit
  rw [hx.source_depth_split hnp hA]
  omega

theorem ValidPrefix.source_syracuse_suffix {n K q i : ℕ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hq : Odd q) (hhit : ∃ A, iterate A q = x K) (hi : i ≤ K) :
    (syracuse^[firstHitOddDepth n q - i]) q = x i := by
  obtain ⟨A, hA⟩ := hhit
  obtain ⟨B, hB, _⟩ := hx.suffix_hit_clock hi le_rfl
  have hqi : iterate (A + B) q = x i := by rw [iterate_add, hA, hB]
  have hd := (hx.restrict hi).source_depth_split hnp hqi
  have he : firstHitOddDepth n q - i = oddCount (A + B) q := by omega
  rw [he]
  exact syracuse_of_odd_shortcut_hit hq (Nat.odd_iff.mpr (hx.odd hnodd hi)) hqi

theorem firstHitOddDepth_syracuse_tail {n q t : ℕ}
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n) (hq : Odd q)
    (hhit : ∃ A, iterate A q = n) (ht : t ≤ firstHitOddDepth n q) :
    firstHitOddDepth n ((syracuse^[t]) q) = firstHitOddDepth n q - t ∧
      ∃ A, iterate A ((syracuse^[t]) q) = n := by
  let y := (syracuse^[t]) q
  have hy : Odd y := syracuse_iterate_odd t q hq
  have hland : (syracuse^[firstHitOddDepth n q - t]) y = n := by
    dsimp [y]
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel ht]
    exact syracuse_firstHitOddDepth hnodd hq hhit
  let A := taoTupleWeight (syracuseValuationPNatList (firstHitOddDepth n q - t) y hy)
  have hA : iterate A y = n := by
    rw [show iterate A y = (syracuse^[firstHitOddDepth n q - t]) y from
      syracuse_shortcut_landing _ y hy]
    exact hland
  refine ⟨?_, A, hA⟩
  rw [firstHitOddDepth_of_first_hit (firstHit_of_nonperiodic hnp hA)]
  exact syracuse_shortcut_oddCount _ y hy

theorem ValidPrefix.visit_depth_le {n K R i : ℕ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hi : i ≤ K) (hvisit : x i ≤ R) : i ≤ lastVisitDepthBound n R := by
  classical
  have hm : x i ∈ boundedHitEndpoints n R := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      hx.odd hnodd hi, hx.ancestor hi⟩
  have h := Finset.le_sup (f := firstHitOddDepth n) hm
  simpa only [hx.firstHitOddDepth_eq hnp hi] using h

theorem ValidPrefix.le_lastVisit_of_visit {n K R i : ℕ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hi : i ≤ K) (hvisit : x i ≤ R) : i ≤ lastVisitIndex n R x :=
  le_finiteLastVisit (hx.visit_depth_le hnodd hnp hi hvisit) hvisit

theorem ValidPrefix.lastVisit_mem {n K R : ℕ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hR : n ≤ R) : x (lastVisitIndex n R x) ≤ R :=
  finiteLastVisit_mem (by simpa only [hx.1] using hR)

theorem source_first_passage_eq_reverse_lastVisit {n K q : ℕ} {R : ℝ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hq : Odd q) (hhit : ∃ A, iterate A q = x K)
    (hR : 0 ≤ R) (hnR : (n : ℝ) ≤ R)
    (hK : lastVisitDepthBound n ⌊R⌋₊ ≤ K) :
    syracuseFirstHitAtMostReal R q
      (firstHitOddDepth n q - lastVisitIndex n ⌊R⌋₊ x) := by
  have hσK := (lastVisitIndex_le_bound n ⌊R⌋₊ x).trans hK
  have hσd := hσK.trans (hx.le_source_depth hnp hhit)
  have hnRnat : n ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR).mpr hnR
  have hsuffix := hx.source_syracuse_suffix hnodd hnp hq hhit hσK
  refine ⟨?_, ?_⟩
  · rw [hsuffix]
    exact (Nat.cast_le.mpr (hx.lastVisit_mem hnRnat)).trans (Nat.floor_le hR)
  · intro t ht
    by_contra hnot
    have hlow : ((syracuse^[t]) q : ℝ) ≤ R := le_of_not_gt hnot
    have htD : t ≤ firstHitOddDepth n q := by omega
    have hroot : ∃ A, iterate A q = n := by
      obtain ⟨A, hA⟩ := hhit
      obtain ⟨B, hB⟩ := hx.ancestor le_rfl
      exact ⟨A + B, by rw [iterate_add, hA, hB]⟩
    obtain ⟨hdepth, hbasin⟩ := firstHitOddDepth_syracuse_tail hnodd hnp hq hroot htD
    have hy : (syracuse^[t]) q ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR).mpr hlow
    have hm : (syracuse^[t]) q ∈ boundedHitEndpoints n ⌊R⌋₊ := by
      classical
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        Nat.odd_iff.mp (syracuse_iterate_odd t q hq), hbasin⟩
    have hb := Finset.le_sup (f := firstHitOddDepth n) hm
    rw [hdepth] at hb
    have hjK : firstHitOddDepth n q - t ≤ K := hb.trans hK
    have hstate := hx.source_syracuse_suffix hnodd hnp hq hhit hjK
    have hdt : firstHitOddDepth n q - (firstHitOddDepth n q - t) = t := by omega
    rw [hdt] at hstate
    have hvisit : x (firstHitOddDepth n q - t) ≤ ⌊R⌋₊ := by
      rwa [← hstate]
    have hle := hx.le_lastVisit_of_visit hnodd hnp hjK hvisit
    omega

theorem source_barrier_clock_add_lastVisit {n K q : ℕ} {R : ℝ} {x : ℕ → ℕ}
    (hx : ValidPrefix n K x) (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hq : Odd q) (hhit : ∃ A, iterate A q = x K)
    (hR : 0 ≤ R) (hnR : (n : ℝ) ≤ R)
    (hK : lastVisitDepthBound n ⌊R⌋₊ ≤ K) :
    actualBarrierTime R q + lastVisitIndex n ⌊R⌋₊ x = firstHitOddDepth n q := by
  rw [actualBarrierTime_eq_of_first_hit
    (source_first_passage_eq_reverse_lastVisit hx hnodd hnp hq hhit hR hnR hK)]
  exact Nat.sub_add_cancel ((lastVisitIndex_le_bound n ⌊R⌋₊ x).trans
    (hK.trans (hx.le_source_depth hnp hhit)))

#print axioms syracuse_of_odd_shortcut_hit
#print axioms ValidPrefix.source_syracuse_suffix
#print axioms firstHitOddDepth_syracuse_tail
#print axioms source_first_passage_eq_reverse_lastVisit
#print axioms source_barrier_clock_add_lastVisit

end CollatzCylinderPacking.Arithmetic.InverseDoob
