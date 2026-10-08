import NativeTaoArithmeticBridge
import DefaultPassComposition
import Erdos1135.Tao.Syracuse.FirstPassageInterval

set_option autoImplicit false

namespace CollatzCanonical.NativeTao
open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

theorem syracuse_clock_strictMono (q : ℕ) (hq : Odd q) :
    StrictMono (fun n => Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [Tao.taoTupleWeight_syracuseValuationPNatList_succ]
  exact Nat.lt_add_of_pos_right (Tao.syracuseTerminalExponentPNat n q hq).pos

theorem le_syracuse_clock (n q : ℕ) (hq : Odd q) :
    n ≤ Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hp := (Tao.syracuseTerminalExponentPNat n q hq).pos
    rw [Tao.taoTupleWeight_syracuseValuationPNatList_succ]
    omega

/-- An odd shortcut source occurs at an exact Syracuse expansion boundary. -/
theorem odd_shortcut_index_is_syracuse_clock (n q : ℕ) (hq : Odd q)
    (i : ℕ) (hi : i < Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq))
    (hodd : Odd ((Terras.accelerated^[i]) q)) :
    ∃ j < n, i = Tao.taoTupleWeight (Tao.syracuseValuationPNatList j q hq) := by
  induction n generalizing q i with
  | zero => simp [Tao.syracuseValuationPNatList, Tao.taoTupleWeight] at hi
  | succ n ih =>
    have hlength : Tao.taoTupleWeight (Tao.syracuseValuationPNatList (n + 1) q hq) =
        Tao.syracuseExponent q +
          Tao.taoTupleWeight (Tao.syracuseValuationPNatList n (Tao.syracuse q) (Tao.syracuse_odd q)) := by
      simp [Tao.syracuseValuationPNatList, Tao.taoTupleWeight]
    rw [hlength] at hi
    have hland : (Terras.accelerated^[Tao.syracuseExponent q]) q = Tao.syracuse q := by
      simpa only [Tao.syracuseParityBlock_length] using
        Tao.accelerated_iterate_syracuseParityBlock_length_eq_syracuse hq
    by_cases hblock : i < Tao.syracuseExponent q
    · have hiz := odd_index_in_syracuse_block_eq_zero hq hblock hodd
      refine ⟨0, Nat.succ_pos n, ?_⟩
      simpa [Tao.syracuseValuationPNatList, Tao.taoTupleWeight] using hiz
    · have hai : Tao.syracuseExponent q ≤ i := Nat.le_of_not_gt hblock
      have he : (Terras.accelerated^[i]) q =
          (Terras.accelerated^[i - Tao.syracuseExponent q]) (Tao.syracuse q) := by
        rw [← hland, ← Function.iterate_add_apply, Nat.sub_add_cancel hai]
      obtain ⟨j, hj, hjEq⟩ := ih (Tao.syracuse q) (Tao.syracuse_odd q)
        (i - Tao.syracuseExponent q) (by omega) (by simpa only [he] using hodd)
      refine ⟨j + 1, by omega, ?_⟩
      simp only [Tao.syracuseValuationPNatList, Tao.taoTupleWeight]
      change i = Tao.syracuseExponent q +
        Tao.taoTupleWeight (Tao.syracuseValuationPNatList j (Tao.syracuse q) (Tao.syracuse_odd q))
      omega

theorem shortcut_odd_endpoint_is_syracuse_clock (K q : ℕ) (hq : Odd q)
    (hodd : Odd (iterate K q)) :
    ∃ n, K = Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq) := by
  obtain ⟨n, _, hn⟩ := odd_shortcut_index_is_syracuse_clock (K + 1) q hq K
    ((Nat.lt_succ_self K).trans_le (le_syracuse_clock (K + 1) q hq))
    (by simpa only [iterate_eq_native] using hodd)
  exact ⟨n, hn⟩

theorem pass_preserved_of_syracuse_prefix_high {B q r : ℕ} (hB : 1 ≤ B)
    (hpre : ∀ i < r, B < (Tao.syracuse^[i]) q) :
    Tao.syracusePassLocationAtMostOrOne B q hB =
      Tao.syracusePassLocationAtMostOrOne B ((Tao.syracuse^[r]) q) hB := by
  classical
  have hh : Tao.syracuseHitsAtMost q B ↔ Tao.syracuseHitsAtMost ((Tao.syracuse^[r]) q) B := by
    constructor
    · rintro ⟨t, ht⟩
      have hrt : r ≤ t := by
        by_contra h
        exact (not_lt_of_ge ht) (hpre t (Nat.lt_of_not_ge h))
      refine ⟨t - r, ?_⟩
      simpa only [← Function.iterate_add_apply, Nat.sub_add_cancel hrt] using ht
    · rintro ⟨t, ht⟩
      exact ⟨t + r, by simpa only [Function.iterate_add_apply] using ht⟩
  by_cases hq : Tao.syracuseHitsAtMost q B
  · let t := Tao.syracuseFirstPassageTime ((Tao.syracuse^[r]) q) B (hh.mp hq)
    have ht := Tao.syracuseFirstHitAtMost_of_hitsAtMost ((Tao.syracuse^[r]) q) B (hh.mp hq)
    apply Subtype.ext
    rw [CollatzClockAudit.passAtMostOrOne_of_first_hit hB
      (Tao.syracuseFirstHitAtMost_of_tail hpre ht),
      CollatzClockAudit.passAtMostOrOne_of_first_hit hB ht]
    rw [Nat.add_comm r, Function.iterate_add_apply]
  · rw [Tao.syracusePassLocationAtMostOrOne_of_not_hitsAtMost hB hq,
      Tao.syracusePassLocationAtMostOrOne_of_not_hitsAtMost hB (mt hh.mpr hq)]

/-- Passage is unchanged after an odd shortcut landing whenever all earlier
odd source states lie above the barrier, including failed passages. -/
theorem pass_preserved_after_shortcut_odd_landing {B q u K : ℕ}
    (hB : 1 ≤ B) (hq : Odd q) (hu : Odd u) (hland : iterate K q = u)
    (hpre : ∀ i < K, Odd (iterate i q) → B < iterate i q) :
    Tao.syracusePassLocationAtMostOrOne B q hB =
      Tao.syracusePassLocationAtMostOrOne B u hB := by
  obtain ⟨n, hn⟩ := shortcut_odd_endpoint_is_syracuse_clock K q hq (by rwa [hland])
  have hnative : (Tao.syracuse^[n]) q = u := by
    rw [hn, syracuse_shortcut_landing] at hland
    exact hland
  rw [← hnative]
  apply pass_preserved_of_syracuse_prefix_high hB
  intro j hj
  have hclock := syracuse_clock_strictMono q hq hj
  dsimp only at hclock
  rw [← hn] at hclock
  have hp := hpre (Tao.taoTupleWeight (Tao.syracuseValuationPNatList j q hq)) hclock
    (by rw [syracuse_shortcut_landing]; exact Tao.syracuse_iterate_odd j q hq)
  simpa only [syracuse_shortcut_landing] using hp

#print axioms shortcut_odd_endpoint_is_syracuse_clock
#print axioms pass_preserved_after_shortcut_odd_landing

end CollatzCanonical.NativeTao
