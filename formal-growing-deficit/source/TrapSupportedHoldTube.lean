import TrapGoodPathFromTube
import TrapHoldSourceSupport
import Erdos1135.Tao.Renewal.SourcePathData

/-! A literal raw-prefix tube controls every supported Hold endpoint before the horizontal cutoff. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_hold_prefix_path_coordinates
    (start : TaoSection7RenewalPoint) (pres : List (List ℕ)) (q : ℕ) (hq : q ≤ pres.length) :
    ((taoSection7RenewalPathPoint start (taoSection7HoldIncrementsOfPrefixes pres) q).j : ℕ) =
      (start.j : ℕ) + (taoSection7SourceBlocks (pres.take q)).length ∧
    (taoSection7RenewalPathPoint start (taoSection7HoldIncrementsOfPrefixes pres) q).l =
      start.l + ((taoSection7SourceBlocks (pres.take q)).sum : ℕ) := by
  induction q generalizing start pres with
  | zero => simp [taoSection7SourceBlocks]
  | succ q ih =>
      cases pres with
      | nil => simp at hq
      | cons pre pres =>
          have hqtail : q ≤ pres.length := by simpa using hq
          have h := ih (start + taoSection7HoldIncrementOfPrefix pre) pres hqtail
          simp only [taoSection7HoldIncrementsOfPrefixes, List.map_cons,
            taoSection7RenewalPathPoint_cons_succ]
          simp only [List.take_succ_cons, taoSection7SourceBlocks, List.length_append,
            List.length_cons, List.sum_append, List.sum_cons]
          constructor
          · calc
              _ = ((start + taoSection7HoldIncrementOfPrefix pre).j : ℕ) +
                  (taoSection7SourceBlocks (pres.take q)).length := h.1
              _ = _ := by
                rw [TaoSection7RenewalPoint.add_j, PNat.add_coe]
                simp [taoSection7HoldIncrementOfPrefix, taoSection7ShiftIndex]
                omega
          · simpa [TaoSection7RenewalPoint.add_l, taoSection7HoldIncrementOfPrefix,
              taoSection7HoldIncrementsOfPrefixes, Nat.cast_add, add_assoc, add_left_comm, add_comm] using h.2

theorem trap_source_first_prefix_path_coordinates
    (pre : List ℕ) (pres : List (List ℕ)) (q : ℕ) (hq : q ≤ pres.length) :
    ((taoSection7RenewalPathPoint (taoSection7HoldIncrementOfPrefix pre)
      (taoSection7HoldIncrementsOfPrefixes pres) q).j : ℕ) =
      (taoSection7SourceBlocks (pre :: pres.take q)).length ∧
    (taoSection7RenewalPathPoint (taoSection7HoldIncrementOfPrefix pre)
      (taoSection7HoldIncrementsOfPrefixes pres) q).l =
      ((taoSection7SourceBlocks (pre :: pres.take q)).sum : ℕ) := by
  have h := trap_hold_prefix_path_coordinates (taoSection7HoldIncrementOfPrefix pre) pres q hq
  constructor
  · simpa [taoSection7SourceBlocks, taoSection7HoldIncrementOfPrefix,
      taoSection7ShiftIndex, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.1
  · simpa [taoSection7SourceBlocks, taoSection7HoldIncrementOfPrefix,
      Nat.cast_add, add_assoc, add_left_comm, add_comm] using h.2

theorem trap_source_blocks_take_endpoint
    (pre : List ℕ) (pres : List (List ℕ)) (q : ℕ) :
    (taoSection7SourceBlocks (pre :: pres)).take
        (taoSection7SourceBlocks (pre :: pres.take q)).length =
      taoSection7SourceBlocks (pre :: pres.take q) := by
  have hsplit : taoSection7SourceBlocks (pre :: pres) =
      taoSection7SourceBlocks (pre :: pres.take q) ++ taoSection7SourceBlocks (pres.drop q) := by
    rw [← taoSection7SourceBlocks_append, List.cons_append, List.take_append_drop]
  rw [hsplit, List.take_left]

theorem trap_supported_hold_path_raw_coordinates
    (x : ℕ × List ℕ) (xs : List (ℕ × List ℕ))
    (hsupp : ∀ y ∈ x :: xs, y.1 = y.2.length) (q : ℕ) (hq : q ≤ xs.length) :
    let p := taoSection7RenewalPathPoint (taoSection7HoldPointOfPrefix x.1 x.2)
      (xs.map fun y => taoSection7HoldPointOfPrefix y.1 y.2) q
    let raw := taoSection7SourceBlocks ((x :: xs).map Prod.snd)
    (raw.take (p.j : ℕ)).length = (p.j : ℕ) ∧ ((raw.take (p.j : ℕ)).sum : ℤ) = p.l := by
  have hx := hsupp x (by simp)
  have hxs : ∀ y ∈ xs, y.1 = y.2.length := fun y hy => hsupp y (by simp [hy])
  dsimp only
  rw [hx, trap_holdPoint_length_eq_increment,
    trap_holdPoint_map_eq_increments_of_supported xs hxs]
  have hcoords := trap_source_first_prefix_path_coordinates x.2 (xs.map Prod.snd) q
    (by simpa using hq)
  simp only [List.map_cons]
  rw [hcoords.1, trap_source_blocks_take_endpoint]
  exact ⟨rfl, hcoords.2.symm⟩

theorem trap_supported_hold_source_tube
    (J : ℕ) (D : ℝ) (xs : List (ℕ × List ℕ))
    (hsupp : ∀ y ∈ xs, y.1 = y.2.length)
    (hprefix : ∀ j ≤ J,
      |((((taoSection7RawPrefixOfHoldBlocks J xs).take j).sum : ℕ) : ℝ) - 4 * (j : ℝ)| ≤ D)
    (start : TaoSection7RenewalPoint) (full : List TaoSection7RenewalPoint)
    (hmap : xs.map (fun y => taoSection7HoldPointOfPrefix y.1 y.2) = start :: full)
    (q : ℕ) (hq : q ≤ full.length)
    (hJ : ((taoSection7RenewalPathPoint start full q).j : ℕ) ≤ J) :
    |((taoSection7RenewalPathPoint start full q).l : ℝ) -
      4 * (((taoSection7RenewalPathPoint start full q).j : ℕ) : ℝ)| ≤ D := by
  cases xs with
  | nil => simp at hmap
  | cons x xs =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨rfl, rfl⟩ := hmap
      have hcoords := trap_supported_hold_path_raw_coordinates x xs hsupp q (by simpa using hq)
      dsimp only at hcoords
      have hpref := hprefix
        ((taoSection7RenewalPathPoint (taoSection7HoldPointOfPrefix x.1 x.2)
          (xs.map fun y => taoSection7HoldPointOfPrefix y.1 y.2) q).j : ℕ) hJ
      rw [taoSection7RawPrefixOfHoldBlocks, List.take_take, Nat.min_eq_left hJ] at hpref
      have hsum := congrArg (fun z : ℤ => (z : ℝ)) hcoords.2
      simp only [Int.cast_natCast] at hsum
      rw [hsum] at hpref
      exact hpref

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_supported_hold_path_raw_coordinates
#print axioms Erdos1135.Tao.trap_supported_hold_source_tube
